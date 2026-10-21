"""Randomized execution never acquires a generated determinism certificate."""

import shutil
import tempfile
import textwrap
import unittest

from algo2lean.checker import lean_imports
from algo2lean.modular import compile_project
from algo2lean.module_facts import emit_facts
from algo2lean.project import ProjectError
from algo2lean.project_checker import check_project, project_lean_sources
from algo2lean.server import project_response


class RandomizedModuleTests(unittest.TestCase):
    def compile(self, sources, entry="main"):
        sources = {name: textwrap.dedent(source).lstrip("\n") for name, source in sources.items()}
        with tempfile.TemporaryDirectory(prefix="algo2lean-random-modules-") as root:
            return compile_project(entry, root=root, sources=sources)

    def assert_no_determinism(self, module):
        self.assertTrue(module.randomized)
        self.assertEqual(module.facts_lean, "")
        self.assertEqual(module.facts_module, "")
        self.assertEqual(emit_facts(module), "")
        self.assertNotIn("Run.eq_of_call", module.lean)

    def test_randomized_module_has_no_determinism_file_or_public_claim(self):
        compiled = self.compile({"main": "def sample() -> Int:\n    return randint(-2, 4)\n"})
        self.assert_no_determinism(compiled.entry)
        self.assertNotIn("Algo.main.Facts", compiled.files)
        self.assertEqual(compiled.entry.probability_module, "Algo.main.Probability")
        self.assertEqual(compiled.files["Algo.main.Probability"], compiled.entry.probability_lean)
        self.assertIn("def sample.law", compiled.entry.probability_lean)
        self.assertIn("theorem choice_step", compiled.entry.probability_lean)
        response = project_response(compiled)
        self.assertFalse(any(entry["name"].endswith(".Run.eq_of_call")
                             for function in response["functions"]
                             for entry in function["interface_entries"]))

    def test_transitive_calls_and_reexports_do_not_restore_determinism(self):
        compiled = self.compile({
            "random_source": "def sample() -> Int:\n    return randint(0, 2)\n",
            "bridge": "from random_source import sample as selected\n",
            "middle": "import bridge\ndef sample() -> Int:\n    return bridge.selected()\n",
            "main": "from middle import sample as selected\ndef run() -> Int:\n    return selected()\n",
        })
        for name in ("random_source", "middle", "main"):
            self.assert_no_determinism(compiled.modules[name])
            self.assertNotIn("Algo." + name + ".Facts", compiled.files)
        # A pure re-export has no executable wrapper; its original callee is
        # still the separately compiled randomized source module.
        self.assertFalse(compiled.modules["bridge"].randomized)
        self.assertFalse(compiled.modules["bridge"].probability_lean)
        self.assertIn("Algo.random_source.Probability", lean_imports(compiled.modules["middle"].probability_lean))
        self.assertIn("Algo.middle.Probability", lean_imports(compiled.entry.probability_lean))

    def test_unused_source_import_does_not_disable_a_valid_certificate(self):
        compiled = self.compile({
            "random_source": "def sample() -> Int:\n    return randint(0, 2)\n",
            "main": "import random_source\ndef answer() -> Int:\n    return 42\n",
        })
        self.assertFalse(compiled.entry.randomized)
        self.assertIn("theorem deterministic", compiled.entry.facts_lean)
        self.assertIn("answer.Run.eq_of_call", compiled.entry.facts_lean)
        self.assertNotIn("random_source».«Facts", compiled.entry.facts_lean)

    def test_mixed_unit_certifies_only_reachable_deterministic_functions(self):
        compiled = self.compile({"main": """
            def answer() -> Int:
                return 42
            def sample() -> Int:
                return randint(0, 2)
        """})
        self.assertTrue(compiled.entry.randomized)
        self.assertEqual(compiled.entry.deterministic_functions, {"answer"})
        self.assertIn("answer.Run.eq_of_call", compiled.entry.facts_lean)
        self.assertNotIn("sample.Run.eq_of_call", compiled.entry.facts_lean)
        self.assertNotIn("theorem deterministic :", compiled.entry.facts_lean)
        self.assertIn("answer.Call.hasLaw", compiled.entry.probability_lean)
        self.assertNotIn("sample.Call.hasLaw", compiled.entry.probability_lean)

    def test_recursive_group_facades_and_external_caller_inherit_randomness(self):
        sources = {
            "left": """
                from right import recurse
                def sample(n: Int) -> Int:
                    if n <= 0:
                        return randint(0, 2)
                    return recurse(n - 1)
            """,
            "right": """
                from left import sample
                def recurse(n: Int) -> Int:
                    return sample(n)
            """,
            "main": "from right import recurse\ndef run(n: Int) -> Int:\n    return recurse(n)\n",
        }
        compiled = self.compile(sources)
        for module in (*compiled.implementation_modules.values(), *compiled.modules.values()):
            self.assert_no_determinism(module)
        self.assertFalse(any(name.endswith(".Facts") for name in compiled.files))
        implementation = next(iter(compiled.implementation_modules.values()))
        self.assertIn("def nextChoice", implementation.probability_lean)
        for name, function in (("left", "sample"), ("right", "recurse")):
            facade = compiled.modules[name]
            self.assertIn("import " + implementation.probability_module, facade.probability_lean)
            self.assertNotIn("def nextChoice", facade.probability_lean)
            self.assertIn("abbrev nextChoice := @", facade.probability_lean)
            for member in ("law", "outcome", "returnProbability", "outputProbability",
                           "terminationProbability", "expectedCost"):
                self.assertIn("abbrev " + function + "." + member + " := @", facade.probability_lean)
        left, right = self.compile(sources, "left"), self.compile(sources, "right")
        self.assertEqual(left.files, right.files)
        for name, source in left.files.items():
            self.assertEqual(source, compiled.files[name])

    def test_recursive_group_inherits_an_external_random_dependency(self):
        compiled = self.compile({
            "random_source": "def sample() -> Int:\n    return randint(0, 2)\n",
            "left": """
                from right import recurse
                from random_source import sample
                def run(n: Int) -> Int:
                    if n <= 0:
                        return sample()
                    return recurse(n - 1)
            """,
            "right": "from left import run\ndef recurse(n: Int) -> Int:\n    return run(n)\n",
        }, "left")
        for module in (*compiled.implementation_modules.values(), *compiled.modules.values()):
            self.assert_no_determinism(module)

    def test_abstract_slot_keeps_explicit_determinism_evidence(self):
        compiled = self.compile({
            "api": """
                from algo2lean import Interface
                class Source(Interface):
                    def get(self) -> Int: ...
            """,
            "main": "from api import Source\ndef read(source: Source) -> Int:\n    return source.get()\n",
        })
        self.assertFalse(compiled.entry.randomized)
        self.assertIn("structure DependencyFacts", compiled.entry.facts_lean)
        self.assertIn("facts.«Source».step_next", compiled.entry.facts_lean)
        self.assertFalse(compiled.entry.probability_lean)

    def test_deterministic_callees_gain_only_optional_companions(self):
        sources = {
            "helper": "def increment(x: Int) -> Int:\n    return x + 1\n",
            "main": "from helper import increment\ndef run() -> Int:\n    return increment(randint(0, 2))\n",
        }
        deterministic = self.compile(sources, "helper")
        compiled = self.compile(sources)
        self.assertFalse(any(name.endswith(".Probability") for name in deterministic.files))
        for name, source in deterministic.files.items():
            self.assertEqual(source, compiled.files[name])
        helper = compiled.modules["helper"]
        self.assertFalse(helper.randomized)
        self.assertTrue(helper.facts_lean)
        self.assertTrue(helper.probability_lean)
        self.assertIn("Algo.helper.Probability", lean_imports(compiled.entry.probability_lean))

    def test_probability_names_work_with_imported_classes_and_empty_facades(self):
        compiled = self.compile({
            "helper": """
                class Box:
                    def __init__(self) -> None:
                        return
                    def get(self) -> Int:
                        return 3
            """,
            "main": """
                from helper import Box
                def run() -> Int:
                    item = Box()
                    return item.get() + randint(0, 2)
            """,
        })
        self.assertTrue(compiled.entry.probability_lean)
        reexport = self.compile({
            "main": "from recursive import sample\n",
            "recursive": "import main\ndef sample() -> Int:\n    return randint(0, 2)\n",
        })
        self.assertFalse(reexport.entry.functions)
        self.assertIn("abbrev nextChoice", reexport.entry.probability_lean)

    def test_probability_name_collision_identifies_its_source_module(self):
        with self.assertRaisesRegex(ProjectError, "Box.law.*probability declaration") as raised:
            self.compile({"main": """
                class Box:
                    def __init__(self) -> None:
                        return
                    def law(self) -> Int:
                        return randint(0, 2)
            """})
        self.assertTrue(raised.exception.file.endswith("main.algo"))

    def test_probability_companions_are_excluded_from_default_and_facts_checks(self):
        compiled = self.compile({"main": "def sample() -> Int:\n    return randint(0, 2)\n"})
        for check_facts in (False, True):
            selected = project_lean_sources(compiled, check_facts=check_facts)
            self.assertNotIn(compiled.entry.probability_module, selected)
        selected = project_lean_sources(compiled, analysis_modules=[compiled.entry.probability_module])
        self.assertIn(compiled.entry.probability_module, selected)

    def test_probability_import_can_compile_a_proof_only_deterministic_dependency(self):
        compiled = self.compile({
            "main": "def sample() -> Int:\n    return randint(0, 2)\n",
            "helper": "def answer() -> Int:\n    return 42\n",
        })
        self.assertNotIn("helper", compiled.modules)
        proof = "import Algo.helper.Probability\n"
        selected = project_lean_sources(compiled, proof_sources={"Algo.main.Analysis": proof},
                                       analysis_modules=["Algo.main.Analysis"])
        self.assertIn("Algo.helper.Generated", selected)
        self.assertIn("Algo.helper.Probability", selected)
        # An explicitly requested deterministic companion now includes the
        # certificate used to lift existing Call proofs to probability laws.
        self.assertIn("Algo.helper.Facts", selected)
        self.assertIn("theorem answer.Call.hasLaw", selected["Algo.helper.Probability"])

    def test_abstract_probability_limit_is_explicit_and_propagates_to_callers(self):
        compiled = self.compile({
            "api": """
                from algo2lean import Interface
                class Source(Interface):
                    def get(self) -> Int: ...
            """,
            "generic": """
                from api import Source
                def read(source: Source) -> Int:
                    return source.get() + randint(0, 2)
            """,
            "backend": """
                class Source:
                    def __init__(self) -> None:
                        return
                    def get(self) -> Int:
                        return 0
            """,
            "wrapper": """
                from backend import Source
                from generic import read
                def run() -> Int:
                    source = Source()
                    return read(source)
            """,
            "main": "from wrapper import run\ndef sample() -> Int:\n    return run()\n",
        })
        for name in ("generic", "wrapper", "main"):
            module = compiled.modules[name]
            self.assert_no_determinism(module)
            self.assertFalse(module.probability_lean)
            self.assertIn("probability contracts", module.probability_diagnostic)
            self.assertNotIn("Algo." + name + ".Probability", compiled.files)
        self.assertIn("imported module 'wrapper'", compiled.entry.probability_diagnostic)
        self.assertTrue(compiled.modules["backend"].probability_lean)

    def test_randomized_concrete_interface_binding_has_a_source_diagnostic(self):
        with self.assertRaisesRegex(ProjectError, "Randomized implementation 'backend.Source'.*interface 'Source'") as raised:
            self.compile({
                "api": """
                    from algo2lean import Interface
                    class Source(Interface):
                        def get(self) -> Int: ...
                """,
                "generic": "from api import Source\ndef read(source: Source) -> Int:\n    return source.get()\n",
                "backend": """
                    class Source:
                        def __init__(self) -> None:
                            return
                        def get(self) -> Int:
                            return randint(0, 2)
                """,
                "main": """
                    from backend import Source
                    from generic import read
                    def run() -> Int:
                        source = Source()
                        return read(source)
                """,
            })
        self.assertTrue(raised.exception.file.endswith("main.algo"))

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_randomized_delegation_and_recursive_groups_check_in_lean(self):
        compiled = self.compile({
            "random_source": "def sample() -> Int:\n    return randint(-1, 2)\n",
            "left": """
                from right import recurse
                from random_source import sample
                def run(n: Int) -> Int:
                    if n <= 0:
                        return sample()
                    return recurse(n - 1)
            """,
            "right": "from left import run\ndef recurse(n: Int) -> Int:\n    return run(n)\n",
            "main": "from left import run\ndef sample() -> Int:\n    return run(2)\n",
        })
        checked = check_project(compiled, check_facts=True, timeout=90)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)


if __name__ == "__main__":
    unittest.main()
