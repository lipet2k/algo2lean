"""Interface declarations and generic calls retain their meaning across import cycles."""

import shutil
import tempfile
import unittest

from algo2lean.modular import compile_project
from algo2lean.project import ProjectError
from algo2lean.project_checker import check_project, project_lean_sources


COUNTER = """from algo2lean import Interface
class Counter(Interface):
    def get(self) -> Int: ...
    def put(self, value: Int) -> None: ...
"""
STORAGE = """class Storage:
    value: Int
    def __init__(self) -> None:
        self.value = 0
    def get(self) -> Int:
        tick("reads")
        return self.value
    def put(self, value: Int) -> None:
        tick("writes")
        self.value = value
"""
INCREMENT = """from api import Counter
def increment(counter: Counter) -> Int:
    value = counter.get()
    counter.put(value + 1)
    return value + 1
"""
GENERIC_CYCLE = {
    "api": "import algorithm\n" + COUNTER,
    "algorithm": INCREMENT,
    "backend": STORAGE,
    "client": """from backend import Storage
from algorithm import increment
def run() -> Int:
    counter = Storage()
    return increment(counter)
""",
}
TWO_INTERFACES = {
    "api1": "from algo2lean import Interface\nclass First(Interface):\n    def get(self) -> Int: ...\n",
    "api2": "from algo2lean import Interface\nclass Second(Interface):\n    def get(self) -> Int: ...\n",
    "a": "from api1 import First\nimport b\ndef first(x: First) -> Int:\n    return x.get()\n",
    "b": "from api2 import Second\nimport a\ndef second(x: Second) -> Int:\n    return x.get()\n",
}


class RecursiveInterfaceTests(unittest.TestCase):
    def compile(self, entry, sources):
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-interface-") as root:
            return compile_project(entry, root=root, sources=sources)

    def test_import_only_cycle_has_an_empty_shared_execution(self):
        compiled = self.compile("a", {"a": "import b\n", "b": "import a\n"})
        self.assertEqual(set(compiled.modules), {"a", "b"})
        self.assertEqual(compiled.entry.functions, {})
        self.assertEqual(len(compiled.implementation_modules), 1)
        self.assertEqual(set(project_lean_sources(compiled, check_facts=True)), set(compiled.files))

    def test_interface_only_cycle_keeps_its_declaration_in_the_source_namespace(self):
        compiled = self.compile("api", {"api": "import exports\n" + COUNTER,
                                         "exports": "from api import Counter\n"})
        self.assertEqual(compiled.modules["api"].functions, {})
        self.assertEqual(compiled.modules["exports"].functions, {})
        implementation = compiled.entry.implementation
        self.assertIn("namespace Algo.«api»", implementation.lean)
        self.assertIn("namespace «Counter»", implementation.lean)
        self.assertEqual(set(project_lean_sources(compiled, check_facts=True)), set(compiled.files))

    def test_external_client_instantiates_an_interface_declared_inside_a_cycle(self):
        compiled = self.compile("client", GENERIC_CYCLE)
        self.assertIn(("algorithm", "api"), compiled.project.compilation_groups)
        self.assertEqual(compiled.project.compilation_groups[-1], ("client",))
        generic = compiled.modules["algorithm"]
        self.assertEqual(len(generic.dependencies), 1)
        self.assertEqual(compiled.entry.dependencies, {})
        self.assertIn("increment.Call", generic.lean)
        self.assertIn("Algo.algorithm.Generated", compiled.entry.lean)
        self.assertEqual(set(project_lean_sources(compiled, check_facts=True)), set(compiled.files))

    def test_multiple_interface_dependencies_are_identical_from_every_group_entry(self):
        first = self.compile("a", TWO_INTERFACES)
        second = self.compile("b", TWO_INTERFACES)
        self.assertEqual(first.files, second.files)
        self.assertEqual(list(first.modules["a"].dependencies), list(second.modules["a"].dependencies))

    def test_unrelated_caller_interface_does_not_change_recursive_group_output(self):
        sources = dict(TWO_INTERFACES,
            aaa="from algo2lean import Interface\nclass Unrelated(Interface):\n    def get(self) -> Int: ...\n",
            client="import aaa\nfrom b import second\nfrom api1 import First\nfrom api2 import Second\ndef call(x: Second, other: First) -> Int:\n    return second(x)\n")
        independent = self.compile("a", sources)
        caller = self.compile("client", sources)
        for name, contents in independent.files.items():
            with self.subTest(module=name):
                self.assertEqual(contents, caller.files[name])

    def test_concrete_backend_in_recursive_group_has_an_explicit_binding_diagnostic(self):
        sources = {
            "api": COUNTER,
            "algorithm": INCREMENT,
            "a": "import b\nfrom algorithm import increment\n" + STORAGE + """
def run() -> Int:
    counter = Storage()
    return increment(counter)
""",
            "b": "from a import Storage\ndef read(counter: Storage) -> Int:\n    return counter.get()\n",
        }
        with self.assertRaisesRegex(ProjectError, "outside the recursive compilation group"):
            self.compile("a", sources)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class RecursiveInterfaceCheckingTests(unittest.TestCase):
    def test_multiple_interface_dependencies_check_from_either_entry(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-two-interfaces-") as root:
            first = compile_project("a", root=root, sources=TWO_INTERFACES)
            second = compile_project("b", root=root, sources=TWO_INTERFACES)
            self.assertEqual(first.files, second.files)
            checked = check_project(first, check_facts=True)
            self.assertTrue(checked.ok, checked.output)

    def test_empty_and_interface_only_group_definitions_check(self):
        for sources in ({"api": "import exports\n", "exports": "import api\n"},
                        {"api": "import exports\n" + COUNTER,
                         "exports": "from api import Counter\n"}):
            with self.subTest(interface="class Counter" in sources["api"]), \
                    tempfile.TemporaryDirectory(prefix="algo2lean-recursive-declarations-") as root:
                compiled = compile_project("api", root=root, sources=sources)
                checked = check_project(compiled, check_facts=True)
                self.assertTrue(checked.ok, checked.output)

    def test_external_interface_binding_checks_the_shared_execution_and_facades(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-interface-check-") as root:
            compiled = compile_project("client", root=root, sources=GENERIC_CYCLE)
            proof = """import Algo.client.Facts
import Algo.algorithm.Points
#check Algo.api.Counter.Code
#check Algo.algorithm.increment.Call
#check Algo.client.run.ReturnsWithCost
"""
            checked = check_project(compiled, analysis=proof, check_facts=True)
            self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
