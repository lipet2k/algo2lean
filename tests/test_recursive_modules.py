"""Cross-file recursive groups preserve source identity and modular proof reuse."""

from pathlib import Path
import shutil
import tempfile
import textwrap
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project, project_lean_sources


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples/mutual_recursion"
PARITY = {
    "even": """
        from odd import is_odd
        def is_even(n: Int) -> Bool:
            tick("work", 2)
            # @test
            if n <= 0:
                return True
            return is_odd(n - 1)
    """,
    "odd": """
        import even as partner
        def is_odd(n: Int) -> Bool:
            tick("work", 2)
            if n <= 0:
                return False
            return partner.is_even(n - 1)
    """,
    "client": """
        from even import is_even as parity
        def classify(n: Int) -> Bool:
            return parity(n)
    """,
}


def sources_clean(sources):
    return {name: textwrap.dedent(source).lstrip("\n")
            for name, source in sources.items()}


class RecursiveModulesTests(unittest.TestCase):
    def compile(self, entry, sources):
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-") as root:
            return compile_project(entry, root=root, sources=sources_clean(sources))

    def test_entry_and_external_callers_preserve_the_same_recursive_group(self):
        even = self.compile("even", PARITY)
        odd = self.compile("odd", PARITY)
        client = self.compile("client", PARITY)
        self.assertEqual(even.files, odd.files)
        for name, source in even.files.items():
            self.assertEqual(client.files[name], source)
        self.assertEqual(set(even.entry.functions), {"is_even"})
        self.assertEqual(set(odd.entry.functions), {"is_odd"})
        self.assertEqual(set(client.entry.functions), {"classify"})
        self.assertEqual(client.entry.clocks, ("work",))
        self.assertIn("import Algo.even.Generated", client.entry.lean)
        self.assertNotIn("structure State_is_odd", client.entry.lean)
        self.assertIn("Algo.even.Generated", even.files)
        self.assertIn("Algo.odd.Generated", even.files)
        self.assertIn("is_even.ReturnsWithCost", even.entry.lean)

    def test_label_changes_leave_all_general_definitions_unchanged(self):
        original = self.compile("client", PARITY)
        source = PARITY["even"]
        unlabelled = source.replace("            # @test\n", "")
        changes = {
            "rename": source.replace("# @test", "# @renamed"),
            "remove": unlabelled,
            "add": source.replace('            tick("work", 2)',
                                  '            # @charge\n            tick("work", 2)'),
            "move": unlabelled.replace('            tick("work", 2)',
                                       '            # @test\n            tick("work", 2)'),
        }
        for edit, source in changes.items():
            with self.subTest(edit=edit):
                changed = self.compile("client", dict(PARITY, even=source))
                self.assertEqual(set(original.files), set(changed.files))
                changed_files = {name for name in original.files
                                 if original.files[name] != changed.files[name]}
                self.assertTrue(changed_files)
                self.assertTrue(all(name.endswith(".Points") for name in changed_files), changed_files)

    def test_client_reuses_one_wrapper_for_both_members_of_a_recursive_group(self):
        compiled = self.compile("client", dict(PARITY, client="""
            from even import is_even
            from odd import is_odd
            def both(n: Int) -> Bool:
                return is_even(n) or is_odd(n)
        """))
        self.assertEqual(len(compiled.entry.imports), 2)
        self.assertEqual(len({call.frame for call in compiled.entry.imports.values()}), 1)
        self.assertEqual(compiled.entry.lean.count("theorem import_0_simulates"), 1)

    def test_aliases_and_same_named_functions_keep_distinct_identities(self):
        compiled = self.compile("left", {
            "left": """
                from right import count as other
                def count(n: Int) -> Int:
                    if n <= 0:
                        return 10
                    return other(n - 1)
            """,
            "right": """
                import left as other
                def count(n: Int) -> Int:
                    if n <= 0:
                        return 20
                    return other.count(n - 1)
            """,
        })
        self.assertEqual(set(compiled.modules["left"].functions), {"count"})
        self.assertEqual(set(compiled.modules["right"].functions), {"count"})
        self.assertIn("Algo.left.Generated", compiled.files)
        self.assertIn("Algo.right.Generated", compiled.files)
        # The source dependency cycle must become an acyclic Lean import graph.
        self.assertEqual(set(project_lean_sources(compiled, check_facts=True)), set(compiled.files))

    def test_external_dependency_remains_separately_compiled(self):
        library = 'def base() -> Int:\n    tick("base", 3)\n    return 7\n'
        compiled = self.compile("a", {
            "library": library,
            "a": """
                from b import recurse
                from library import base
                def recurse_a(n: Int) -> Int:
                    if n <= 0:
                        return base()
                    return recurse(n - 1)
            """,
            "b": """
                from a import recurse_a
                def recurse(n: Int) -> Int:
                    return recurse_a(n)
            """,
        })
        independent = self.compile("library", {"library": library})
        for name, source in independent.files.items():
            self.assertEqual(compiled.files[name], source)
        self.assertEqual(compiled.entry.clocks, ("base",))
        project_lean_sources(compiled, check_facts=True)

    def test_mutual_recursion_does_not_require_a_termination_argument(self):
        compiled = self.compile("a", {
            "a": "from b import g\ndef f(n: Int) -> Int:\n    return g(n)\n",
            "b": "from a import f\ndef g(n: Int) -> Int:\n    return f(n)\n",
        })
        self.assertIn("ValidTranscript", compiled.modules["a"].lean)
        self.assertIn("ValidTranscript", compiled.modules["b"].lean)
        project_lean_sources(compiled, check_facts=True)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class RecursiveModulesCheckingTests(unittest.TestCase):
    def test_caller_of_both_group_members_checks_with_one_wrapper(self):
        sources = dict(PARITY, client="""
            import even
            import odd
            def both(n: Int) -> Bool:
                return even.is_even(n) or odd.is_odd(n)
        """)
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-shared-wrapper-") as root:
            compiled = compile_project("client", root=root, sources=sources_clean(sources))
            self.assertEqual(len({call.frame for call in compiled.entry.imports.values()}), 1)
            checked = check_project(compiled, check_facts=True)
            self.assertTrue(checked.ok, checked.output)

    def test_self_import_uses_one_recursive_group(self):
        sources = {"selfcall": """
            import selfcall as own
            def count(n: Int) -> Int:
                if n <= 0:
                    return 0
                return 1 + own.count(n - 1)
        """}
        with tempfile.TemporaryDirectory(prefix="algo2lean-self-import-") as root:
            compiled = compile_project("selfcall", root=root, sources=sources_clean(sources))
            checked = check_project(compiled, check_facts=True)
            self.assertTrue(checked.ok, checked.output)

    def test_recursive_groups_call_other_groups_and_independent_libraries(self):
        sources = {
            "library": 'def base() -> Int:\n    tick("base", 3)\n    return 7\n',
            "a": """
                from b import count as partner
                from c import count as finish
                def count(n: Int) -> Int:
                    if n <= 0:
                        return finish(0)
                    return partner(n - 1)
            """,
            "b": """
                from a import count as partner
                def count(n: Int) -> Int:
                    return partner(n)
            """,
            "c": """
                from d import count as partner
                from library import base
                def count(n: Int) -> Int:
                    if n <= 0:
                        return base()
                    return partner(n - 1)
            """,
            "d": """
                from c import count as partner
                def count(n: Int) -> Int:
                    return partner(n)
            """,
        }
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-layers-") as root:
            compiled = compile_project("a", root=root, sources=sources_clean(sources))
            checked = check_project(compiled, check_facts=True)
            self.assertTrue(checked.ok, checked.output)

    def test_weighted_parity_group_and_external_client_check(self):
        compiled = compile_project("client", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.client.Analysis", check_facts=True)
        self.assertTrue(checked.ok, checked.output)

    def test_companion_analysis_can_request_a_different_group_entry(self):
        compiled = compile_project("odd", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.client.Analysis")
        self.assertTrue(checked.ok, checked.output)

    def test_diverging_cross_file_calls_have_valid_finite_prefixes(self):
        sources = {
            "a": "from b import g\ndef f(n: Int) -> Int:\n    return g(n)\n",
            "b": "from a import f\ndef g(n: Int) -> Int:\n    return f(n)\n",
        }
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-prefix-") as root:
            compiled = compile_project("a", root=root, sources=sources)
            internal = compiled.entry.implementation.namespace + ".Algo2LeanGenerated"
            first = compiled.modules["a"].implementation_names["f"]
            second = compiled.modules["b"].implementation_names["g"]
            proof = """import Algo.a.Generated
open Algo2LeanCore _root_.Algo2LeanGenerated Algo.a

example (input : Int) :
    ∃ trace, f.ValidTranscript input trace ∧ trace.length = 5 := by
  open INTERNAL in
    have first := Step.FIRST_pc3 {} { v0 := input } []
    have second := Step.FIRST_pc2 {} { v0 := input, t2 := input } []
    have executionPrefix := Valid.cons first (Valid.cons second
      (Valid.cons (Step.SECOND_pc3 _ _ _)
        (Valid.cons (Step.SECOND_pc2 _ _ _) (Valid.single _))))
    exact ⟨_, ⟨trivial, _, executionPrefix⟩, rfl⟩
""".replace("INTERNAL", internal).replace("FIRST", first).replace("SECOND", second)
            checked = check_project(compiled, analysis=proof)
            self.assertTrue(checked.ok, checked.output)

    def test_mutable_class_method_can_reenter_an_importing_module(self):
        sources = {
            "counter": """
                from recurse import continue_count
                class Counter:
                    value: Int
                    def __init__(self, value: Int) -> None:
                        self.value = value
                    def count(self, values: Seq, n: Int) -> Int:
                        if n <= 0:
                            return self.value
                        self.value = self.value + 1
                        values[-1] = self.value
                        return continue_count(self, values, n - 1)
            """,
            "recurse": """
                from counter import Counter as SharedCounter
                def continue_count(counter: SharedCounter, values: Seq, n: Int) -> Int:
                    return counter.count(values, n)
            """,
            "client": """
                from counter import Counter
                def run(n: Int) -> Int:
                    counter = Counter(0)
                    values = const(0)
                    return counter.count(values, n)
            """,
        }
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-object-") as root:
            compiled = compile_project("client", root=root, sources=sources_clean(sources))
            checked = check_project(compiled, check_facts=True)
            self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
