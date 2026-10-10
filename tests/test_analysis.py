"""Analysis proofs are separate Lean modules, never appended generated text."""

from pathlib import Path
import shutil
import unittest

from algo2lean.analysis import check_analysis, generated_module_name
from algo2lean.compiler import compile_source


ROOT = Path(__file__).resolve().parents[1]


class AnalysisNamesTests(unittest.TestCase):
    def test_module_names_are_predictable_and_safe(self):
        cases = {"merge_sort.algo": "MergeSortGenerated", "factorial.algo": "FactorialGenerated",
                 "../foo.bar.algo": "FooBarGenerated", "123.algo": "Algorithm123Generated",
                 "名.algo": "AlgorithmGenerated", "C:\\folder\\sum_loop.algo": "SumLoopGenerated"}
        for filename, expected in cases.items():
            self.assertEqual(generated_module_name(filename), expected)

    def test_every_example_has_a_matching_analysis(self):
        sources = {path.stem for path in (ROOT / "examples").glob("*.algo")}
        analyses = {path.stem for path in (ROOT / "examples/analysis").glob("*.lean")}
        self.assertTrue(sources, "Keep algorithm examples in the repository")
        self.assertEqual(sources, analyses,
                         "Every example needs an analysis, and each analysis needs its source")

    def test_checker_rejects_unsafe_or_reserved_module_names(self):
        for module in ("../Generated", "Foo.Bar", "Bad-Name", "Algo2Lean", "Init"):
            with self.subTest(module=module), self.assertRaises(ValueError):
                check_analysis("", "", module)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class AnalysisCheckingTests(unittest.TestCase):
    def test_separate_import_and_analysis_diagnostics(self):
        generated = compile_source("def identity(x: Int) -> Int:\n    return x\n").lean
        prefix = "import IdentityGenerated\n"
        valid = check_analysis(generated, prefix + "example : Int → Int → Prop := identity.Returns\n", "IdentityGenerated")
        self.assertTrue(valid.ok, valid.output)
        rejected = check_analysis(generated, prefix + "example : (1 : Nat) = 2 := by decide\n", "IdentityGenerated")
        self.assertFalse(rejected.ok)
        self.assertIn("Analysis.lean:2:", rejected.output)
        unfinished = check_analysis(generated, prefix + "example : False := by sorry\n", "IdentityGenerated")
        self.assertFalse(unfinished.ok)
        self.assertIn("incomplete", unfinished.output)

    def test_success_is_scoped_to_lean_options_and_assumptions(self):
        generated = compile_source("def identity(x: Int) -> Int:\n    return x\n").lean
        prefix = "import IdentityGenerated\n"
        suppressed = check_analysis(generated, prefix +
            "set_option warn.sorry false\nexample : False := by sorry\n", "IdentityGenerated")
        self.assertTrue(suppressed.ok, suppressed.output)
        self.assertIn("declared assumptions and options", suppressed.output)
        assumptions = check_analysis(generated, prefix +
            "noncomputable def chosen : Nat := Classical.choice ⟨0⟩\n"
            "example (P Q : Prop) (h : P ↔ Q) : P = Q := propext h\n"
            "axiom explicitAssumption : False\n"
            "example : False := explicitAssumption\n", "IdentityGenerated")
        self.assertTrue(assumptions.ok, assumptions.output)
        self.assertIn("declared assumptions and options", assumptions.output)

    def test_named_points_import_core_and_keep_theorem_statement_independent(self):
        source = "def identity(x: Int) -> Int:\n    # @result\n    return x\n"
        generated = compile_source(source, module="Identity")
        core = check_analysis(generated.lean,
            "import Identity\nexample : Int → Int → Prop := identity.Returns\n", generated.module)
        self.assertTrue(core.ok, core.output)
        points = check_analysis(generated.lean,
            "import IdentityPoints\nopen Algo2LeanGenerated\nexample : Configuration → Prop := identity.At.result\n"
            "example : Int → Int → Prop := identity.Returns\n", generated.module,
            points_lean=generated.points_lean)
        self.assertTrue(points.ok, points.output)
        unavailable = check_analysis(generated.lean,
            "import Identity\n#check identity.At.result\n", generated.module,
            points_lean=generated.points_lean)
        self.assertFalse(unavailable.ok)
        self.assertIn("identity.At.result", unavailable.output)

    def test_analysis_named_core_has_no_temporary_file_collision(self):
        for module in ("Analysis", "analysis"):
            with self.subTest(module=module):
                generated = compile_source("def identity(x: Int) -> Int:\n    # @result\n    return x\n", module=module)
                prefix = "import %sPoints\n" % module
                checked = check_analysis(generated.lean,
                    prefix + "example : Int → Int → Prop := identity.Returns\n",
                    generated.module, points_lean=generated.points_lean)
                self.assertTrue(checked.ok, checked.output)
                rejected = check_analysis(generated.lean,
                    prefix + "example : False := by decide\n",
                    generated.module, points_lean=generated.points_lean)
                self.assertFalse(rejected.ok)
                self.assertIn("Analysis.lean:2:", rejected.output)

    def test_conditional_fixture_analysis(self):
        source = ROOT / "tests/fixtures/my_func.algo"
        proof = ROOT / "tests/fixtures/my_func.lean"
        generated = compile_source(source.read_text(), filename=source.name)
        checked = check_analysis(generated.lean, proof.read_text(), generated.module,
                                 points_lean=generated.points_lean)
        self.assertTrue(checked.ok, checked.output)

    def test_example_analyses(self):
        analyses = sorted((ROOT / "examples/analysis").glob("*.lean"))
        self.assertTrue(analyses, "Keep checked analysis examples in the repository")
        for path in analyses:
            with self.subTest(example=path.stem):
                source = ROOT / "examples" / (path.stem + ".algo")
                generated = compile_source(source.read_text(), filename=source.name)
                checked = check_analysis(generated.lean, path.read_text(), generated.module,
                                         points_lean=generated.points_lean)
                self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
