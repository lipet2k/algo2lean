"""The editor's randomized example includes a checked eventual-output theorem."""

from pathlib import Path
import shutil
import unittest

from algo2lean.editor_examples import load_example_project
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples/randomized"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


class RandomExamplesTests(unittest.TestCase):
    def test_catalog_contains_matched_source_and_analysis(self):
        project = load_example_project("randomized")
        self.assertEqual(project["entry"], "sampling.algo")
        self.assertEqual(set(project["sources"]), {"sampling.algo", "client.algo", "retry.algo"})
        analysis = project["analyses"]["Algo.sampling.Analysis"]
        self.assertIn("-- Main result: Correctness", analysis)
        self.assertIn("theorem die_output_probability", analysis)
        self.assertIn("theorem die_return_probability", analysis)
        self.assertNotIn("sorry", analysis)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_die_eventual_output_probability_and_termination_are_checked(self):
        compiled = compile_project(EXAMPLES / "sampling.algo", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.sampling.Analysis", timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
