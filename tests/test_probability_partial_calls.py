"""Imported partial contracts retain divergence mass and all-path tick costs."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/probability_partial_calls"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class PartialProbabilityCallTests(unittest.TestCase):
    def test_imported_partial_reward_preserves_divergence_and_charged_work(self):
        compiled = compile_project("client", root=FIXTURE)
        checked = check_project(compiled, analysis_module="Algo.client.Analysis", timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
