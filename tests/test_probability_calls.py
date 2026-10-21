"""Completed probability contracts are reused across actual source imports."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/probability_calls"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ProbabilityCallTests(unittest.TestCase):
    def test_imported_probability_contract(self):
        compiled = compile_project("client", root=FIXTURE)
        checked = check_project(compiled, analysis_module="Algo.client.Analysis", timeout=120)
        self.assertTrue(checked.ok, checked.output)

    def test_reused_caller_exports_a_contract_for_a_third_module(self):
        compiled = compile_project("driver", root=FIXTURE)
        checked = check_project(compiled, analysis_module="Algo.driver.Analysis", timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
