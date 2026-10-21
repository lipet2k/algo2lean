"""Check unbounded probabilistic completed calls against execution semantics."""

from pathlib import Path
import shutil
import unittest

from algo2lean.probability_checker import check_probability_sources


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ProbabilityCallCoreTests(unittest.TestCase):
    def test_unbounded_completed_call_law(self):
        proof = (ROOT / "tests/proofs/probability_call_core.lean").read_text(encoding="utf-8")
        checked = check_probability_sources({"CallCoreAnalysis": proof}, timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
