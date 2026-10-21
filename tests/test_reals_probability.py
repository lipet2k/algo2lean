"""Exact integer sampling induces the claimed probabilities on Real outputs."""

from pathlib import Path
import shutil
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.compiler import compile_source


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class RealProbabilityTests(unittest.TestCase):
    def test_exact_half_outputs_preserve_heap_and_terminate_almost_surely(self):
        compiled = compile_source(
            "def draw() -> Real:\n    return randint(0, 2) / 2\n", module="RealDraw")
        proof = (ROOT / "tests/proofs/reals_probability.lean").read_text(encoding="utf-8")
        checked = check_analysis(compiled.lean, proof, compiled.module,
            probability_lean=compiled.probability_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
