"""Check actual independent draw probabilities in generated tuple expressions."""

from pathlib import Path
import shutil
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.compiler import compile_source


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class TupleProbabilityTests(unittest.TestCase):
    def test_tuple_draws_are_independent_and_preserve_the_heap(self):
        compiled = compile_source(
            "def tosses() -> Tuple[Int, Int]:\n"
            "    return randint(0, 2), randint(0, 2)\n",
            module="Tosses")
        proof = (ROOT / "tests/proofs/tuple_probability.lean").read_text(encoding="utf-8")
        checked = check_analysis(compiled.lean, proof, compiled.module,
            probability_lean=compiled.probability_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
