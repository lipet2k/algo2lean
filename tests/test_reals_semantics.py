"""Check exact arithmetic, definedness, and reusable effectful Real call contracts."""

from pathlib import Path
import shutil
import unittest

from algo2lean.compiler import compile_source
from algo2lean.probability_checker import check_mathlib_sources

ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/NormNum.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class RealSemanticsTests(unittest.TestCase):
    def test_exact_arithmetic_failure_short_circuit_coercions_and_effect_order(self):
        compiled = compile_source((ROOT / "tests/proofs/reals.algo").read_text(encoding="utf-8"),
                                  filename="reals.algo", module="RealsGenerated")
        contracts = (ROOT / "tests/proofs/reals.lean").read_text(encoding="utf-8")
        proof = "import RealsGenerated\nimport Mathlib.Tactic.NormNum\n" + contracts
        # Audit the source-facing contracts, including reused calls and final clocks.
        results = ("divide_call", "divide_zero", "decimal_sum_call", "short_circuit_call",
                   "short_chain_call", "range_cast_call", "unary_cast_call", "effect_order_observation")
        proof += "\n" + "\n".join("#print axioms " + name for name in results) + "\n"
        checked = check_mathlib_sources({
            "RealsGenerated": compiled.lean,
            "RealsProof": proof,
        }, timeout=120)
        self.assertTrue(checked.ok, checked.output)
        audit = [line for line in checked.output.splitlines() if "depends on axioms" in line]
        self.assertEqual(len(audit), len(results), checked.output)
        for line in audit:
            names = {name.strip() for name in line.split("[", 1)[1].rstrip("]").split(",")}
            self.assertLessEqual(names, {"propext", "Classical.choice", "Quot.sound"})


if __name__ == "__main__":
    unittest.main()
