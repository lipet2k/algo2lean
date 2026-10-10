"""Reusable clock costs and allocation-aware framing are checked by Lean."""

from pathlib import Path
import shutil
import unittest

from algo2lean.checker import check_lean


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class CallCostTests(unittest.TestCase):
    def test_same_call_costs_and_fresh_allocation_frames(self):
        proof = (ROOT / "tests/proofs/call_cost.lean").read_text(encoding="utf-8")
        checked = check_lean(proof, module="CallCostTest", timeout=60)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses 'sorry'", checked.output)


if __name__ == "__main__":
    unittest.main()
