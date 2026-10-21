"""Kernel-check finite heap validation, ordered updates, and shallow reference laws."""
from pathlib import Path
import shutil
import unittest

from algo2lean.checker import check_lean

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class FiniteCollectionsRuntimeTests(unittest.TestCase):
    def test_checked_payloads_order_aliases_and_local_footprints(self):
        proof = (ROOT / "tests/proofs/finite_collections_runtime.lean").read_text(encoding="utf-8")
        checked = check_lean(proof, module="FiniteCollectionsRuntimeTest", timeout=90)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
