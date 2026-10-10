"""Checked module calls preserve reusable proofs and concrete execution effects."""

from pathlib import Path
import shutil
import unittest

from algo2lean.checker import check_lean


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ModuleCoreTests(unittest.TestCase):
    def test_reuse_transitive_calls_divergence_aliases_allocation_and_clocks(self):
        proof = (ROOT / "tests/proofs/modules.lean").read_text(encoding="utf-8")
        checked = check_lean(proof, module="ModulesCoreTest", timeout=60)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)


if __name__ == "__main__":
    unittest.main()
