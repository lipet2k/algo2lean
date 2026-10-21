"""Safe scalar decoding and typed Real storage preserve the Std-only runtime."""

from pathlib import Path
import shutil
import unittest

from algo2lean.checker import check_lean


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "tests/proofs"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean").is_file())


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ScalarStorageTests(unittest.TestCase):
    def test_primitive_computation_and_wrong_type_rejection_without_mathlib(self):
        source = (PROOFS / "scalar_storage_std.lean").read_text(encoding="utf-8")
        checked = check_lean(source, module="ScalarStorageStdTest", timeout=90)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_real_values_tuples_fields_and_typed_collections(self):
        source = (PROOFS / "scalar_storage.lean").read_text(encoding="utf-8")
        checked = check_lean(source, module="ScalarStorageTest", timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
