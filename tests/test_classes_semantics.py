"""Lean proofs exercise the emitted mutable-class transition semantics."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.checker import prepare_lean_environment
from algo2lean.compiler import compile_source
from tests.test_lean import constructor_tactic


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "tests" / "proofs"


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ClassesSemanticsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean_environment = prepare_lean_environment(timeout=120)

    def check_fixture(self, stem, use_constructors=True):
        generated = compile_source((PROOFS / (stem + ".algo")).read_text(), filename=stem + ".algo")
        proof = (PROOFS / (stem + ".lean")).read_text()
        with tempfile.TemporaryDirectory(prefix="algo2lean-classes-") as directory:
            path = Path(directory) / (stem + ".lean")
            helpers = constructor_tactic(generated.lean) if use_constructors else ""
            path.write_text(generated.lean + helpers + proof)
            checked = subprocess.run(
                ["lean", str(path)], cwd=ROOT, env=self.lean_environment,
                capture_output=True, text=True, timeout=120,
            )
        output = checked.stdout + checked.stderr
        self.assertEqual(checked.returncode, 0, output)
        self.assertNotIn("declaration uses `sorry`", output)

    def test_python_evaluation_order_and_heap_preservation(self):
        self.check_fixture("classes_order")

    def test_aliases_cycles_null_and_object_output_interface(self):
        self.check_fixture("classes_refs")

    def test_missing_fields_and_null_receivers_have_no_fabricated_behavior(self):
        self.check_fixture("classes_stuck", use_constructors=False)


if __name__ == "__main__":
    unittest.main()
