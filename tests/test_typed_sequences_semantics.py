"""Kernel-checked object collection aliases, ordering, and public interfaces."""

from pathlib import Path
import shutil
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.compiler import compile_source
from tests.test_lean import constructor_tactic


ROOT = Path(__file__).resolve().parents[1]


class TypedSequencesSemanticsTests(unittest.TestCase):
    def test_labels_do_not_change_algorithm_and_integer_spelling_is_compatible(self):
        source = (ROOT / "tests/proofs/typed_sequences.algo").read_text()
        generated = compile_source(source)
        renamed = compile_source(source.replace("# @replace", "# @change").replace("# @after", "# @next"))
        self.assertEqual(generated.lean, renamed.lean)
        self.assertNotEqual(generated.points_lean, renamed.points_lean)
        integer = "def f(a: Seq) -> Seq:\n    return copy(a)\n"
        self.assertEqual(compile_source(integer).lean,
                         compile_source(integer.replace("Seq", "Seq[Int]")).lean)
        self.assertNotIn("SequenceType", compile_source(integer).program_lean)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_typed_sequences_semantics_and_local_interface(self):
        source = (ROOT / "tests/proofs/typed_sequences.algo").read_text()
        generated = compile_source(source, filename="typed_sequences.algo")
        proof = (ROOT / "tests/proofs/typed_sequences.lean").read_text()
        checked = check_analysis(
            generated.lean,
            "import " + generated.points_module + "\nopen Algo2LeanGenerated\n"
            + constructor_tactic(generated.lean) + proof,
            generated.module, points_lean=generated.points_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)
