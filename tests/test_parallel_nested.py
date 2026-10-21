"""Nested integer-row fork access, alias safety, and portable generation."""

from pathlib import Path
import shutil
import unittest

from algo2lean import CompileError, compile_source
from algo2lean.analysis import check_analysis
from algo2lean.checker import check_lean

ROOT = Path(__file__).resolve().parents[1]
SOURCE = """def fetch(a: Seq[Seq], row: Int, column: Int) -> Int:
    return a[row][column]

def put(a: Seq[Seq], row: Int, column: Int, value: Int) -> Int:
    a[row][column] = value
    return value

def replace(a: Seq[Seq], row: Int, value: Seq) -> Int:
    a[row] = value
    return 0

def copy_rows(a: Seq[Seq]) -> Seq[Seq]:
    return copy(a)

def pair_read(a: Seq[Seq], i: Int, j: Int) -> Tuple[Int, Int]:
    return fork_join(fetch(a, i, 0), fetch(a, j, 0))

def pair_write(a: Seq[Seq], i: Int, j: Int) -> Tuple[Int, Int]:
    return fork_join(put(a, i, 0, 7), put(a, j, 0, 8))

def fresh() -> Seq[Seq]:
    rows: Seq[Seq] = const(const(0))
    rows[1] = const(1)
    copied = copy_rows(rows)
    values = pair_write(copied, 0, 1)
    return copied
"""


class NestedParallelCompilerTests(unittest.TestCase):
    def test_reads_record_outer_row_slot_and_actual_inner_cell(self):
        compiled = compile_source(SOURCE)
        self.assertIn("Access.read (.collection s.v0 s.v1)", compiled.lean)
        self.assertIn("Access.readSeq ((seq_Seq_Int.get h s.v0 s.v1).getD 0) s.v2", compiled.lean)
        self.assertIn("Access.writeSeq ((seq_Seq_Int.get h s.v0 s.v1).getD 0) s.v2", compiled.lean)
        self.assertIn("Access.write (.collection s.v0 s.v1)", compiled.lean)
        self.assertIn("seq_Seq_Int.set h s.v0 s.v1 s.v2", compiled.lean)
        self.assertIn("x = .collection s.t2 i", compiled.lean)
        self.assertIn("parallelSimulation", compiled.lean)

    def test_nested_tuple_and_index_reads_are_recorded(self):
        source = """def read(pair: Tuple[Seq[Seq], Int], positions: Seq) -> Int:
    return pair[0][positions[pair[1]]][positions[0]]

def run(a: Seq[Seq], positions: Seq) -> Tuple[Int, Int]:
    return fork_join(read((a, 0), positions), read((a, 1), positions))
"""
        compiled = compile_source(source)
        for text in ("Access.read (.collection (s.v0).1 (h.read s.v1 (s.v0).2))",
                     "Access.readSeq s.v1 (s.v0).2", "Access.readSeq s.v1 (0 : Int)"):
            self.assertIn(text, compiled.lean)

    def test_other_typed_storage_stays_rejected(self):
        for typ in ("Seq[Bool]", "Seq[Seq[Seq]]", "Seq[Tuple[Int, Int]]", "Set[Int]", "Dict[Int, Int]", "Real"):
            source = (f"def identity(a: {typ}) -> {typ}:\n    return a\n"
                      f"def run(a: {typ}) -> Tuple[{typ}, {typ}]:\n"
                      "    return fork_join(identity(a), identity(a))\n")
            with self.subTest(typ=typ), self.assertRaises(CompileError) as error:
                compile_source(source)
            self.assertRegex(str(error.exception), "fork_join.*supports")

    def test_nested_labels_leave_general_definitions_unchanged(self):
        first = compile_source(SOURCE.replace("    return a[row][column]", "    # @cell\n    return a[row][column]"))
        second = compile_source(SOURCE.replace("    return a[row][column]", "    # @entry\n    return a[row][column]"))
        self.assertEqual(first.lean, second.lean)
        self.assertNotEqual(first.points_lean, second.points_lean)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class NestedParallelLeanTests(unittest.TestCase):
    def test_nested_generation_and_alias_contracts(self):
        generated = compile_source(SOURCE, module="ParallelNestedGenerated")
        proof = (ROOT / "tests/proofs/parallel_nested.lean").read_text()
        result = check_analysis(generated.lean, proof, generated.module, timeout=120)
        self.assertTrue(result.ok, result.output)
        self.assertNotIn("sorryAx", result.output)

    def test_nested_standalone_generation(self):
        generated = compile_source(SOURCE, standalone=True)
        result = check_lean(generated.lean, timeout=120)
        self.assertTrue(result.ok, result.output)


if __name__ == "__main__":
    unittest.main()
