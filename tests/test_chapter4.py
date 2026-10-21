"""Behavioral regressions for the fixed CLRS Chapter 4 matrix examples.

This Python adapter runs trusted repository files only. It checks examples
against an independent mathematical oracle; it is not the Lean semantics or
formal proof. The existing test_analysis suite checks canonical editor analyses.
The modular regression here independently checks import dependencies and the
general recurrence applications that are maintained outside the editor bundle.
"""

import __future__
from pathlib import Path
import random
import shutil
import unittest

from algo2lean.compiler import compile_source
from scripts.build_chapter4_analysis import build_analysis, DESTINATION
from scripts.check_chapter4_proofs import audit_assumptions, check_proofs
from tests.test_examples import IndexedSequence


ROOT = Path(__file__).resolve().parents[1]
ALGORITHMS = ("matrix_multiply", "matrix_recursive", "matrix_strassen")
ENTRY_POINTS = {"matrix_multiply": "matrix_multiply",
                "matrix_recursive": "matrix_recursive",
                "matrix_strassen": "strassen"}


def load_matrix_example(name):
    """Load one whitelisted example, with fresh named operation counters."""
    if name not in ALGORITHMS:
        raise ValueError("Only the fixed Chapter 4 matrix examples can be executed")
    path = ROOT / "examples" / (name + ".algo")
    source = path.read_text(encoding="utf-8")
    compile_source(source, filename=str(path))
    clocks = {}

    def tick(clock, amount=1):
        if not isinstance(amount, int) or amount < 0:
            raise ValueError("Ticks must charge a nonnegative integer")
        clocks[clock] = clocks.get(clock, 0) + amount

    environment = {
        "__builtins__": {}, "Int": int, "Seq": IndexedSequence,
        "const": lambda value: IndexedSequence(lambda _index: value), "tick": tick,
    }
    # Keep source annotations such as Seq[Seq[Int]] as annotations; this adapter
    # models the operations, while the real compiler checks their source types.
    exec(compile(source, str(path), "exec", flags=__future__.annotations.compiler_flag),
         environment, environment)
    return environment[ENTRY_POINTS[name]], clocks


def matrix_oracle(a, b, n):
    """Ordinary row-by-column multiplication, independent of example helpers."""
    return [sum(a[row][k] * b[k][column] for k in range(n))
            for row in range(n) for column in range(n)]


def matrix_input(values, n, seed):
    """Build finite rows with arbitrary nonzero contents outside the square."""
    default_row = IndexedSequence(lambda column: seed * column - 71)
    rows = [IndexedSequence(lambda column, row=row: seed * column + row + 31,
                            enumerate(values[row * n:(row + 1) * n]))
            for row in range(n)]
    matrix = IndexedSequence(lambda _row: default_row, enumerate(rows))
    return matrix, [matrix, default_row, *rows]


def expected_clocks(name, n):
    if name == "matrix_multiply":
        return {"multiply_add": n ** 3} if n else {}
    if n <= 0 or n & (n - 1):
        raise ValueError("Recursive examples require a positive power of two")
    depth = n.bit_length() - 1
    if name == "matrix_recursive":
        return {"multiplications": 8 ** depth,
                "calls": sum(8 ** level for level in range(depth + 1))}
    overhead = 0
    for level in range(depth):
        half = 2 ** level
        overhead = half * half + 7 * overhead
    costs = {"products": 7 ** depth,
             "calls": sum(7 ** level for level in range(depth + 1))}
    if overhead:
        costs.update(linear_cells=18 * overhead, copied_cells=12 * overhead)
    return costs


class Chapter4MatrixTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Compilation is cheap and done once per source, not once per matrix.
        cls.examples = {name: load_matrix_example(name) for name in ALGORITHMS}

    def check_product(self, name, a_values, b_values, n, *, alias=False, shared_rows=False):
        self.assertEqual(len(a_values), n * n)
        self.assertEqual(len(b_values), n * n)
        a, a_objects = matrix_input(a_values, n, 17)
        b, b_objects = (a, a_objects) if alias else matrix_input(b_values, n, 29)
        if shared_rows and n:
            # Repeated rows within a matrix and shared rows across both inputs
            # must remain valid, without requiring separation assumptions.
            for row in range(1, n):
                if row % 2:
                    a[row] = a[0]
                    b[row] = a[0]
        expected = matrix_oracle(a, b, n)
        # Complete overlays and default functions describe all integer indices,
        # so equality of these snapshots checks full input preservation here.
        objects = {id(value): value for value in a_objects + b_objects}
        snapshots = [(value, dict(value._values), value._default) for value in objects.values()]
        execute, clocks = self.examples[name]
        clocks.clear()
        result = execute(a, b, n)
        self.assertIsNot(result, a)
        self.assertIsNot(result, b)
        self.assertEqual([result[row][column] for row in range(n) for column in range(n)], expected)
        for value, overlay, default in snapshots:
            self.assertEqual(value._values, overlay)
            self.assertIs(value._default, default)
        active_rows = [result[row] for row in range(n)]
        self.assertEqual(len({id(row) for row in active_rows}), n,
                         "Each output row must have its own mutable identity")
        self.assertTrue(all(id(row) not in objects for row in active_rows),
                        "Output rows must be fresh, including when input rows alias")
        outside = (-10 ** 100, -17, -1, n, n + 1, 10 ** 100)
        for row in (*range(n), *outside):
            columns = outside if 0 <= row < n else (*range(n), *outside)
            for column in columns:
                self.assertEqual(result[row][column], 0,
                                 "Fresh results must be zero outside the n by n square")
        self.assertEqual(clocks, expected_clocks(name, n))

    def test_strassen_analysis_bundle_is_current(self):
        self.assertEqual(DESTINATION.read_text(encoding="utf-8"), build_analysis(),
                         "Rebuild with scripts/build_chapter4_analysis.py after editing proof modules")

    def test_empty_iterative_matrix(self):
        self.check_product("matrix_multiply", [], [], 0)

    def test_signed_random_matrices_and_exact_costs(self):
        rng = random.Random(20261008)
        for n in (1, 2, 4, 8):
            for case in range(8):
                a = [rng.randrange(-31, 32) for _ in range(n * n)]
                b = [rng.randrange(-31, 32) for _ in range(n * n)]
                for name in ALGORITHMS:
                    with self.subTest(algorithm=name, n=n, case=case):
                        self.check_product(name, a, b, n)

    def test_zero_identity_and_unbounded_integer_entries(self):
        huge = 10 ** 100 + 37
        for n in (1, 2, 4, 8):
            zero = [0] * (n * n)
            identity = [int(row == column) for row in range(n) for column in range(n)]
            arbitrary = [(-1 if cell % 2 else 1) * (huge + cell * cell)
                         for cell in range(n * n)]
            cases = ((zero, arbitrary), (arbitrary, zero),
                     (identity, arbitrary), (arbitrary, identity), (arbitrary, arbitrary))
            for case, (a, b) in enumerate(cases):
                for name in ALGORITHMS:
                    with self.subTest(algorithm=name, n=n, case=case):
                        self.check_product(name, a, b, n)

    def test_aliased_inputs_are_preserved(self):
        rng = random.Random(40204)
        for n in (1, 2, 4, 8):
            values = [rng.randrange(-100, 101) for _ in range(n * n)]
            for name in ALGORITHMS:
                with self.subTest(algorithm=name, n=n):
                        self.check_product(name, values, values, n, alias=True)

    def test_shared_input_rows_are_preserved(self):
        for n in (2, 4, 8):
            a = [cell - 7 for cell in range(n * n)]
            b = [3 * cell + 1 for cell in range(n * n)]
            for name in ALGORITHMS:
                with self.subTest(algorithm=name, n=n):
                    self.check_product(name, a, b, n, shared_rows=True)

    def test_iterative_odd_dimensions(self):
        for n in (3, 5, 7):
            self.check_product("matrix_multiply", list(range(n * n)),
                               list(reversed(range(n * n))), n)


class Chapter4AssumptionAuditTests(unittest.TestCase):
    def test_accepts_multiline_standard_axioms_and_axiom_free_report(self):
        output = ("'Chapter4.first' depends on axioms: [propext,\n"
                  " Classical.choice,\n Quot.sound]\n"
                  "'Chapter4.second' does not depend on any axioms\n")
        self.assertIsNone(audit_assumptions(output, ("Chapter4.first", "Chapter4.second")))

    def test_rejects_disallowed_axiom_after_newline(self):
        output = ("'Chapter4.first' depends on axioms: [propext,\n"
                  " Classical.choice, Quot.sound,\n unproved_contract]\n")
        diagnostic = audit_assumptions(output, ("Chapter4.first",))
        self.assertIn("Unexpected proof assumptions for Chapter4.first", diagnostic)
        self.assertIn("unproved_contract", diagnostic)

    def test_requires_a_complete_report_for_every_requested_theorem(self):
        first = "'Chapter4.first' does not depend on any axioms\n"
        for incomplete in ("", "'Chapter4.second' depends on axioms: [propext,\n"):
            with self.subTest(incomplete=incomplete):
                diagnostic = audit_assumptions(first + incomplete, ("Chapter4.first", "Chapter4.second"))
                self.assertIn("Missing axiom report for Chapter4.second", diagnostic)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class Chapter4ProofModulesTests(unittest.TestCase):
    def test_modular_proofs_and_assumptions(self):
        # Independently check real imports; the editor bundle cannot hide a
        # missing dependency. Also check general-framework applications that
        # deliberately stay outside the editor's single-file payload.
        result = check_proofs()
        self.assertTrue(result.ok, result.output)


if __name__ == "__main__":
    unittest.main()
