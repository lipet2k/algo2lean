"""Behavioral regressions for the fixed CLRS Chapter 4 matrix examples.

This Python adapter runs trusted repository files only. It checks examples
against an independent mathematical oracle; it is not the Lean semantics or
formal proof. The existing test_analysis suite checks canonical editor analyses.
The modular regression here independently checks import dependencies and the
general recurrence applications that are maintained outside the editor bundle.
"""

from pathlib import Path
import random
import shutil
import unittest

from algo2lean.compiler import compile_source
from scripts.build_chapter4_analysis import build_analysis, DESTINATION
from scripts.check_chapter4_proofs import check_proofs
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
    exec(compile(source, str(path), "exec"), environment, environment)
    return environment[ENTRY_POINTS[name]], clocks


def matrix_oracle(a, b, n):
    """Ordinary row-by-column multiplication, independent of example helpers."""
    return [sum(a[row * n + k] * b[k * n + column] for k in range(n))
            for row in range(n) for column in range(n)]


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

    def check_product(self, name, a_values, b_values, n, *, alias=False):
        self.assertEqual(len(a_values), n * n)
        self.assertEqual(len(b_values), n * n)
        a = IndexedSequence(lambda index: 17 * index + 31, enumerate(a_values))
        b = a if alias else IndexedSequence(
            lambda index: 29 * index - 43, enumerate(b_values))
        expected = matrix_oracle(a_values, a_values if alias else b_values, n)
        # Complete overlays and default functions describe all integer indices,
        # so equality of these snapshots checks full input preservation here.
        snapshots = [(dict(value._values), value._default) for value in (a, b)]
        execute, clocks = self.examples[name]
        clocks.clear()
        result = execute(a, b, n)
        self.assertIsNot(result, a)
        self.assertIsNot(result, b)
        self.assertEqual([result[cell] for cell in range(n * n)], expected)
        for value, (overlay, default) in zip((a, b), snapshots):
            self.assertEqual(value._values, overlay)
            self.assertIs(value._default, default)
        for index in (-10 ** 100, -17, -1, n * n, n * n + 1, 10 ** 100):
            self.assertEqual(result[index], 0, "Fresh results must be zero outside the matrix")
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
