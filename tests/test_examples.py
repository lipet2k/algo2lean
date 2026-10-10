"""Algorithm checks for trusted, repository-owned example files.

This test-only adapter executes fixed examples as Python with mutable,
integer-indexed sequence objects. It is not used by the compiler
or editor, and never accepts arbitrary user source. Separate Lean tests
check actual emitted relations; these execution checks are not formal proofs.
"""

import bisect
import math
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.compiler import compile_source
from algo2lean.checker import prepare_lean_environment
from tests.test_lean import constructor_tactic


ROOT = Path(__file__).resolve().parents[1]


class IndexedSequence:
    """A mutable finite overlay on an arbitrary integer-indexed function."""

    def __init__(self, default, values=None):
        self._default = default
        self._values = dict(values or {})

    def __getitem__(self, index):
        if index in self._values:
            return self._values[index]
        return self._default(index)

    def __setitem__(self, index, value):
        self._values[index] = value

    def updated(self, index, value):
        self[index] = value
        return self

    def copied(self):
        return IndexedSequence(self._default, self._values)



def load_trusted_example(name):
    if name not in {"merge_sort", "gcd", "lower_bound", "mutable_sequences", "range_sum"}:
        raise ValueError("Only the fixed repository examples can be executed")
    path = ROOT / "examples" / (name + ".algo")
    source = path.read_text(encoding="utf-8")
    compile_source(source, filename=str(path))
    clock_counts = {}

    def tick(clock, amount=1):
        if not isinstance(amount, int) or amount < 0:
            raise ValueError("A clock increment must be a nonnegative integer")
        clock_counts[clock] = clock_counts.get(clock, 0) + amount

    environment = {
        "__builtins__": {}, "Int": int, "Bool": bool, "Seq": IndexedSequence, "range": range,
        "const": lambda value: IndexedSequence(lambda _index: value),
        "update": lambda sequence, index, value: sequence.updated(index, value),
        "copy": lambda sequence: sequence.copied(),
        "tick": tick, "_clock_counts": clock_counts,
    }
    exec(compile(source, str(path), "exec"), environment, environment)
    return environment


def sequence_with_interval(values, lo):
    return IndexedSequence(
        lambda index: index * 101 + 37,
        {lo + offset: value for offset, value in enumerate(values)},
    )


class ExampleAlgorithmsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.merge_functions = load_trusted_example("merge_sort")
        cls.gcd_functions = load_trusted_example("gcd")
        cls.search_functions = load_trusted_example("lower_bound")
        cls.mutable_functions = load_trusted_example("mutable_sequences")
        cls.range_functions = load_trusted_example("range_sum")

    def check_sort(self, values, lo, hi=None):
        hi = lo + len(values) if hi is None else hi
        source = sequence_with_interval(values, lo)
        snapshots = [source[i] for i in range(lo - 3, lo + len(values) + 3)]
        result = self.merge_functions["merge_sort"](source, lo, hi)
        expected = sorted(values) if hi > lo else values
        self.assertEqual([result[lo + i] for i in range(len(values))], expected)
        # The original sequence remains unchanged despite stores in merge().
        self.assertEqual([source[i] for i in range(lo - 3, lo + len(values) + 3)], snapshots)
        # This samples outside preservation; the separate Lean analysis proves
        # it for every outside integer index and every input interval.
        for index in (lo - 3, lo - 1, max(lo + len(values), hi), hi + 100,
                      -(10 ** 100), 10 ** 100):
            if not lo <= index < hi:
                self.assertEqual(result[index], source[index])

    def test_merge_sort_edge_cases(self):
        cases = [[], [4], [2, 1], [7, 7, 7], [0, -3, 4, -3, 1],
                 [10 ** 100, -(10 ** 100), 0, 10 ** 100],
                 list(range(12)), list(range(11, -1, -1))]
        for lo in (-17, 0, 29):
            for values in cases:
                with self.subTest(lo=lo, values=values):
                    self.check_sort(values, lo)
        self.check_sort([8, 2, 5], 7, hi=4)

    def test_merge_sort_random_intervals(self):
        rng = random.Random(20261007)
        for case in range(160):
            values = [rng.randrange(-15, 16) for _ in range(rng.randrange(33))]
            lo = rng.randrange(-50, 51)
            with self.subTest(case=case, lo=lo, values=values):
                self.check_sort(values, lo)

    def test_merge_sorted_halves(self):
        rng = random.Random(7102026)
        for case in range(60):
            left = sorted(rng.randrange(-9, 10) for _ in range(rng.randrange(12)))
            right = sorted(rng.randrange(-9, 10) for _ in range(rng.randrange(12)))
            values = left + right
            lo = rng.randrange(-20, 21)
            source = sequence_with_interval(values, lo)
            result = self.merge_functions["merge"](source, lo, lo + len(left), lo + len(values))
            with self.subTest(case=case):
                self.assertEqual([result[lo + i] for i in range(len(values))], sorted(values))
                self.assertEqual([source[lo + i] for i in range(len(values))], values)
                self.assertEqual(result[lo - 1], source[lo - 1])
                self.assertEqual(result[lo + len(values)], source[lo + len(values)])

    def test_mutable_sequence_examples(self):
        self.assertEqual(self.mutable_functions["alias_demo"](), 42)
        self.assertEqual(self.mutable_functions["copy_demo"](), 7)
        self.assertEqual(self.mutable_functions["rebind_demo"](), 2)
        self.assertEqual(self.mutable_functions["callee_demo"](), 41)
        shared = sequence_with_interval([3], 0)
        self.assertEqual(self.mutable_functions["aliased_parameters"](shared, shared), 11)
        self.assertEqual(shared[0], 11)
        independent = sequence_with_interval([3], 0)
        self.assertEqual(self.mutable_functions["aliased_parameters"](shared, independent), 3)

    def test_range_examples(self):
        for n in (-9, 0, 1, 12):
            self.assertEqual(self.range_functions["range_sum"](n), sum(range(n)))
        for start, stop, step in ((0, 7, 2), (7, -3, -2), (0, 7, -1),
                                  (-5, -5, 1), (10 ** 100, 10 ** 100 + 3, 1)):
            self.assertEqual(self.range_functions["stepped_sum"](start, stop, step),
                             sum(range(start, stop, step)))
        self.assertEqual(self.range_functions["empty_range_preserves_binding"](), 9)

    def test_merge_sort_demo(self):
        result = self.merge_functions["demo_merge_sort"]()
        self.assertEqual([result[i] for i in range(4)], [1, 1, 3, 4])
        self.assertEqual((result[-1], result[4], result[10 ** 100]), (99, 77, 0))

    def test_gcd_matches_mathematical_reference(self):
        cases = [(0, 0), (0, -15), (-15, 0), (54, 24), (-54, 24),
                 (-54, -24), (10 ** 100, 25 * 10 ** 90), (1, 10 ** 100)]
        rng = random.Random(20261008)
        cases.extend((rng.randrange(-10 ** 20, 10 ** 20), rng.randrange(-10 ** 20, 10 ** 20))
                     for _ in range(100))
        for a, b in cases:
            with self.subTest(a=a, b=b):
                self.assertEqual(self.gcd_functions["gcd"](a, b), math.gcd(a, b))

    def test_lower_bound_matches_bisect(self):
        rng = random.Random(20261009)
        for case in range(100):
            values = sorted(rng.randrange(-12, 13) for _ in range(rng.randrange(30)))
            lo = rng.randrange(-40, 41)
            sequence = sequence_with_interval(values, lo)
            for target in (-10 ** 100, -12, -1, 0, 6, 12, 10 ** 100):
                with self.subTest(case=case, target=target):
                    actual = self.search_functions["lower_bound"](sequence, lo, lo + len(values), target)
                    self.assertEqual(actual, lo + bisect.bisect_left(values, target))
        sequence = sequence_with_interval([5], -9)
        self.assertEqual(self.search_functions["lower_bound"](sequence, -9, -12, 5), -9)
        self.assertEqual(self.search_functions["demo_lower_bound"](), 1)


class MergeSortRuntimeTests(unittest.TestCase):
    def setUp(self):
        self.environment = load_trusted_example("merge_sort")
        self.costs = self.environment["_clock_counts"]

    def test_base_cases_charge_one_call_and_no_element_writes(self):
        for lo, hi in ((-8, -8), (4, 5), (13, -2)):
            with self.subTest(lo=lo, hi=hi):
                self.costs.clear()
                source = sequence_with_interval([7, 3], lo)
                result = self.environment["merge_sort"](source, lo, hi)
                self.assertIs(result, source)
                self.assertEqual(self.costs, {"merge_sort": 1})

    def test_merging_charges_exactly_one_tick_per_written_element(self):
        cases = [([], []), ([], [1, 4, 9]), ([1, 4, 9], []),
                 ([1, 3, 5], [2, 4, 6]), ([2, 2], [2, 2, 2]),
                 ([10, 11], [-8, -7, -6]), ([-9, -8], [3, 4, 5])]
        for left, right in cases:
            with self.subTest(left=left, right=right):
                self.costs.clear()
                lo = -11
                values = left + right
                source = sequence_with_interval(values, lo)
                result = self.environment["merge"](source, lo, lo + len(left), lo + len(values))
                self.assertEqual(self.costs.get("merge_sort", 0), len(values))
                self.assertEqual([result[lo + i] for i in range(len(values))], sorted(values))

    def test_power_of_two_lengths_match_the_closed_form_tree_cost(self):
        # A complete balanced tree has 2*n-1 calls and n writes at each merge level.
        for depth in range(9):
            length = 2 ** depth
            expected = 2 * length - 1 + length * depth
            for values in (list(range(length)), list(range(length - 1, -1, -1)), [4] * length):
                with self.subTest(depth=depth, values=values[:8]):
                    self.costs.clear()
                    source = sequence_with_interval(values, -17)
                    result = self.environment["merge_sort"](source, -17, -17 + length)
                    self.assertEqual(self.costs, {"merge_sort": expected})
                    self.assertEqual([result[-17 + i] for i in range(length)], sorted(values))

    def test_unbalanced_lengths_obey_the_proved_logarithmic_envelope(self):
        for length in range(66):
            with self.subTest(length=length):
                self.costs.clear()
                source = sequence_with_interval(list(range(length - 1, -1, -1)), 9)
                self.environment["merge_sort"](source, 9, 9 + length)
                floor_log = max(0, length.bit_length() - 1)
                self.assertLessEqual(self.costs["merge_sort"], 2 * length * (floor_log + 1) + 1)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ExampleLeanTests(unittest.TestCase):
    def test_merge_sort_relation_and_infinite_outside_preservation(self):
        source = (ROOT / "examples" / "merge_sort.algo").read_text(encoding="utf-8")
        generated = compile_source(source, filename="merge_sort.algo").lean
        proofs = (ROOT / "tests" / "proofs" / "merge_sort.lean").read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory(prefix="algo2lean-sort-proof-") as directory:
            path = Path(directory) / "MergeSort.lean"
            path.write_text(generated + constructor_tactic(generated) + proofs, encoding="utf-8")
            result = subprocess.run(
                ["lean", "+v4.26.0", str(path)], cwd=str(ROOT),
                env=prepare_lean_environment(timeout=120),
                capture_output=True, text=True, timeout=120,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("declaration uses 'sorry'", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
