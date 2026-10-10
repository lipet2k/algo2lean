"""Behavioral checks of the proved Ackermann potential on actual source calls.

Only the fixed, compiler-validated repository source is executed by the trusted
adapter in test_kruskal.  The independent evaluator below computes finite
Ackermann comparisons, never the enormous integers beyond their thresholds.
These regressions supplement the Lean proofs; they are not proof substitutes.
"""

from functools import lru_cache
import random
import unittest

from tests.test_kruskal import union_find_environment


UF_CLOCKS = ("uf_init", "uf_find", "uf_compress", "uf_union")


@lru_cache(maxsize=16384)
def ackermann_capped(level, value, cap):
    """min(A_level(value), cap), with A_0(x)=x+1 and A_{k+1}=A_k^(x+1)(x)."""
    if value >= cap:
        return cap
    if level == 0:
        return min(value + 1, cap)
    result = value
    for _ in range(value + 1):
        result = ackermann_capped(level - 1, result, cap)
        if result == cap:
            break
    return result


def inverse_ackermann(size):
    """The least positive level whose value at one strictly exceeds size."""
    level = 1
    while ackermann_capped(level, 1, size + 1) <= size:
        level += 1
    return level


def forest_snapshot(sets):
    return ([sets.parent[i] for i in range(sets.size)],
            [sets.rank[i] for i in range(sets.size)])


def root_and_depth(parents, vertex):
    depth = 0
    while parents[vertex] != vertex:
        vertex = parents[vertex]
        depth += 1
        if depth >= len(parents):
            raise AssertionError("parent pointers must form a forest")
    return vertex, depth


def forest_potential(parents, ranks):
    """Calculate the rank/level/iteration potential directly from the forest.

    A root owns alpha*rank credit.  A positive-rank nonroot subtracts its
    level*rank and its iteration count.  Rank-zero vertices have zero credit.
    Saturation above the parent's rank preserves every comparison performed.
    """
    size, alpha = len(parents), inverse_ackermann(len(parents))
    total = 0
    for vertex, rank in enumerate(ranks):
        parent = parents[vertex]
        assert 0 <= parent < size
        if parent == vertex:
            total += alpha * rank
            continue
        parent_rank = ranks[parent]
        assert 0 <= rank < parent_rank
        if rank == 0:
            continue
        cap = parent_rank + 1
        level = 0
        while ackermann_capped(level + 1, rank, cap) <= parent_rank:
            level += 1
        iterations, value = 0, rank
        while True:
            value = ackermann_capped(level, value, cap)
            if value > parent_rank:
                break
            iterations += 1
        assert 0 <= level < alpha
        assert 1 <= iterations <= rank
        credit = (alpha - level) * rank - iterations
        assert credit >= 0
        total += credit
    return total


class UnionFindAmortizedTests(unittest.TestCase):
    def test_saturating_hierarchy_and_inverse_thresholds(self):
        # Closed forms independently calibrate both the hierarchy convention
        # and saturation, including equality at the strict inverse threshold.
        for cap in range(1, 25):
            for value in range(9):
                self.assertEqual(ackermann_capped(0, value, cap), min(value + 1, cap))
                self.assertEqual(ackermann_capped(1, value, cap), min(2 * value + 1, cap))
                self.assertEqual(ackermann_capped(2, value, cap),
                                 min(2 ** (value + 1) * (value + 1) - 1, cap))
        self.assertEqual(ackermann_capped(3, 1, 2048), 2047)
        for size, expected in ((0, 1), (1, 1), (2, 1), (3, 2), (6, 2),
                               (7, 3), (2046, 3), (2047, 4)):
            self.assertEqual(inverse_ackermann(size), expected)

    def new_sets(self, size):
        constructor, clocks = union_find_environment()
        clocks.update({"uf_init": 101, "uf_find": 103, "uf_compress": 107,
                       "uf_union": 109, "caller_work": 113, "heap_swaps": 127})
        before = dict(clocks)
        sets = constructor(size)
        self.assertEqual(clocks["uf_init"] - before["uf_init"], size + 1)
        self.assertEqual({name: value for name, value in clocks.items() if name != "uf_init"},
                         {name: value for name, value in before.items() if name != "uf_init"})
        self.assertEqual(forest_potential(*forest_snapshot(sets)), 0)
        return sets, clocks

    def check_operation(self, sets, clocks, operation, first, second=None):
        parents, ranks = forest_snapshot(sets)
        before_potential = forest_potential(parents, ranks)
        before = dict(clocks)
        first_root, first_depth = root_and_depth(parents, first)
        alpha = inverse_ackermann(sets.size)
        if operation == "find":
            self.assertEqual(sets.find(first), first_root)
            budget = 2 * alpha + 3
            self.assertEqual([sets.rank[i] for i in range(sets.size)], ranks)
            self.assertEqual(clocks["uf_find"] - before["uf_find"], first_depth + 1)
            self.assertEqual(clocks["uf_compress"] - before["uf_compress"], first_depth)
            self.assertEqual(clocks["uf_union"], before["uf_union"])
            vertex = first
            while parents[vertex] != vertex:
                self.assertEqual(sets.parent[vertex], first_root)
                vertex = parents[vertex]
        else:
            self.assertEqual(operation, "union")
            second_root, _ = root_and_depth(parents, second)
            self.assertEqual(sets.union(first, second), first_root != second_root)
            budget = 6 * alpha + 7
            self.assertEqual(clocks["uf_union"] - before["uf_union"], 1)
        after_potential = forest_potential(*forest_snapshot(sets))
        cost = sum(clocks[name] - before[name] for name in UF_CLOCKS)
        self.assertLessEqual(cost + 2 * after_potential, 2 * before_potential + budget)
        self.assertEqual(clocks["uf_init"], before["uf_init"])
        self.assertEqual(clocks["caller_work"], before["caller_work"])
        self.assertEqual(clocks["heap_swaps"], before["heap_swaps"])
        return cost

    def test_balanced_trees_pay_for_long_paths_and_repeated_finds(self):
        for size in (1, 2, 16, 64, 128):
            sets, clocks = self.new_sets(size)
            width = 1
            while width < size:
                for first in range(0, size, 2 * width):
                    self.check_operation(sets, clocks, "union", first, first + width)
                width *= 2
            before_potential = forest_potential(*forest_snapshot(sets))
            cost = self.check_operation(sets, clocks, "find", size - 1)
            if size >= 64:
                # An individual call exceeds its amortized allowance.  Credit
                # from this same forest, accrued by the earlier unions, pays.
                self.assertGreater(cost, 2 * inverse_ackermann(size) + 3)
                self.assertLess(forest_potential(*forest_snapshot(sets)), before_potential)
            stable_potential = forest_potential(*forest_snapshot(sets))
            for _ in range(8):
                self.assertEqual(self.check_operation(sets, clocks, "find", size - 1),
                                 1 if size == 1 else 3)
                self.assertEqual(forest_potential(*forest_snapshot(sets)), stable_potential)

    def test_random_mixed_calls_telescope_from_nonzero_counters(self):
        for size in (0, 1, 2, 3, 7, 17, 64):
            sets, clocks = self.new_sets(size)
            baseline = dict(clocks)
            finds = unions = cumulative_cost = 0
            rng = random.Random(62903 + size)
            for _ in range(180 if size else 0):
                first = rng.randrange(size)
                if rng.randrange(3) == 0:
                    cumulative_cost += self.check_operation(sets, clocks, "find", first)
                    finds += 1
                else:
                    cumulative_cost += self.check_operation(
                        sets, clocks, "union", first, rng.randrange(size))
                    unions += 1
                alpha = inverse_ackermann(size)
                self.assertLessEqual(cumulative_cost + 2 * forest_potential(*forest_snapshot(sets)),
                                     finds * (2 * alpha + 3) + unions * (6 * alpha + 7))
            self.assertEqual(cumulative_cost,
                             sum(clocks[name] - baseline[name] for name in UF_CLOCKS))


if __name__ == "__main__":
    unittest.main()
