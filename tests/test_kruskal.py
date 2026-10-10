"""Behavior and Lean contracts for the reusable Kruskal project components.

Execution is restricted to fixed repository-owned example sources. These
behavior checks supplement, rather than replace, proofs of generated Lean.
"""

from pathlib import Path
import random
import shutil
import unittest

from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from tests.test_examples import IndexedSequence


ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "examples/kruskal"


def union_find_environment():
    source = (PROJECT / "union_find.algo").read_text()
    compile_source(source)
    clocks = {}

    def tick(name, amount=1):
        assert isinstance(amount, int) and amount >= 0
        clocks[name] = clocks.get(name, 0) + amount

    environment = {
        "__builtins__": {"__build_class__": __build_class__},
        "__name__": "trusted_union_find_example",
        "Int": int, "Bool": bool, "Seq": IndexedSequence,
        "const": lambda value: IndexedSequence(lambda _index: value),
        "tick": tick,
    }
    exec(compile(source, str(PROJECT / "union_find.algo"), "exec"), environment)
    return environment["UnionFind"], clocks


class UnionFindBehaviorTests(unittest.TestCase):
    def test_initial_singletons_and_empty_universe(self):
        constructor, clocks = union_find_environment()
        for size in (0, 1, 32):
            before = clocks.get("uf_init", 0)
            sets = constructor(size)
            self.assertEqual(sets.size, size)
            self.assertEqual(clocks["uf_init"] - before, size + 1)
            for vertex in range(size):
                self.assertEqual(sets.parent[vertex], vertex)
                self.assertEqual(sets.rank[vertex], 0)

    def test_find_compresses_entire_path_without_changing_ranks(self):
        constructor, clocks = union_find_environment()
        sets = constructor(16)
        # Equal-rank merges create a height-four tree before any compression.
        for width in (1, 2, 4, 8):
            for start in range(0, 16, 2 * width):
                self.assertTrue(sets.union(start, start + width))
        path, vertex = [], 15
        while sets.parent[vertex] != vertex:
            path.append(vertex)
            vertex = sets.parent[vertex]
        self.assertEqual(len(path), 4)
        ranks = [sets.rank[i] for i in range(16)]
        before = dict(clocks)
        self.assertEqual(sets.find(15), vertex)
        for visited in path:
            self.assertEqual(sets.parent[visited], vertex)
        self.assertEqual([sets.rank[i] for i in range(16)], ranks)
        self.assertEqual(clocks["uf_find"] - before["uf_find"], 5)
        self.assertEqual(clocks["uf_compress"] - before.get("uf_compress", 0), 4)
        before = dict(clocks)
        self.assertEqual(sets.find(15), vertex)
        self.assertEqual(clocks["uf_find"] - before["uf_find"], 2)

    def test_random_unions_match_independent_partition_and_rank_bound(self):
        constructor, _ = union_find_environment()
        rng = random.Random(20261010)
        for size in (1, 2, 7, 32):
            sets = constructor(size)
            labels = list(range(size))
            for _ in range(120):
                a, b = rng.randrange(size), rng.randrange(size)
                first, second = labels[a], labels[b]
                self.assertEqual(sets.union(a, b), first != second)
                labels = [first if label == second else label for label in labels]
                for x in range(size):
                    parent = sets.parent[x]
                    self.assertTrue(0 <= parent < size)
                    self.assertLessEqual(sets.rank[x], size.bit_length() - 1)
                    if parent != x:
                        self.assertLess(sets.rank[x], sets.rank[parent])
                    for y in range(size):
                        self.assertEqual(sets.find(x) == sets.find(y), labels[x] == labels[y])

    def test_amortized_mixed_sequence_with_preexisting_clocks(self):
        # Balanced unions create long paths before lookups compress them. Count
        # only increments: client work and earlier uses of the same clocks must
        # not be charged to this sequence of calls.
        for size in (1, 2, 16, 1024):
            constructor, clocks = union_find_environment()
            clocks.update({"caller_work": 97, "uf_init": 101, "uf_find": 103,
                           "uf_compress": 107, "uf_union": 109})
            sets = constructor(size)
            baseline = dict(clocks)
            unions = finds = 0
            width = 1
            while width < size:
                for first in range(0, size, 2 * width):
                    if first + width < size:
                        sets.union(first, first + width)
                        unions += 1
                width *= 2
            before_deep = clocks["uf_find"] + clocks["uf_compress"]
            sets.find(size - 1)
            finds += 1
            deep_cost = clocks["uf_find"] + clocks["uf_compress"] - before_deep
            # For these sizes the least positive Ackermann index is 1, 2, or 3:
            # A_1(1)=3, A_2(1)=7, A_3(1)=2047.
            alpha = 1 if size < 3 else 2 if size < 7 else 3
            if size == 1024:
                self.assertGreater(deep_cost, 2 * alpha + 3)
            rng = random.Random(3180 + size)
            for _ in range(3 * size):
                vertex = rng.randrange(size)
                if rng.randrange(3) == 0:
                    sets.union(vertex, rng.randrange(size))
                    unions += 1
                else:
                    sets.find(vertex)
                    finds += 1
            actual = sum(clocks[name] - baseline[name] for name in
                         ("uf_find", "uf_compress", "uf_union"))
            self.assertLessEqual(actual, unions * (6 * alpha + 7) + finds * (2 * alpha + 3))
            self.assertEqual(clocks["uf_init"], baseline["uf_init"])
            self.assertEqual(clocks["caller_work"], 97)

    def test_objects_do_not_share_storage(self):
        constructor, _ = union_find_environment()
        first, second = constructor(4), constructor(4)
        first.union(0, 1)
        self.assertEqual(first.find(0), first.find(1))
        self.assertNotEqual(second.find(0), second.find(1))


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class KruskalLeanTests(unittest.TestCase):
    def test_union_find_analysis(self):
        compilation = compile_project("union_find", root=PROJECT)
        analysis = (PROJECT / "analysis/union_find.lean").read_text()
        result = check_project(compilation, analysis=analysis, timeout=300)
        self.assertTrue(result.ok, result.output)

    def test_union_find_constructor_analysis(self):
        compilation = compile_project("union_find", root=PROJECT)
        analysis = (PROJECT / "analysis/union_find_init.lean").read_text()
        result = check_project(compilation, analysis=analysis,
                               analysis_module="Algo.union_find_init.Analysis", timeout=300)
        self.assertTrue(result.ok, result.output)


if __name__ == "__main__":
    unittest.main()
