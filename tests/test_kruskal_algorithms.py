"""Independent behavior and Lean regressions for the concrete Kruskal project.

Only the five fixed, repository-owned Algo2Lean sources below are executed.
The finite-graph oracle enumerates spanning forests and uses graph traversal;
it does not reproduce Kruskal, disjoint sets, or the imported heap algorithm.
"""

import ast
from itertools import combinations
from pathlib import Path
import random
import shutil
import tempfile
import unittest

from algo2lean.editor_examples import load_example_project
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from tests.test_examples import IndexedSequence


ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "examples/kruskal"
TRUSTED_IMPORTS = {
    "indexed_heap": {},
    "union_find": {},
    "sort_indices": {"indexed_heap": frozenset({"MinHeap"})},
    "kruskal_sorted": {"union_find": frozenset({"UnionFind"})},
    "kruskal": {
        "sort_indices": frozenset({"sort_indices"}),
        "kruskal_sorted": frozenset({"kruskal_sorted"}),
    },
}


def trusted_environment(entry, initial_clocks=None):
    """Load an allowlisted source graph without executing Python import hooks.

    Compilation first validates the actual Algo2Lean project. AST imports are
    removed only after their source and exported names match the fixed graph;
    their bindings come from recursively loaded trusted example environments.
    This is a test harness for repository files, not an arbitrary-code sandbox.
    """
    if entry not in TRUSTED_IMPORTS:
        raise ValueError("Only the fixed Kruskal example modules can be executed")
    compile_project(entry, root=PROJECT)
    clocks = {"caller_work": 23}
    clocks.update(initial_clocks or {})
    loaded = {}

    def tick(name, amount=1):
        if not isinstance(amount, int) or amount < 0:
            raise ValueError("Clock increments must be nonnegative integers")
        clocks[name] = clocks.get(name, 0) + amount

    def load(name):
        if name in loaded:
            return loaded[name]
        if name not in TRUSTED_IMPORTS:
            raise ValueError("Untrusted example import: " + name)
        path = PROJECT / (name + ".algo")
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        environment = {
            "__builtins__": {"__build_class__": __build_class__},
            "__name__": "trusted_kruskal_example_" + name,
            "Int": int,
            "Bool": bool,
            "Seq": IndexedSequence,
            "const": lambda value: IndexedSequence(lambda _index: value),
            "tick": tick,
        }
        imports = []
        body = []
        for statement in tree.body:
            if isinstance(statement, ast.ImportFrom):
                allowed = TRUSTED_IMPORTS[name].get(statement.module)
                if statement.level or allowed is None:
                    raise ValueError("Unexpected trusted-example import")
                dependency = load(statement.module)
                for imported in statement.names:
                    if imported.name not in allowed:
                        raise ValueError("Unexpected trusted-example export")
                    environment[imported.asname or imported.name] = dependency[imported.name]
                imports.append(statement)
            elif isinstance(statement, ast.Import):
                raise ValueError("Only the explicit named example imports are supported")
            else:
                body.append(statement)
        # No nested import statement can evade the top-level allowlist.
        for node in ast.walk(tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)) and node not in imports:
                raise ValueError("Nested imports are outside the trusted example graph")
        tree.body = body
        exec(compile(tree, str(path), "exec"), environment)
        loaded[name] = environment
        return environment

    return load(entry), clocks


def sequence(values):
    """Include observable values outside the input prefix to detect extra writes."""
    return IndexedSequence(lambda index: 1000003 + 17 * index, dict(enumerate(values)))


def components(size, edges, selected):
    """Canonical connectivity partition, computed solely with adjacency traversal."""
    neighbors = [set() for _ in range(size)]
    for index in selected:
        source, target, _weight = edges[index]
        neighbors[source].add(target)
        neighbors[target].add(source)
    unseen = set(range(size))
    result = []
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        pending = [start]
        component = {start}
        while pending:
            vertex = pending.pop()
            discovered = neighbors[vertex] & unseen
            unseen.difference_update(discovered)
            component.update(discovered)
            pending.extend(discovered)
        result.append(frozenset(component))
    return frozenset(result)


def exhaustive_minimum_forest(size, edges):
    """Enumerate every spanning forest and return its globally minimum weight.

    An undirected multigraph with c components is a forest exactly when it has
    n-c edges. Requiring the original connectivity partition and this edge count
    therefore excludes cycles, parallel-edge cycles, and loops independently
    of the implementation's edge order and union-find decisions.
    """
    partition = components(size, edges, range(len(edges)))
    edge_count = size - len(partition)
    best = None
    for selected in combinations(range(len(edges)), edge_count):
        if components(size, edges, selected) == partition:
            weight = sum(edges[index][2] for index in selected)
            best = weight if best is None else min(best, weight)
    if best is None:
        raise AssertionError("Every finite undirected graph has a spanning forest")
    return partition, edge_count, best


class KeyedSortBehaviorTests(unittest.TestCase):
    def check_keys(self, values):
        environment, clocks = trusted_environment("sort_indices")
        keys = sequence(values)
        original = dict(keys._values)
        observed = {-11: keys[-11], -1: keys[-1], len(values): keys[len(values)]}
        output = environment["sort_indices"](keys, len(values))
        order = [output[index] for index in range(len(values))]
        self.assertEqual(sorted(order), list(range(len(values))))
        self.assertEqual([values[index] for index in order], sorted(values))
        self.assertIsNot(output, keys)
        self.assertEqual(keys._values, original)
        self.assertEqual({index: keys[index] for index in observed}, observed)
        for index in (-19, -1, len(values), len(values) + 17):
            self.assertEqual(output[index], 0)
        count = len(values)
        depth = (count + 1).bit_length() - 1
        self.assertEqual(clocks.get("sort_steps", 0), 2 * count)
        self.assertLessEqual(clocks.get("heap_comparisons", 0), 4 * count * depth)
        self.assertLessEqual(clocks.get("heap_swaps", 0), 2 * count * (depth + 1))
        runtime = sum(clocks.get(name, 0) for name in
                      ("sort_steps", "heap_comparisons", "heap_swaps"))
        self.assertLessEqual(runtime, 2 * count * (3 * depth + 2))
        self.assertEqual(clocks["caller_work"], 23)

    def test_empty_singleton_duplicate_negative_and_extreme_keys(self):
        cases = [[], [4], [-8], [5] * 17, [0, -4, 0, 2, -4, -9, 2],
                 [10**80, -(10**100), 0, 10**80, -(10**100)],
                 list(range(32)), list(reversed(range(33)))]
        for values in cases:
            with self.subTest(values=values):
                self.check_keys(values)

    def test_seeded_random_permutations_and_proven_clock_bound(self):
        rng = random.Random(202610101)
        for count in (2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 80):
            for attempt in range(4):
                with self.subTest(count=count, attempt=attempt):
                    self.check_keys([rng.randrange(-13, 14) for _ in range(count)])

    def test_calls_return_separate_arrays_and_preserve_inputs(self):
        environment, _clocks = trusted_environment("sort_indices")
        keys = sequence([3, -1, 2, -1])
        first = environment["sort_indices"](keys, 4)
        second = environment["sort_indices"](keys, 4)
        saved = [second[index] for index in range(4)]
        first[0] = 99
        self.assertIsNot(first, second)
        self.assertEqual([second[index] for index in range(4)], saved)
        self.assertEqual([keys[index] for index in range(4)], [3, -1, 2, -1])


class KruskalBehaviorTests(unittest.TestCase):
    def check_graph(self, size, edges, *, order=None, initial_clocks=None):
        entry = "kruskal" if order is None else "kruskal_sorted"
        environment, clocks = trusted_environment(entry, initial_clocks)
        baseline = dict(clocks)
        sources = sequence([edge[0] for edge in edges])
        targets = sequence([edge[1] for edge in edges])
        weights = sequence([edge[2] for edge in edges])
        inputs = (sources, targets, weights)
        arguments = (size, sources, targets, weights, len(edges))
        if order is not None:
            self.assertEqual(sorted(order), list(range(len(edges))))
            self.assertEqual([edges[index][2] for index in order],
                             sorted(edge[2] for edge in edges))
            sorted_ids = sequence(order)
            inputs += (sorted_ids,)
            arguments += (sorted_ids,)
        saved = [dict(values._values) for values in inputs]
        outside = [{index: values[index] for index in (-7, -1, len(edges), len(edges) + 13)}
                   for values in inputs]
        chosen = environment[entry](*arguments)
        increments = {clock: clocks.get(clock, 0) - baseline.get(clock, 0)
                      for clock in clocks.keys() | baseline.keys()}
        flags = [chosen[index] for index in range(len(edges))]
        self.assertTrue(all(value in (0, 1) for value in flags))
        selected = [index for index, value in enumerate(flags) if value == 1]
        partition, edge_count, minimum = exhaustive_minimum_forest(size, edges)
        self.assertEqual(components(size, edges, selected), partition,
                         "The selected edges must span every original component")
        self.assertEqual(len(selected), edge_count,
                         "A spanning selection with n-c edges is acyclic, including in a multigraph")
        self.assertEqual(sum(edges[index][2] for index in selected), minimum,
                         "The forest must attain the global exhaustive minimum")
        for index in selected:
            self.assertNotEqual(edges[index][0], edges[index][1], "Self-loops cannot belong to a forest")
        for values, before, outside_values in zip(inputs, saved, outside):
            self.assertIsNot(chosen, values)
            self.assertEqual(values._values, before)
            self.assertEqual({index: values[index] for index in outside_values}, outside_values)
        for index in (-7, -1, len(edges), len(edges) + 13):
            self.assertEqual(chosen[index], 0)
        count = len(edges)
        self.assertEqual(increments.get("kruskal", 0), count + 1)
        self.assertEqual(increments.get("uf_init", 0), size + 1)
        self.assertEqual(increments.get("uf_union", 0), len(selected))
        self.assertEqual(increments.get("sort_steps", 0), 2 * count if order is None else 0)
        find_work = increments.get("uf_find", 0) + increments.get("uf_compress", 0)
        vertex_depth = max(0, size.bit_length() - 1)
        self.assertLessEqual(find_work, 2 * (count + len(selected)) * (2 * vertex_depth + 1))
        sort_work = sum(increments.get(name, 0) for name in
                        ("sort_steps", "heap_comparisons", "heap_swaps"))
        edge_depth = (count + 1).bit_length() - 1
        self.assertLessEqual(sort_work, 2 * count * (3 * edge_depth + 2))
        self.assertEqual(clocks["caller_work"], baseline["caller_work"])
        if order is not None:
            for name in ("sort_steps", "heap_comparisons", "heap_swaps"):
                self.assertEqual(increments.get(name, 0), 0,
                                 "The sorted entry must not sort or operate a sorting heap")
        return selected

    def test_empty_isolated_loops_parallel_negative_disconnected_and_tree(self):
        cases = [
            (0, []),
            (1, []),
            (5, []),
            (1, [(0, 0, -20), (0, 0, 0), (0, 0, 17)]),
            (2, [(0, 1, 8), (0, 1, -3), (1, 0, -3), (1, 1, -100)]),
            (4, [(0, 1, -5), (1, 2, 0), (2, 3, 9)]),
            (6, [(0, 1, 9), (1, 2, -4), (0, 2, 2), (3, 4, -8),
                 (3, 4, 1), (5, 5, -100)]),
            (4, [(0, 1, 1), (1, 2, 1), (2, 3, 1), (3, 0, 1),
                 (0, 2, 1), (1, 3, 1)]),
            (3, [(0, 1, 10**60), (1, 2, -(10**80)), (0, 2, -(10**80) - 1)]),
        ]
        for size, edges in cases:
            with self.subTest(size=size, edges=edges):
                self.check_graph(size, edges)

    def test_seeded_small_graphs_against_exhaustive_global_minimum(self):
        rng = random.Random(202610102)
        for attempt in range(80):
            size = rng.randrange(0, 7)
            count = rng.randrange(0, 10) if size else 0
            edges = [(rng.randrange(size), rng.randrange(size), rng.randrange(-9, 10))
                     for _ in range(count)]
            with self.subTest(attempt=attempt, size=size, edges=edges):
                self.check_graph(size, edges)

    def test_explicit_loop_handles_more_edges_than_the_python_recursion_limit(self):
        environment, clocks = trusted_environment("kruskal")
        count = 2000
        sources = sequence([0] * count)
        targets = sequence([1] * count)
        weights = sequence(list(range(count, 0, -1)))
        chosen = environment["kruskal"](2, sources, targets, weights, count)
        self.assertEqual([chosen[index] for index in range(count)], [0] * (count - 1) + [1])
        self.assertEqual(clocks.get("uf_union", 0), 1)
        self.assertEqual(clocks.get("kruskal", 0), count + 1)

    def test_exhaustive_oracle_rejects_nonminimal_spanning_tree(self):
        # The oracle's optimum differs from a valid but expensive spanning tree.
        edges = [(0, 1, 10), (1, 2, 10), (0, 2, -7)]
        partition, edge_count, optimum = exhaustive_minimum_forest(3, edges)
        self.assertEqual(partition, frozenset({frozenset({0, 1, 2})}))
        self.assertEqual(edge_count, 2)
        self.assertEqual(optimum, 3)
        self.assertGreater(sum(edges[index][2] for index in (0, 1)), optimum)


class SortedKruskalBehaviorTests(unittest.TestCase):
    check_graph = KruskalBehaviorTests.check_graph

    # Distinct nonzero baselines make resetting or overwriting any clock visible.
    initial_clocks = {
        "sort_steps": 109, "heap_comparisons": 223, "heap_swaps": 307,
        "uf_init": 419, "uf_find": 503, "uf_compress": 601,
        "uf_union": 709, "kruskal": 809, "caller_work": 10**70,
    }

    def test_sorted_input_skips_sorting_with_arbitrary_starting_counters(self):
        cases = [
            (0, []), (1, []), (5, []),
            (1, [(0, 0, -20), (0, 0, 0), (0, 0, 17)]),
            (2, [(0, 1, 8), (0, 1, -3), (1, 0, -3), (1, 1, -100)]),
            (6, [(0, 1, 9), (1, 2, -4), (0, 2, 2), (3, 4, -8),
                 (3, 4, 1), (5, 5, -100)]),
            (4, [(0, 1, 1), (1, 2, 1), (2, 3, 1), (3, 0, 1),
                 (0, 2, 1), (1, 3, 1)]),
            (3, [(0, 1, 10**60), (1, 2, -(10**80)), (0, 2, -(10**80) - 1)]),
        ]
        for size, edges in cases:
            # Reverse the tie order: no stability assumption belongs to this API.
            order = sorted(range(len(edges)), key=lambda index: (edges[index][2], -index))
            with self.subTest(size=size, edges=edges):
                self.check_graph(size, edges, order=order, initial_clocks=self.initial_clocks)

    def test_seeded_sorted_orders_against_exhaustive_minimum(self):
        rng = random.Random(202610104)
        for attempt in range(64):
            size = rng.randrange(0, 7)
            count = rng.randrange(0, 10) if size else 0
            edges = [(rng.randrange(size), rng.randrange(size), rng.randrange(-4, 5))
                     for _ in range(count)]
            order = list(range(count))
            rng.shuffle(order)
            order.sort(key=lambda index: edges[index][2])
            with self.subTest(attempt=attempt, size=size, edges=edges, order=order):
                self.check_graph(size, edges, order=order, initial_clocks=self.initial_clocks)

    def test_input_order_controls_equal_weight_choices(self):
        edges = [(0, 1, 5), (1, 2, 5), (0, 2, 5)]
        forward = self.check_graph(3, edges, order=[0, 1, 2],
                                   initial_clocks=self.initial_clocks)
        reverse = self.check_graph(3, edges, order=[2, 1, 0],
                                   initial_clocks=self.initial_clocks)
        self.assertEqual(forward, [0, 1])
        self.assertEqual(reverse, [1, 2])

    def test_sorted_entry_has_no_sorter_in_its_source_dependencies(self):
        compilation = compile_project("kruskal_sorted", root=PROJECT)
        self.assertEqual(set(compilation.project.modules), {"union_find", "kruskal_sorted"})

    def test_repeated_calls_preserve_inputs_and_prior_output(self):
        environment, clocks = trusted_environment("kruskal_sorted", self.initial_clocks)
        sources, targets, weights, order = map(sequence, ([0, 1, 0], [1, 2, 2], [7, -3, 2], [1, 2, 0]))
        arguments = (3, sources, targets, weights, 3, order)
        first = environment["kruskal_sorted"](*arguments)
        saved = dict(first._values)
        second = environment["kruskal_sorted"](*arguments)
        self.assertIsNot(first, second)
        self.assertEqual(first._values, saved)
        self.assertEqual([second[index] for index in range(3)], [0, 1, 1])
        second[0] = 77
        self.assertEqual(first._values, saved)
        self.assertEqual([order[index] for index in range(3)], [1, 2, 0])
        for name in ("sort_steps", "heap_comparisons", "heap_swaps"):
            self.assertEqual(clocks[name], self.initial_clocks[name])
        self.assertEqual(clocks["kruskal"] - self.initial_clocks["kruskal"], 8)
        self.assertEqual(clocks["caller_work"], self.initial_clocks["caller_work"])


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ConcreteKruskalLeanTests(unittest.TestCase):
    def test_keyed_sort_analysis(self):
        compilation = compile_project("sort_indices", root=PROJECT)
        result = check_project(compilation, analysis_module="Algo.sort_indices.Analysis", timeout=300)
        self.assertTrue(result.ok, result.output)

    def test_complete_kruskal_analysis(self):
        bundle = load_example_project("kruskal")
        self.assertIn("Algo.kruskal.Analysis", bundle["analyses"])
        with tempfile.TemporaryDirectory() as directory:
            compilation = compile_project(bundle["entry"], root=directory, sources=bundle["sources"])
            result = check_project(compilation, proof_sources=bundle["analyses"],
                                   analysis_module="Algo.kruskal.Analysis", timeout=300)
        self.assertTrue(result.ok, result.output)
        self.assertNotIn("declaration uses `sorry`", result.output)

    def test_sorted_kruskal_analysis(self):
        compilation = compile_project("kruskal_sorted", root=PROJECT)
        result = check_project(compilation, analysis_module="Algo.kruskal_sorted.Analysis", timeout=300)
        self.assertTrue(result.ok, result.output)
        self.assertNotIn("declaration uses `sorry`", result.output)

    def test_two_calls_reuse_the_contract_and_preserve_the_first_output(self):
        compilation = compile_project("kruskal", root=PROJECT)
        analysis = (ROOT / "tests/proofs/kruskal_reuse.lean").read_text()
        result = check_project(compilation, analysis=analysis,
                               analysis_module="Algo.KruskalReuse", timeout=300)
        self.assertTrue(result.ok, result.output)
        self.assertNotIn("declaration uses `sorry`", result.output)


if __name__ == "__main__":
    unittest.main()
