"""Finite execution checks complement the separate, incremental Lean proofs.

Only fixed repository examples are executed. Bellman-Ford is the independent
reference; no heap or Dijkstra logic is shared with the expected result.
"""

import __future__
import ast
import builtins
from pathlib import Path
import random
import unittest

from algo2lean.compiler import compile_source
from tests.test_examples import IndexedSequence


ROOT = Path(__file__).resolve().parents[1]


def load_example(name):
    if name not in {"indexed_heap", "dijkstra"}:
        raise ValueError("Only these fixed repository examples can be executed")
    path = ROOT / "examples" / (name + ".algo")
    source = path.read_text()
    compile_source(source, filename=path.name)
    costs = {}

    def tick(clock, amount=1):
        if not isinstance(clock, str) or type(amount) is not int or amount < 0:
            raise ValueError("Invalid clock increment")
        costs[clock] = costs.get(clock, 0) + amount

    environment = {
        "__builtins__": {"__build_class__": builtins.__build_class__},
        "__name__": "trusted_example_" + name,
        "Int": int, "Bool": bool, "Seq": IndexedSequence,
        "const": lambda value: IndexedSequence(lambda _index: value),
        "tick": tick,
    }
    exec(compile(source, str(path), "exec", flags=__future__.annotations.compiler_flag,
                 dont_inherit=True), environment, environment)
    return environment, costs


def bellman_ford(n, edges, source):
    distances = [None] * n
    if not 0 <= source < n:
        return [-1] * n
    distances[source] = 0
    for _ in range(max(0, n - 1)):
        changed = False
        for u, v, weight in edges:
            if distances[u] is not None:
                candidate = distances[u] + weight
                if distances[v] is None or candidate < distances[v]:
                    distances[v] = candidate
                    changed = True
        if not changed:
            break
    return [-1 if value is None else value for value in distances]


class IndexedHeapTests(unittest.TestCase):
    def test_dijkstra_uses_the_same_heap_class(self):
        def heap_class(name):
            tree = ast.parse((ROOT / "examples" / (name + ".algo")).read_text())
            return ast.dump(next(node for node in tree.body
                                 if isinstance(node, ast.ClassDef) and node.name == "MinHeap"))
        self.assertEqual(heap_class("indexed_heap"), heap_class("dijkstra"))

    def test_updates_extracts_inverse_positions_and_heap_order(self):
        environment, costs = load_example("indexed_heap")
        heap = environment["MinHeap"]()
        expected = {}
        rng = random.Random(20261009)
        for _ in range(1500):
            if rng.randrange(4) or not expected:
                vertex, key = rng.randrange(70), rng.randrange(-1000, 1001)
                heap.push_or_decrease(vertex, key)
                expected[vertex] = min(expected.get(vertex, key), key)
            else:
                vertex = heap.pop_min()
                self.assertIn(vertex, expected)
                self.assertEqual(expected[vertex], min(expected.values()))
                del expected[vertex]
            self.assertEqual(heap.size, len(expected))
            self.assertEqual({heap.vertices[i] for i in range(heap.size)}, set(expected))
            for vertex in range(70):
                if vertex in expected:
                    self.assertEqual(heap.vertices[heap.positions[vertex]], vertex)
                    self.assertEqual(heap.keys[vertex], expected[vertex])
                else:
                    self.assertEqual(heap.positions[vertex], -1)
            for i in range(1, heap.size):
                self.assertLessEqual(heap.keys[heap.vertices[(i - 1) // 2]],
                                     heap.keys[heap.vertices[i]])
        while expected:
            vertex = heap.pop_min()
            self.assertEqual(expected.pop(vertex), min([heap.keys[vertex], *expected.values()]))
        self.assertEqual(heap.pop_min(), -1)
        self.assertEqual(heap.pop_min(), -1)
        self.assertGreater(costs["heap_comparisons"], 0)
        self.assertGreater(costs["heap_swaps"], 0)


class DijkstraExamplesTests(unittest.TestCase):
    def check_graph(self, n, edges, source):
        environment, costs = load_example("dijkstra")
        graph = environment["Graph"](n)
        for u, v, weight in edges:
            self.assertTrue(graph.add_edge(u, v, weight))
        heads = [graph.heads[i] for i in range(n)]
        edge_snapshot = []
        for head in heads:
            edge = head
            while edge is not None:
                edge_snapshot.append((edge, edge.target, edge.weight, edge.next))
                edge = edge.next
        result = environment["dijkstra"](graph, source)
        expected = bellman_ford(n, edges, source)
        self.assertEqual([result[i] for i in range(n)], expected)
        self.assertEqual([graph.heads[i] for i in range(n)], heads)
        for edge, target, weight, following in edge_snapshot:
            self.assertEqual((edge.target, edge.weight, edge.next), (target, weight, following))
        self.assertEqual(result[-1], -1)
        self.assertEqual(result[n + 100], -1)
        reachable = sum(value >= 0 for value in expected)
        visited_edges = sum(expected[u] >= 0 for u, _, _ in edges)
        self.assertEqual(costs.get("settlements", 0), reachable)
        self.assertEqual(costs.get("edges", 0), visited_edges)
        self.assertLessEqual(costs.get("improvements", 0), visited_edges)
        # A conservative logarithmic envelope for this instrumented binary heap.
        # General runtime bounds are proved separately in examples/analysis/dijkstra.lean.
        depth = max(1, n.bit_length())
        pushes = (1 if reachable else 0) + costs.get("improvements", 0)
        self.assertLessEqual(costs.get("heap_comparisons", 0),
                             pushes * (depth + 1) + 2 * reachable * depth)
        self.assertLessEqual(costs.get("heap_swaps", 0),
                             pushes * depth + reachable * (depth + 1))

    def test_disconnected_zero_parallel_self_and_large_weights(self):
        for n, edges, source in [
            (0, [], 0), (1, [], 0), (3, [], -1), (3, [], 3),
            (5, [(0, 1, 10), (0, 2, 1), (2, 1, 1), (1, 3, 0), (3, 2, 0)], 0),
            (4, [(0, 0, 0), (0, 1, 8), (0, 1, 2), (1, 2, 0), (2, 1, 0)], 0),
            (4, [(0, 1, 10 ** 100), (1, 2, 10 ** 100), (0, 2, 10 ** 101)], 0),
        ]:
            with self.subTest(n=n, edges=edges, source=source):
                self.check_graph(n, edges, source)

    def test_random_graphs_against_bellman_ford(self):
        rng = random.Random(99102026)
        for case in range(120):
            n = rng.randrange(1, 18)
            edges = [(u, v, rng.randrange(0, 30))
                     for u in range(n) for v in range(n) if rng.randrange(5) == 0]
            source = rng.randrange(n)
            with self.subTest(case=case, n=n, source=source):
                self.check_graph(n, edges, source)

    def test_graph_builder_rejects_invalid_edges(self):
        environment, _ = load_example("dijkstra")
        graph = environment["Graph"](3)
        for u, v, weight in [(-1, 0, 0), (0, -1, 0), (3, 0, 0), (0, 3, 0), (0, 1, -1)]:
            self.assertFalse(graph.add_edge(u, v, weight))
        self.assertTrue(all(graph.heads[i] is None for i in range(3)))
        self.assertEqual(environment["Graph"](-10).size, 0)
