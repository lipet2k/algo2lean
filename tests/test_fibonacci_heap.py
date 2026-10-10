"""Execute the fixed Fibonacci examples and compare against independent models.

These tests complement Lean proofs: random runs check the actual pointer rings,
marks, degrees, Fibonacci subtree bound, and Dijkstra's graph-level behavior.
"""

import __future__
import ast
import builtins
from pathlib import Path
import random
import unittest

from algo2lean.compiler import compile_source
from tests.test_dijkstra import bellman_ford
from tests.test_examples import IndexedSequence


ROOT = Path(__file__).resolve().parents[1]


def load_fibonacci_example(name):
    if name not in {"fibonacci_heap", "dijkstra_fibonacci"}:
        raise ValueError("Only these fixed repository examples can be executed")
    path = ROOT / "examples" / (name + ".algo")
    source = path.read_text()
    compile_source(source, filename=path.name)
    costs = {}
    allocations = []

    def const(value):
        sequence = IndexedSequence(lambda _index: value)
        allocations.append(sequence)
        return sequence

    def tick(clock, amount=1):
        if not isinstance(clock, str) or type(amount) is not int or amount < 0:
            raise ValueError("Invalid clock increment")
        costs[clock] = costs.get(clock, 0) + amount

    environment = {
        "__builtins__": {"__build_class__": builtins.__build_class__},
        "__name__": "trusted_example_" + name,
        "Int": int, "Bool": bool, "Seq": IndexedSequence,
        "const": const, "allocations": allocations,
        "tick": tick,
    }
    exec(compile(source, str(path), "exec", flags=__future__.annotations.compiler_flag,
                 dont_inherit=True), environment, environment)
    return environment, costs


def source_declaration(name, declaration):
    tree = ast.parse((ROOT / "examples" / (name + ".algo")).read_text())
    return next(node for node in tree.body if isinstance(node, (ast.ClassDef, ast.FunctionDef))
                and node.name == declaration)


class FibonacciHeapTests(unittest.TestCase):
    def ring(self, heap, first):
        if first < 0:
            return []
        nodes = []
        node = first
        while node not in nodes:
            self.assertGreaterEqual(node, 0)
            self.assertEqual(heap.present[node], 1)
            self.assertEqual(heap.right[heap.left[node]], node)
            self.assertEqual(heap.left[heap.right[node]], node)
            nodes.append(node)
            self.assertLessEqual(len(nodes), heap.size)
            node = heap.right[node]
        self.assertEqual(node, first)
        return nodes

    def assert_heap(self, heap, expected):
        self.assertEqual(heap.size, len(expected))
        self.assertTrue(all(value == -1 for value in heap.table._values.values()))
        self.assertEqual(heap.table[-1], -1)
        roots = self.ring(heap, heap.minimum)
        if not expected:
            self.assertEqual(heap.minimum, -1)
        else:
            self.assertEqual(heap.keys[heap.minimum], min(expected.values()))
        visited = set()

        def visit(node, parent):
            self.assertNotIn(node, visited)
            visited.add(node)
            self.assertEqual(heap.parents[node], parent)
            self.assertEqual(heap.keys[node], expected[node])
            self.assertIn(heap.marks[node], (0, 1))
            if parent < 0:
                self.assertEqual(heap.marks[node], 0)
            else:
                self.assertLessEqual(heap.keys[parent], heap.keys[node])
            children = self.ring(heap, heap.children[node])
            self.assertEqual(heap.degrees[node], len(children))
            size = 1 + sum(visit(child, node) for child in children)
            # A degree-d Fibonacci node has at least F_(d+2) descendants
            # including itself; calculate the threshold using integers only.
            a, b = 0, 1
            for _ in range(heap.degrees[node] + 2):
                a, b = b, a + b
            self.assertGreaterEqual(size, a)
            return size

        for root in roots:
            visit(root, -1)
        self.assertEqual(visited, set(expected))
        self.assertEqual({vertex for vertex in expected if heap.present[vertex]}, set(expected))

    def test_shared_source_and_unchanged_graph_algorithm(self):
        self.assertEqual(ast.dump(source_declaration("fibonacci_heap", "FibonacciHeap")),
                         ast.dump(source_declaration("dijkstra_fibonacci", "FibonacciHeap")))
        for declaration in ("Edge", "Graph"):
            self.assertEqual(ast.dump(source_declaration("dijkstra", declaration)),
                             ast.dump(source_declaration("dijkstra_fibonacci", declaration)))
        original = source_declaration("dijkstra", "dijkstra")
        replacement = source_declaration("dijkstra_fibonacci", "dijkstra")
        for node in ast.walk(replacement):
            if isinstance(node, ast.Name) and node.id == "FibonacciHeap":
                node.id = "MinHeap"
        self.assertEqual(ast.dump(original), ast.dump(replacement))

    def test_random_updates_extracts_and_full_forest_invariants(self):
        environment, costs = load_fibonacci_example("fibonacci_heap")
        heap = environment["FibonacciHeap"]()
        expected = {}
        rng = random.Random(20261010)
        for _ in range(2400):
            if rng.randrange(4) or not expected:
                vertex, key = rng.randrange(120), rng.randrange(-10000, 10001)
                heap.push_or_decrease(vertex, key)
                expected[vertex] = min(expected.get(vertex, key), key)
            else:
                minimum = min(expected.values())
                vertex = heap.pop_min()
                self.assertEqual(expected.pop(vertex), minimum)
                self.assertEqual(heap.present[vertex], 0)
                self.assertEqual(heap.parents[vertex], -1)
            self.assert_heap(heap, expected)
            for vertex in range(120):
                self.assertEqual(heap.present[vertex], int(vertex in expected))
        while expected:
            minimum = min(expected.values())
            self.assertEqual(expected.pop(heap.pop_min()), minimum)
            self.assert_heap(heap, expected)
        self.assertEqual(heap.pop_min(), -1)
        self.assertEqual(heap.pop_min(), -1)
        # All mutable storage is allocated once in the constructor. In
        # particular, repeated extracts reuse and clear the degree table.
        self.assertEqual(len(environment["allocations"]), 9)
        for clock in ("heap_comparisons", "heap_links", "heap_cuts", "heap_root_scans",
                      "heap_degree_scans", "heap_promotions"):
            self.assertGreater(costs[clock], 0)

    def test_cascading_cut_clears_two_marked_ancestors(self):
        environment, costs = load_fibonacci_example("fibonacci_heap")
        heap = environment["FibonacciHeap"]()
        expected = {vertex: 1000 + vertex for vertex in range(257)}
        for vertex, key in expected.items():
            heap.push_or_decrease(vertex, key)
        self.assertEqual(heap.pop_min(), 0)
        del expected[0]
        self.assert_heap(heap, expected)
        # Find two nonroot ancestors in the binomial tree created by the first
        # consolidation. Mark each by cutting another child, then trigger both.
        child_parent = next(vertex for vertex in expected
                            if heap.degrees[vertex] >= 2 and heap.parents[vertex] >= 0
                            and heap.parents[heap.parents[vertex]] >= 0)
        parent = heap.parents[child_parent]
        sibling = next(child for child in self.ring(heap, heap.children[parent])
                       if child != child_parent)
        children = self.ring(heap, heap.children[child_parent])
        heap.push_or_decrease(sibling, -10)
        expected[sibling] = -10
        self.assertEqual(heap.marks[parent], 1)
        heap.push_or_decrease(children[0], -20)
        expected[children[0]] = -20
        self.assertEqual(heap.marks[child_parent], 1)
        before = costs.get("heap_cuts", 0)
        heap.push_or_decrease(children[1], -30)
        expected[children[1]] = -30
        self.assertEqual(costs["heap_cuts"] - before, 3)
        for node in (children[1], child_parent, parent):
            self.assertEqual(heap.parents[node], -1)
            self.assertEqual(heap.marks[node], 0)
        self.assert_heap(heap, expected)

    def test_empty_singleton_reinsertion_and_non_decreasing_updates(self):
        environment, costs = load_fibonacci_example("fibonacci_heap")
        heap = environment["FibonacciHeap"]()
        self.assertEqual(heap.pop_min(), -1)
        for key in (10 ** 100, -10 ** 100, 0):
            heap.push_or_decrease(10 ** 100, key)
            heap.push_or_decrease(10 ** 100, key + 1)
            heap.push_or_decrease(10 ** 100, key)
            self.assert_heap(heap, {10 ** 100: key})
            self.assertEqual(heap.pop_min(), 10 ** 100)
            self.assert_heap(heap, {})
        self.assertEqual(costs.get("heap_degree_scans", 0), 0)


class FibonacciDijkstraTests(unittest.TestCase):
    def check_graph(self, n, edges, source):
        environment, costs = load_fibonacci_example("dijkstra_fibonacci")
        graph = environment["Graph"](n)
        for u, v, weight in edges:
            self.assertTrue(graph.add_edge(u, v, weight))
        heads = [graph.heads[i] for i in range(n)]
        snapshot = []
        for head in heads:
            edge = head
            while edge is not None:
                snapshot.append((edge, edge.target, edge.weight, edge.next))
                edge = edge.next
        result = environment["dijkstra"](graph, source)
        expected = bellman_ford(n, edges, source)
        self.assertEqual([result[i] for i in range(n)], expected)
        self.assertEqual([graph.heads[i] for i in range(n)], heads)
        for edge, target, weight, following in snapshot:
            self.assertEqual((edge.target, edge.weight, edge.next), (target, weight, following))
        self.assertEqual(result[-1], -1)
        self.assertEqual(result[n + 100], -1)
        reachable = sum(value >= 0 for value in expected)
        visited_edges = sum(expected[u] >= 0 for u, _, _ in edges)
        self.assertEqual(costs.get("settlements", 0), reachable)
        self.assertEqual(costs.get("edges", 0), visited_edges)
        self.assertLessEqual(costs.get("improvements", 0), visited_edges)
        updates = costs.get("improvements", 0) + int(reachable > 0)
        self.assertEqual(costs.get("heap_operations", 0), reachable + updates)
        # Check a conservative E + V log V envelope on actual events. The
        # separate Lean statements explain the amortization assumptions.
        heap_work = sum(value for clock, value in costs.items() if clock.startswith("heap_"))
        self.assertLessEqual(heap_work, 20 * (updates + reachable * max(1, n.bit_length())))

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
        rng = random.Random(99102027)
        for case in range(90):
            n = rng.randrange(1, 25)
            edges = [(u, v, rng.randrange(30)) for u in range(n) for v in range(n)
                     if rng.randrange(5) == 0]
            with self.subTest(case=case, n=n):
                self.check_graph(n, edges, rng.randrange(n))

    def test_graph_builder_rejects_invalid_edges(self):
        environment, _ = load_fibonacci_example("dijkstra_fibonacci")
        graph = environment["Graph"](3)
        for u, v, weight in [(-1, 0, 0), (0, -1, 0), (3, 0, 0), (0, 3, 0), (0, 1, -1)]:
            self.assertFalse(graph.add_edge(u, v, weight))
        self.assertTrue(all(graph.heads[i] is None for i in range(3)))
        self.assertEqual(environment["Graph"](-10).size, 0)
