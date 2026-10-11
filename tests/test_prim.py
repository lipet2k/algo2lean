"""Prim's actual example source is checked against exhaustive finite MSTs.

The execution adapter loads only a fixed graph of repository-owned examples.
The independent oracle enumerates spanning trees, without sharing Prim's queue
logic or greedy selection rule. Lean separately checks the generated semantics.
"""

import __future__
import ast
from functools import lru_cache
from pathlib import Path
import random
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from tests.test_examples import IndexedSequence
from tests.test_kruskal_algorithms import components, exhaustive_minimum_forest


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"
ENTRY = "prim.prim_fibonacci"
TRUSTED_IMPORTS = {
    "prim.graph": {},
    "fibonacci_heap": {},
    "dijkstra.priority_queue": {"algo2lean": frozenset({"Interface"})},
    "prim.prim": {
        "prim.graph": frozenset({"Graph", "Edge"}),
        "dijkstra.priority_queue": frozenset({"PriorityQueue"}),
    },
    ENTRY: {
        "prim.graph": frozenset({"Graph"}),
        "fibonacci_heap": frozenset({"FibonacciHeap"}),
        "prim.prim": frozenset({"prim"}),
    },
}


@lru_cache(maxsize=1)
def validated_sources():
    """Freeze and compile the exact allowlisted sources used by the tests."""
    sources = {name: EXAMPLES.joinpath(*name.split(".")).with_suffix(".algo").read_text()
               for name in TRUSTED_IMPORTS}
    compiled = compile_project(ENTRY, root=EXAMPLES, sources=sources)
    if set(compiled.modules) != set(TRUSTED_IMPORTS):
        raise ValueError("Prim's trusted source graph changed; review the execution allowlist")
    return sources


def trusted_environment():
    """Resolve only reviewed named imports; never invoke Python import hooks."""
    sources = validated_sources()
    clocks = {"caller_work": 37}
    loaded = {"algo2lean": {"Interface": type("Interface", (), {})}}

    def tick(name, amount=1):
        if not isinstance(name, str) or type(amount) is not int or amount < 0:
            raise ValueError("Invalid tick in trusted example")
        clocks[name] = clocks.get(name, 0) + amount

    def load(name):
        if name in loaded:
            return loaded[name]
        if name not in TRUSTED_IMPORTS:
            raise ValueError("Untrusted example import: " + name)
        path = EXAMPLES.joinpath(*name.split(".")).with_suffix(".algo")
        tree = ast.parse(sources[name], filename=str(path))
        environment = {
            "__builtins__": {"__build_class__": __build_class__},
            "__name__": "trusted_prim_" + name.replace(".", "_"),
            "Int": int, "Bool": bool, "Seq": IndexedSequence,
            "const": lambda value: IndexedSequence(lambda _index: value),
            "tick": tick,
        }
        imports, body = [], []
        for statement in tree.body:
            if isinstance(statement, ast.ImportFrom):
                allowed = TRUSTED_IMPORTS[name].get(statement.module)
                if statement.level or allowed is None:
                    raise ValueError("Unexpected import in trusted Prim source")
                dependency = load(statement.module)
                for imported in statement.names:
                    if imported.name not in allowed:
                        raise ValueError("Unexpected export in trusted Prim source")
                    environment[imported.asname or imported.name] = dependency[imported.name]
                imports.append(statement)
            elif isinstance(statement, ast.Import):
                raise ValueError("Only reviewed named imports are supported")
            else:
                body.append(statement)
        if any(isinstance(node, (ast.Import, ast.ImportFrom)) and node not in imports
               for node in ast.walk(tree)):
            raise ValueError("Nested imports are outside the trusted example graph")
        tree.body = body
        exec(compile(tree, str(path), "exec", flags=__future__.annotations.compiler_flag,
                     dont_inherit=True), environment)
        loaded[name] = environment
        return environment

    return load(ENTRY), clocks


class PrimBehaviorTests(unittest.TestCase):
    def check_graph(self, size, edges, root):
        environment, clocks = trusted_environment()
        graph = environment["Graph"](size)
        for source, target, weight in edges:
            self.assertTrue(graph.add_edge(source, target, weight))
        heads = [graph.heads[vertex] for vertex in range(size)]
        saved = []
        for first in heads:
            edge = first
            while edge is not None:
                saved.append((edge, edge.target, edge.weight, edge.next))
                edge = edge.next

        parent = environment["prim_fibonacci"](graph, root)
        self.assertEqual(parent[root], -1)
        selected, output_weight = [], 0
        for vertex in range(size):
            if vertex == root:
                continue
            predecessor = parent[vertex]
            self.assertTrue(0 <= predecessor < size)
            self.assertNotEqual(predecessor, vertex)
            candidates = [(weight, index) for index, (source, target, weight) in enumerate(edges)
                          if (source, target) in ((predecessor, vertex), (vertex, predecessor))]
            self.assertTrue(candidates, "Every returned parent must name an actual input edge")
            weight, index = min(candidates)
            selected.append(index)
            output_weight += weight
        partition, edge_count, optimum = exhaustive_minimum_forest(size, edges)
        self.assertEqual(len(partition), 1, "This test's MST inputs must be connected")
        self.assertEqual(len(set(selected)), edge_count)
        self.assertEqual(components(size, edges, selected), partition)
        self.assertEqual(output_weight, optimum, "The returned tree must attain the global minimum")

        self.assertEqual([graph.heads[vertex] for vertex in range(size)], heads)
        for edge, target, weight, following in saved:
            self.assertEqual((edge.target, edge.weight, edge.next), (target, weight, following))
        for index in (-100, -1, size, size + 17):
            self.assertEqual(parent[index], -1)
        self.assertEqual(clocks["caller_work"], 37)
        self.assertEqual(clocks.get("settlements", 0), size)
        self.assertEqual(clocks.get("queue_pops", 0), size)
        self.assertEqual(clocks.get("queue_empty_checks", 0), size + 1)
        adjacency_entries = 2 * len(edges)
        self.assertEqual(clocks.get("edges", 0), adjacency_entries)
        self.assertLessEqual(clocks.get("improvements", 0), adjacency_entries)
        self.assertEqual(clocks.get("queue_updates", 0), clocks.get("improvements", 0) + 1)
        runtime = sum(amount for name, amount in clocks.items() if name != "caller_work")
        bound = 23 * (adjacency_entries + 1) + (12 * (2 * (size.bit_length() - 1) + 2) + 3) * size
        self.assertLessEqual(runtime, bound)

    def test_signed_tied_parallel_looped_and_large_weights(self):
        cases = [
            (1, [], 0),
            (1, [(0, 0, -100), (0, 0, 7)], 0),
            (2, [(0, 1, 8), (0, 1, -3), (1, 0, -3), (0, 0, -100)], 1),
            (4, [(0, 1, 1), (1, 2, 1), (2, 3, 1), (3, 0, 1),
                 (0, 2, 1), (1, 3, 1)], 2),
            (4, [(0, 1, -5), (1, 2, 0), (2, 3, 9), (0, 3, 3), (1, 3, -2)], 3),
            (3, [(0, 1, 10**80), (1, 2, -(10**100)), (0, 2, -(10**100) - 1)], 1),
        ]
        for size, edges, root in cases:
            with self.subTest(size=size, edges=edges, root=root):
                self.check_graph(size, edges, root)

    def test_seeded_connected_graphs_against_exhaustive_minimum(self):
        rng = random.Random(2026101017)
        for case in range(48):
            size = rng.randrange(1, 7)
            # The first edges form a tree, ensuring the MST precondition holds.
            edges = [(vertex, rng.randrange(vertex), rng.randrange(-9, 10))
                     for vertex in range(1, size)]
            edges += [(rng.randrange(size), rng.randrange(size), rng.randrange(-9, 10))
                      for _ in range(rng.randrange(0, 6))]
            root = rng.randrange(size)
            with self.subTest(case=case, size=size, root=root):
                self.check_graph(size, edges, root)

    def test_invalid_roots_return_fresh_minus_one_sequences_without_ticks(self):
        for size, root in ((0, 0), (3, -1), (3, 3), (3, 10**80)):
            with self.subTest(size=size, root=root):
                environment, clocks = trusted_environment()
                graph = environment["Graph"](size)
                first = environment["prim_fibonacci"](graph, root)
                second = environment["prim_fibonacci"](graph, root)
                self.assertIsNot(first, second)
                for index in (-13, -1, 0, 2, size, root, root + 1):
                    self.assertEqual(first[index], -1)
                    self.assertEqual(second[index], -1)
                first[0] = 99
                self.assertEqual(second[0], -1)
                self.assertEqual(clocks, {"caller_work": 37})

    def test_graph_builder_preserves_signed_weights_and_rejects_invalid_endpoints(self):
        environment, _clocks = trusted_environment()
        graph = environment["Graph"](3)
        for source, target in ((-1, 0), (0, -1), (3, 0), (0, 3)):
            self.assertFalse(graph.add_edge(source, target, -17))
        self.assertTrue(all(graph.heads[vertex] is None for vertex in range(3)))
        self.assertTrue(graph.add_edge(0, 1, -17))
        self.assertEqual((graph.heads[0].target, graph.heads[0].weight), (1, -17))
        self.assertEqual((graph.heads[1].target, graph.heads[1].weight), (0, -17))
        self.assertEqual(environment["Graph"](-10).size, 0)


class PrimCompilationTests(unittest.TestCase):
    def test_generic_algorithm_has_no_heap_implementation(self):
        generic = compile_project("prim.prim", root=EXAMPLES)
        self.assertEqual(set(generic.modules), {"prim.prim", "prim.graph", "dijkstra.priority_queue"})
        concrete = compile_project(ENTRY, root=EXAMPLES)
        self.assertEqual(concrete.modules["prim.prim"].lean, generic.entry.lean)
        existing_heap = compile_project("fibonacci_heap", root=EXAMPLES)
        self.assertEqual(concrete.modules["fibonacci_heap"].lean, existing_heap.entry.lean)
        self.assertEqual(concrete.modules["fibonacci_heap"].facts_lean, existing_heap.entry.facts_lean)

    def test_line_labels_leave_algorithm_definitions_unchanged(self):
        source = (EXAMPLES / "prim/prim.algo").read_text()
        original = compile_project("prim.prim", root=EXAMPLES)
        renamed_source = source.replace("# @extract", "# @choose_vertex")
        self.assertNotEqual(source, renamed_source)
        renamed = compile_project("prim.prim", root=EXAMPLES, sources={"prim.prim": renamed_source})
        self.assertEqual(original.entry.lean, renamed.entry.lean)
        self.assertEqual(original.entry.facts_lean, renamed.entry.facts_lean)
        self.assertNotEqual(original.entry.points_lean, renamed.entry.points_lean)

    def test_source_contains_the_extraction_and_adjacency_loops(self):
        tree = ast.parse((EXAMPLES / "prim/prim.algo").read_text())
        functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
        self.assertEqual(set(functions), {"scan_edges", "prim"})
        for function in functions.values():
            self.assertTrue(any(isinstance(node, ast.While) for node in function.body))


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class PrimLeanTests(unittest.TestCase):
    def test_complete_analysis_and_standard_axioms(self):
        compiled = compile_project(ENTRY, root=EXAMPLES)
        audit = """import Algo.prim.prim_fibonacci.Analysis
#print axioms FibonacciPrimAnalysis.summary
#print axioms FibonacciPrimAnalysis.correctness_and_running_time
#print axioms FibonacciPrimAnalysis.invalid_root_output
#print axioms Algo2Lean.Prim.Invariant.finish
#print axioms Algo2Lean.Prim.Safe.add_light
"""
        checked = check_project(compiled, analysis=audit, analysis_module="PrimAxiomAudit", timeout=300)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)
        lines = [line for line in checked.output.splitlines() if "depends on axioms" in line]
        self.assertEqual(len(lines), 5, checked.output)
        for line in lines:
            axioms = line.split("[", 1)[1].rstrip("]").replace(" ", "").split(",")
            self.assertLessEqual(set(axioms), {"propext", "Classical.choice", "Quot.sound"})


if __name__ == "__main__":
    unittest.main()
