"""Both existing heaps expose independent reusable priority-queue packages."""

import ast
import copy
from pathlib import Path
import shutil
import unittest

from algo2lean.compiler import Lowerer
from algo2lean.embedding import _fingerprint
from algo2lean.frontend import parse_program
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from tests.test_fibonacci_heap import load_fibonacci_example
from tests.test_dijkstra import load_example


ROOT = Path(__file__).resolve().parents[1]
HEAPS = (
    ("fibonacci_heap", "FibonacciHeap", load_fibonacci_example),
    ("dijkstra_fibonacci", "FibonacciHeap", load_fibonacci_example),
    ("indexed_heap", "MinHeap", load_example),
    ("dijkstra", "MinHeap", load_example),
)
PACKAGES = (("fibonacci", "fibonacci_heap", "FibonacciQueueAnalysis"),
            ("binary", "indexed_heap", "BinaryQueueAnalysis"))


class ComposableHeapTests(unittest.TestCase):
    def test_empty_query_preserves_data_allocations_and_clocks(self):
        for name, heap_class, loader in HEAPS:
            with self.subTest(source=name):
                environment, clocks = loader(name)
                queue = environment[heap_class]()
                for empty in (True, False, True):
                    fields, before = dict(vars(queue)), dict(clocks)
                    allocations = len(environment.get("allocations", []))
                    self.assertEqual(queue.is_empty(), empty)
                    self.assertEqual(vars(queue), fields)
                    self.assertEqual(clocks, before)
                    self.assertEqual(len(environment.get("allocations", [])), allocations)
                    if empty:
                        queue.push_or_decrease(7, -3)
                    else:
                        self.assertEqual(queue.pop_min(), 7)

    def test_appending_empty_query_preserves_every_existing_lowered_function(self):
        for name, heap_class, loader in HEAPS:
            with self.subTest(source=name):
                current = ast.parse((ROOT / "examples" / (name + ".algo")).read_text())
                before = copy.deepcopy(current)
                heap = next(node for node in before.body if isinstance(node, ast.ClassDef)
                            and node.name == heap_class)
                heap.body = [node for node in heap.body if not isinstance(node, ast.FunctionDef)
                             or node.name != "is_empty"]
                earlier, _ = parse_program(before)
                later, _ = parse_program(current)
                self.assertEqual(set(later) - set(earlier), {heap_class + "_is_empty"})
                for function in earlier:
                    self.assertEqual(_fingerprint(Lowerer(earlier[function])),
                                     _fingerprint(Lowerer(later[function])), function)

    def test_editor_reexports_reuse_the_original_heap_module(self):
        for package, source, _ in PACKAGES:
            with self.subTest(package=package):
                original = compile_project(source, root=ROOT / "examples")
                reexport = compile_project("composable_dijkstra." + package,
                                           root=ROOT / "examples")
                self.assertEqual(set(reexport.modules), {source, "composable_dijkstra." + package})
                self.assertEqual(reexport.modules[source].lean, original.entry.lean)
                self.assertEqual(reexport.modules[source].points_lean, original.entry.points_lean)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_complete_migrated_proofs_are_reusable_by_canonical_import(self):
        for package, _, _ in PACKAGES:
            with self.subTest(package=package):
                compiled = compile_project("composable_dijkstra." + package, root=ROOT / "examples")
                checked = check_project(compiled,
                    analysis_module="Algo.composable_dijkstra." + package + ".Analysis")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("warning", checked.output)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_queue_contracts_check_without_a_client_or_extra_axioms(self):
        for package, source, namespace in PACKAGES:
            with self.subTest(package=package):
                compiled = compile_project(source, root=ROOT / "examples")
                analysis = (f"import Algo.composable_dijkstra.{package}_queue.Analysis\n"
                            f"#print axioms {namespace}.contracts\n"
                            f"#print axioms {namespace}.constructor_rep\n")
                checked = check_project(compiled, analysis=analysis)
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("warning", checked.output)
                self.assertNotIn("sorryAx", checked.output)
                self.assertIn(namespace + ".contracts", checked.output)
                for line in checked.output.splitlines():
                    if "depends on axioms:" in line:
                        axioms = line.split("depends on axioms:", 1)[1].strip(" []")
                        self.assertLessEqual(set(axioms.split(", ")),
                                             {"propext", "Classical.choice", "Quot.sound"})


if __name__ == "__main__":
    unittest.main()
