"""The generic Dijkstra proof checks independently of every queue backend."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"
MODULE = "composable_dijkstra.dijkstra"


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ComposableDijkstraTests(unittest.TestCase):
    def test_generic_correctness_and_actual_clock_bounds(self):
        compiled = compile_project(MODULE, root=EXAMPLES)
        self.assertEqual(set(compiled.modules),
                         {"graph", "composable_dijkstra.priority_queue", MODULE})
        checked = check_project(compiled, analysis_module="Algo." + MODULE + ".Analysis")
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)
        proof = (EXAMPLES / "analysis/composable_dijkstra/dijkstra.lean").read_text()
        self.assertIn("Algo2Lean.Dijkstra.Execution.run", proof)
        self.assertIn("theorem every_execution", proof)
        self.assertNotIn("Fibonacci", proof)
        self.assertNotIn("indexed_heap", proof)

    def test_extra_extraction_charge_invalidates_the_existing_bound(self):
        source = (EXAMPLES / "composable_dijkstra/dijkstra.algo").read_text()
        changed = source.replace('tick("queue_pops")', 'tick("queue_pops", 2)')
        self.assertNotEqual(source, changed)
        compiled = compile_project(MODULE, root=EXAMPLES, sources={MODULE: changed})
        checked = check_project(compiled, analysis_module="Algo." + MODULE + ".Analysis")
        self.assertFalse(checked.ok)
        self.assertIn("Algo/composable_dijkstra/dijkstra/Analysis.lean:", checked.output)

    def test_label_changes_keep_generic_definitions_and_proof_reusable(self):
        source = (EXAMPLES / "composable_dijkstra/dijkstra.algo").read_text()
        original = compile_project(MODULE, root=EXAMPLES)
        renamed = compile_project(MODULE, root=EXAMPLES,
            sources={MODULE: source.replace("# @extract", "# @next_vertex")})
        self.assertEqual(original.entry.lean, renamed.entry.lean)
        self.assertEqual(original.entry.facts_lean, renamed.entry.facts_lean)
        self.assertNotEqual(original.entry.points_lean, renamed.entry.points_lean)
        checked = check_project(renamed, analysis_module="Algo." + MODULE + ".Analysis")
        self.assertTrue(checked.ok, checked.output)

    def test_both_concrete_wrappers_reuse_the_same_generic_proof(self):
        generic = compile_project(MODULE, root=EXAMPLES)
        for backend in ("fibonacci", "binary"):
            with self.subTest(backend=backend):
                name = "composable_dijkstra.dijkstra_" + backend
                compiled = compile_project(name, root=EXAMPLES)
                self.assertEqual(compiled.modules[MODULE].lean, generic.entry.lean)
                self.assertEqual(compiled.modules[MODULE].facts_lean, generic.entry.facts_lean)
                checked = check_project(compiled, analysis_module="Algo." + name + ".Analysis")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("declaration uses `sorry`", checked.output)

    def test_concrete_public_theorems_have_only_standard_lean_axioms(self):
        for backend in ("fibonacci", "binary"):
            with self.subTest(backend=backend):
                name = "composable_dijkstra.dijkstra_" + backend
                namespace = backend.title() + "DijkstraAnalysis"
                compiled = compile_project(name, root=EXAMPLES)
                audit = "import Algo." + name + ".Analysis\n" + "\n".join(
                    "#print axioms " + namespace + "." + theorem
                    for theorem in ("summary", "every_execution", "output_exists",
                                    "output_with_cost_correct", "terminates", "invalid_source_output"))
                checked = check_project(compiled, analysis=audit, analysis_module="DijkstraAxiomAudit")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("sorryAx", checked.output)
                self.assertNotIn("Lean.ofReduceBool", checked.output)
                self.assertNotIn("Lean.trustCompiler", checked.output)
                lines = [line for line in checked.output.splitlines() if "depends on axioms" in line]
                self.assertEqual(len(lines), 6, checked.output)
                for line in lines:
                    axioms = line.split("[", 1)[1].rstrip("]").replace(" ", "").split(",")
                    self.assertLessEqual(set(axioms), {"propext", "Classical.choice", "Quot.sound"})

    def test_returned_sequence_is_reused_by_a_further_compiled_caller(self):
        reader = "def read_at(values: Seq, vertex: Int) -> Int:\n    return values[vertex]\n"
        for backend in ("fibonacci", "binary"):
            with self.subTest(backend=backend):
                function = "dijkstra_" + backend
                namespace = backend.title() + "DijkstraAnalysis"
                caller = f"""from graph import Graph
from composable_dijkstra.{function} import {function} as search
from follow_reader import read_at

def lookup(graph: Graph, source: Int, vertex: Int) -> Int:
    distance = search(graph, source)
    return read_at(distance, vertex)
"""
                proof = f"""import Algo.follow_client.Generated
import Algo.composable_dijkstra.{function}.Analysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.graph.Algo2LeanGenerated ComposableDijkstraAnalysis

namespace LaterDijkstraCaller

theorem reader_summary (heap : Heap) (ref : SeqRef) (vertex : Int) (allocated : ref < heap.nextRef) :
    Algo.follow_reader.read_at.Call heap (ref,vertex) heap (heap.read ref vertex) := by
  open Algo.follow_reader.Algo2LeanGenerated in
    refine ⟨allocated,?_⟩
    intro caller
    apply Reaches.prepend (Step.read_at_pc2 _ _ caller allocated)
    exact Reaches.single (Step.read_at_pc1 _ _ caller)

example (heap : Heap) (graph : Ref_Graph) (size source vertex : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (represented : GraphRep heap graph size heads adjacency)
    (lower : 0 ≤ source) (upper : source < size) :
    ∃ after, Algo.follow_client.lookup.Call heap (graph,source,vertex) after
        (after.read heap.nextRef vertex) ∧
      ShortestDistances (representedEdges size adjacency) source (after.read heap.nextRef) ∧
      {namespace}.clockWork (Heap.cost heap after) ≤ {namespace}.runtimeBound size adjacency ∧
      heap.Footprint after [] [] [] := by
  obtain ⟨after,search,_,correct,_,bound,allocated,preserved⟩ := {namespace}.summary heap graph size source
    heads adjacency represented lower upper
  have read := reader_summary after heap.nextRef vertex allocated
  refine ⟨after,⟨represented.valid,?_⟩,correct,bound,preserved⟩
  open Algo.follow_client.Algo2LeanGenerated in
    intro caller
    apply Reaches.prepend (Step.lookup_pc8 _ _ caller)
    apply Reaches.prepend (Step.lookup_pc7 _ _ caller)
    apply Reaches.prepend (Step.lookup_pc6 _ _ caller)
    apply (ModuleCall.summary import_4_simulates _ caller search.2).trans
    apply Reaches.prepend (Step.lookup_pc5 _ _ caller)
    apply Reaches.prepend (Step.lookup_pc4 _ _ caller)
    apply Reaches.prepend (Step.lookup_pc3 _ _ caller)
    apply Reaches.prepend (Step.lookup_pc2 _ _ caller)
    apply (ModuleCall.summary import_5_simulates _ caller read.2).trans
    exact Reaches.single (Step.lookup_pc1 _ _ caller)

end LaterDijkstraCaller
"""
                compiled = compile_project("follow_client", root=EXAMPLES,
                    sources={"follow_client": caller, "follow_reader": reader})
                checked = check_project(compiled, analysis=proof, analysis_module="LaterCallerProof")
                self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
