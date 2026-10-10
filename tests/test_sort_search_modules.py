"""A bounded sort/search composition reuses correctness and runtime proofs."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples/modules"


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class SortSearchModuleTests(unittest.TestCase):
    def test_each_component_and_the_composition_check_independently(self):
        combined = compile_project("sorted_search_three", root=EXAMPLES)
        for name in ("compare_exchange", "sort_three", "lower_bound_three", "sorted_search_three"):
            with self.subTest(module=name):
                independent = compile_project(name, root=EXAMPLES)
                self.assertEqual(independent.entry.lean, combined.modules[name].lean)
                checked = check_project(independent, analysis_module="Algo." + name + ".Analysis")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("declaration uses 'sorry'", checked.output)

    def test_negative_indices_duplicates_and_absent_keys(self):
        compiled = compile_project("sorted_search_three", root=EXAMPLES)
        proof = """import Algo.sorted_search_three.Analysis
open Algo2LeanGenerated Algo.sorted_search_three
open SortedSearchThreeAnalysis

def data : Heap := ({} : Heap).allocate
  (fun index => if index = -4 then 7 else if index = -3 then -2 else if index = -2 then -2 else 99)

example : ∃ after, sorted_search_three.Run data (0, -4, -2) after (-4) := by
  have execution := (summary data 0 (-4) (-2) (by decide)).run
  have answer : LowerBoundThreeAnalysis.position (SortThreeAnalysis.sortedHeap data 0 (-4)) 0 (-4) (-2) = -4 := by decide
  rw [answer] at execution
  exact ⟨_, execution⟩

example : ∃ after, sorted_search_three.Run data (0, -4, 7) after (-2) := by
  have execution := (summary data 0 (-4) 7 (by decide)).run
  have answer : LowerBoundThreeAnalysis.position (SortThreeAnalysis.sortedHeap data 0 (-4)) 0 (-4) 7 = -2 := by decide
  rw [answer] at execution
  exact ⟨_, execution⟩

example : ∃ after, sorted_search_three.Run data (0, -4, 8) after (-1) := by
  have execution := (summary data 0 (-4) 8 (by decide)).run
  have answer : LowerBoundThreeAnalysis.position (SortThreeAnalysis.sortedHeap data 0 (-4)) 0 (-4) 8 = -1 := by decide
  rw [answer] at execution
  exact ⟨_, execution⟩

example (before after : Heap) (ref : SeqRef) (first key result : Int)
    (execution : sorted_search_three.Run before (ref, first, key) after result) :
    Heap.cost before after "sort_comparisons" = 3 ∧
      Heap.cost before after "search_comparisons" ≤ 3 := by
  have specification := correct execution
  exact ⟨specification.2.2.2.1, specification.2.2.2.2.1⟩
"""
        checked = check_project(compiled, analysis=proof, analysis_module="SortSearchClient")
        self.assertTrue(checked.ok, checked.output)

    def test_a_changed_imported_clock_effect_rejects_the_original_proof(self):
        source = (EXAMPLES / "compare_exchange.algo").read_text(encoding="utf-8")
        changed = source.replace('tick("sort_comparisons")', 'tick("sort_comparisons", 2)')
        compiled = compile_project("sorted_search_three", root=EXAMPLES,
                                   sources={"compare_exchange": changed})
        checked = check_project(compiled, analysis_module="Algo.sorted_search_three.Analysis")
        self.assertFalse(checked.ok)
        self.assertIn("Algo/compare_exchange/Analysis.lean:", checked.output)


if __name__ == "__main__":
    unittest.main()
