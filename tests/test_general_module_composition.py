"""General finite-interval proofs remain reusable across independent callers."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples/modules"


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class GeneralModuleCompositionTests(unittest.TestCase):
    def test_original_sort_source_and_each_independent_proof_are_preserved(self):
        self.assertEqual((EXAMPLES / "general_merge_sort.algo").read_text(encoding="utf-8"),
                         (ROOT / "examples/merge_sort.algo").read_text(encoding="utf-8"))
        self.assertEqual((EXAMPLES / "general_binary_lower_bound.algo").read_text(encoding="utf-8"),
                         (ROOT / "examples/lower_bound.algo").read_text(encoding="utf-8"))
        combined = compile_project("general_consumer", root=EXAMPLES)
        for name in ("general_merge_sort", "general_binary_lower_bound", "general_sort_then_search", "general_consumer"):
            with self.subTest(module=name):
                independent = compile_project(name, root=EXAMPLES)
                self.assertEqual(independent.entry.lean, combined.modules[name].lean)
                checked = check_project(independent, analysis_module="Algo." + name + ".Analysis", timeout=120)
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("declaration uses `sorry`", checked.output)

    def test_external_consumer_retains_correctness_storage_and_exact_sort_cost(self):
        compiled = compile_project("general_consumer", root=EXAMPLES)
        proof = """import Algo.general_consumer.Analysis
open Algo2LeanGenerated

example (before after : Heap) (source : SeqRef) (lo hi key offset : Int)
    (execution : Algo.general_consumer.insertion_offset.Run
      before (source, lo, hi, key) after offset) :
    0 ≤ offset ∧ offset ≤ ((hi - lo).toNat : Int) ∧
      Heap.cost before after "merge_sort" = GeneralMergeSortAnalysis.runtime (hi - lo).toNat ∧
      (∀ clock, clock ≠ "merge_sort" → after.clocks clock = before.clocks clock) ∧
      (∀ object, object < before.nextRef → after.store object = before.store object) := by
  have specification := GeneralConsumerAnalysis.correct execution
  obtain ⟨ordered, allocated, sorting, partition, preserved, sortCost, otherClocks⟩ := specification.2.2
  exact ⟨specification.1, specification.2.1, sortCost, otherClocks, preserved.2⟩

example (heap : Heap) (source : SeqRef) (lo hi key : Int)
    (valid : source < heap.nextRef) (empty : hi ≤ lo) :
    Algo.general_consumer.insertion_offset.Run heap (source, lo, hi, key)
      (heap.tick "merge_sort") 0 := by
  have sort := GeneralMergeSortAnalysis.base_case_summary heap source lo hi valid (by omega)
  have search := GeneralBinaryLowerBoundAnalysis.empty_summary (heap.tick "merge_sort")
    source lo hi key (by simpa using valid) empty
  have combined := GeneralSortThenSearchAnalysis.compose heap (heap.tick "merge_sort")
    (heap.tick "merge_sort") source source lo hi key lo sort search
  simpa using (GeneralConsumerAnalysis.compose heap (heap.tick "merge_sort")
    source lo hi key lo combined).run
"""
        checked = check_project(compiled, analysis=proof, analysis_module="GeneralExternalClient", timeout=120)
        self.assertTrue(checked.ok, checked.output)

    def test_changed_search_behavior_rejects_the_original_imported_proof(self):
        source = (EXAMPLES / "general_binary_lower_bound.algo").read_text(encoding="utf-8")
        changed = source.replace("if a[middle] < target:", "if a[middle] <= target:")
        compiled = compile_project("general_consumer", root=EXAMPLES,
                                   sources={"general_binary_lower_bound": changed})
        checked = check_project(compiled, analysis_module="Algo.general_consumer.Analysis", timeout=120)
        self.assertFalse(checked.ok)
        self.assertIn("Algo/general_binary_lower_bound/Analysis.lean:", checked.output)

    def test_linear_variant_composes_sort_and_search_costs_without_changing_other_clocks(self):
        compiled = compile_project("general_linear_consumer", root=EXAMPLES)
        proof = """import Algo.general_linear_consumer.Analysis
open Algo2LeanGenerated

example (before after : Heap) (source : SeqRef) (lo hi key offset : Int)
    (execution : Algo.general_linear_consumer.insertion_offset.Run
      before (source, lo, hi, key) after offset) :
    0 ≤ offset ∧ offset ≤ ((hi - lo).toNat : Int) ∧
      Heap.cost before after "merge_sort" = GeneralMergeSortAnalysis.runtime (hi - lo).toNat ∧
      Heap.cost before after "search_comparisons" ≤ (hi - lo).toNat ∧
      Heap.cost before after "merge_sort" + Heap.cost before after "search_comparisons" ≤
        2 * (hi - lo).toNat * (Nat.log2 (hi - lo).toNat + 1) + (hi - lo).toNat + 1 ∧
      (∀ clock, clock ≠ "merge_sort" → clock ≠ "search_comparisons" →
        after.clocks clock = before.clocks clock) ∧
      (∀ object, object < before.nextRef → after.store object = before.store object) := by
  have specification := GeneralLinearConsumerAnalysis.correct execution
  obtain ⟨ordered, allocated, sorting, partition, preserved, sortCost, searchCost, otherClocks⟩ :=
    specification.2.2
  have sortBound : GeneralMergeSortAnalysis.runtime (hi - lo).toNat ≤
      2 * (hi - lo).toNat * (Nat.log2 (hi - lo).toNat + 1) + 1 :=
    Algo2Lean.MergeSortCost.work_le_logarithmic _
  exact ⟨specification.1, specification.2.1, sortCost, searchCost, by omega, otherClocks, preserved.2⟩

example (heap : Heap) (source : SeqRef) (lo hi key : Int)
    (valid : source < heap.nextRef) (empty : hi ≤ lo) :
    Algo.general_linear_consumer.insertion_offset.Run heap (source, lo, hi, key)
      (heap.tick "merge_sort") 0 := by
  have sort := GeneralMergeSortAnalysis.base_case_summary heap source lo hi valid (by omega)
  have search := GeneralLowerBoundAnalysis.empty_summary (heap.tick "merge_sort")
    source lo hi key (by simpa using valid) empty
  have combined := GeneralLinearSortThenSearchAnalysis.compose heap (heap.tick "merge_sort")
    (heap.tick "merge_sort") source source lo hi key lo sort search
  simpa using (GeneralLinearConsumerAnalysis.compose heap (heap.tick "merge_sort")
    source lo hi key lo combined).run
"""
        checked = check_project(compiled, analysis=proof, analysis_module="GeneralLinearExternalClient", timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
