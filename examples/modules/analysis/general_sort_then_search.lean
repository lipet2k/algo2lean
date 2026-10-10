import Algo.general_sort_then_search.Generated
import Algo.general_sort_then_search.Facts
import Algo.general_merge_sort.Analysis
import Algo.general_binary_lower_bound.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable sort-and-search contract.
- `terminates`: Termination.
- `correct`: Insertion-position correctness.
- `running_time`: Reused logarithmic sorting-work bound.
-/

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.SequenceModel
open Algo.general_sort_then_search

namespace GeneralSortThenSearchAnalysis

/-- The composition's specification uses the same interval model as both
    libraries. Sorting may allocate a new sequence; existing references survive. -/
def ResultSpec (before after : Heap) (source : SeqRef) (lo hi key result : Int) : Prop :=
  ∃ ordered, ordered < after.nextRef ∧
    SortedPermutation (before.store source) (after.store ordered) lo (hi - lo).toNat ∧
    LowerBound (after.store ordered) lo (hi - lo).toNat key result ∧
    GeneralMergeSortAnalysis.Extends before after ∧
    Heap.cost before after "merge_sort" = GeneralMergeSortAnalysis.runtime (hi - lo).toNat ∧
    (∀ clock, clock ≠ "merge_sort" → after.clocks clock = before.clocks clock)

/-- Actual imported calls compose through their existing public summaries. -/
theorem compose (before middle after : Heap) (source ordered : SeqRef) (lo hi key result : Int)
    (sort : Algo.general_merge_sort.merge_sort.Call before (source, lo, hi) middle ordered)
    (search : Algo.general_binary_lower_bound.lower_bound.Call middle (ordered, lo, hi, key) after result) :
    sort_then_search.Call before (source, lo, hi, key) after result := by
  open Algo.general_sort_then_search.Algo2LeanGenerated in
    refine ⟨sort.1, ?_⟩
    intro caller
    apply Reaches.prepend (Step.sort_then_search_pc11 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc10 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc9 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc8 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller sort.2).trans
    apply Reaches.prepend (Step.sort_then_search_pc7 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc6 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc5 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc4 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc3 _ _ caller)
    apply Reaches.prepend (Step.sort_then_search_pc2 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller search.2).trans
    exact Reaches.single (Step.sort_then_search_pc1 _ _ caller)

/-- Termination, correctness, and sorting work reuse the component contracts for
    every finite signed interval. Binary search leaves all clocks unchanged. -/
theorem summary (heap : Heap) (source : SeqRef) (lo hi key : Int) (valid : source < heap.nextRef) :
    ∃ after result, sort_then_search.Call heap (source, lo, hi, key) after result ∧
      ResultSpec heap after source lo hi key result := by
  obtain ⟨middle, ordered, sort, preserved, allocated, sorted, sortCost, sortOther⟩ :=
    GeneralMergeSortAnalysis.summary heap source lo hi valid
  obtain ⟨result, search, partition⟩ :=
    GeneralBinaryLowerBoundAnalysis.normalized_summary middle ordered lo hi key allocated sorted.1
  exact ⟨middle, result, compose heap middle middle source ordered lo hi key result sort search,
    ordered, allocated, sorted, partition, preserved, sortCost, sortOther⟩

theorem terminates (heap : Heap) (source : SeqRef) (lo hi key : Int) (valid : source < heap.nextRef) :
    ∃ after result, sort_then_search.Run heap (source, lo, hi, key) after result ∧
      ResultSpec heap after source lo hi key result := by
  obtain ⟨after, result, call, specification⟩ := summary heap source lo hi key valid
  exact ⟨after, result, call.run, specification⟩

-- Main result: Correctness
/-- The already-proved component behavior applies to every completed caller run. -/
theorem correct {heap after : Heap} {source : SeqRef} {lo hi key result : Int}
    (execution : sort_then_search.Run heap (source, lo, hi, key) after result) :
    ResultSpec heap after source lo hi key result := by
  obtain ⟨expectedHeap, expectedResult, call, specification⟩ := summary heap source lo hi key execution.1
  obtain ⟨sameHeap, sameResult⟩ := execution.eq_of_call call
  subst after
  subst result
  exact specification

/-- The imported sorting-work bound holds for every completed caller run.
    The clock counts sort calls and merged output writes. Binary search is
    uninstrumented, so this theorem bounds the sorting phase only. -/
theorem running_time {heap after : Heap} {source : SeqRef} {lo hi key result : Int}
    (execution : sort_then_search.Run heap (source, lo, hi, key) after result) :
    Heap.cost heap after "merge_sort" ≤
      2 * (hi - lo).toNat * (Nat.log2 (hi - lo).toNat + 1) + 1 := by
  obtain ⟨ordered, allocated, sorted, partition, preserved, cost, otherClocks⟩ := correct execution
  rw [cost]
  exact Algo2Lean.MergeSortCost.work_le_logarithmic (hi - lo).toNat

end GeneralSortThenSearchAnalysis
