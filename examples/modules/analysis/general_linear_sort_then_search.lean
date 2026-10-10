import Algo.general_linear_sort_then_search.Generated
import Algo.general_linear_sort_then_search.Facts
import Algo.general_merge_sort.Analysis
import Algo.general_lower_bound.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable sort-and-search contract.
- `terminates`: Termination.
- `correct`: Insertion-position correctness.
- `running_time`: Combined sorting-work and search-comparison bound.
-/

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.SequenceModel
open Algo.general_linear_sort_then_search

namespace GeneralLinearSortThenSearchAnalysis

/-- The composition's specification uses the same interval model as both
    libraries. Sorting may allocate a new sequence; existing references survive. -/
def ResultSpec (before after : Heap) (source : SeqRef) (lo hi key result : Int) : Prop :=
  ∃ ordered, ordered < after.nextRef ∧
    SortedPermutation (before.store source) (after.store ordered) lo (hi - lo).toNat ∧
    LowerBound (after.store ordered) lo (hi - lo).toNat key result ∧
    GeneralMergeSortAnalysis.Extends before after ∧
    Heap.cost before after "merge_sort" = GeneralMergeSortAnalysis.runtime (hi - lo).toNat ∧
    Heap.cost before after "search_comparisons" ≤ (hi - lo).toNat ∧
    (∀ clock, clock ≠ "merge_sort" → clock ≠ "search_comparisons" →
      after.clocks clock = before.clocks clock)

/-- Actual imported calls compose through their existing public summaries. -/
theorem compose (before middle after : Heap) (source ordered : SeqRef) (lo hi key result : Int)
    (sort : Algo.general_merge_sort.merge_sort.Call before (source, lo, hi) middle ordered)
    (search : Algo.general_lower_bound.lower_bound.Call middle (ordered, lo, hi, key) after result) :
    sort_then_search.Call before (source, lo, hi, key) after result := by
  open Algo.general_linear_sort_then_search.Algo2LeanGenerated in
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

/-- Termination, correctness, and both clock effects compose for every finite
    signed interval. Sorting preserves the search counter, and searching
    preserves the sort counter, including nonzero initial clock values. -/
theorem summary (heap : Heap) (source : SeqRef) (lo hi key : Int) (valid : source < heap.nextRef) :
    ∃ after result, sort_then_search.Call heap (source, lo, hi, key) after result ∧
      ResultSpec heap after source lo hi key result := by
  obtain ⟨middle, ordered, sort, preserved, allocated, sorted, sortCost, sortOther⟩ :=
    GeneralMergeSortAnalysis.summary heap source lo hi valid
  obtain ⟨comparisons, result, bound, search, partition⟩ :=
    GeneralLowerBoundAnalysis.summary middle ordered lo hi key allocated sorted.1
  have searchClock := sortOther "search_comparisons" (by decide)
  refine ⟨middle.tick "search_comparisons" comparisons, result,
    compose heap middle _ source ordered lo hi key result sort search, ordered, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using allocated
  · simpa [SortedPermutation, Sorted, interval, Heap.tick] using sorted
  · simpa [LowerBound] using partition
  · exact ⟨by simpa using preserved.1, fun object allocated => by simpa using preserved.2 object allocated⟩
  · simpa [Heap.cost, Heap.tick] using sortCost
  · simpa [Heap.cost, Heap.tick, searchClock] using bound
  · intro clock notSort notSearch
    simpa [Heap.tick, notSearch] using sortOther clock notSort

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

-- Main result: Running time
/-- Sorting work and search comparisons add along the same caller execution.
    The sorting counter counts sort calls and merged output writes; the search
    counter counts comparisons in the linear scan. -/
theorem running_time {heap after : Heap} {source : SeqRef} {lo hi key result : Int}
    (execution : sort_then_search.Run heap (source, lo, hi, key) after result) :
    Heap.cost heap after "merge_sort" + Heap.cost heap after "search_comparisons" ≤
      2 * (hi - lo).toNat * (Nat.log2 (hi - lo).toNat + 1) + (hi - lo).toNat + 1 := by
  obtain ⟨ordered, allocated, sorted, partition, preserved, sortCost, searchCost, otherClocks⟩ :=
    correct execution
  have sortBound := Algo2Lean.MergeSortCost.work_le_logarithmic (hi - lo).toNat
  change GeneralMergeSortAnalysis.runtime (hi - lo).toNat ≤ _ at sortBound
  omega

end GeneralLinearSortThenSearchAnalysis
