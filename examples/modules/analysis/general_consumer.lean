import Algo.general_consumer.Generated
import Algo.general_consumer.Facts
import Algo.general_sort_then_search.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable sort-and-search contract.
- `terminates`: Termination.
- `correct`: Insertion-position correctness.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.general_consumer

namespace GeneralConsumerAnalysis

open GeneralSortThenSearchAnalysis

/-- An external user of the already-verified composition returns an offset
    within the normalized interval and retains all imported guarantees. -/
def OffsetSpec (before after : Heap) (source : SeqRef) (lo hi key result : Int) : Prop :=
  0 ≤ result ∧ result ≤ ((hi - lo).toNat : Int) ∧
    ResultSpec before after source lo hi key (lo + result)

theorem compose (before after : Heap) (source : SeqRef) (lo hi key position : Int)
    (call : Algo.general_sort_then_search.sort_then_search.Call before
      (source, lo, hi, key) after position) :
    insertion_offset.Call before (source, lo, hi, key) after (position - lo) := by
  open Algo.general_consumer.Algo2LeanGenerated in
    refine ⟨call.1, ?_⟩
    intro caller
    apply Reaches.prepend (Step.insertion_offset_pc8 _ _ caller)
    apply Reaches.prepend (Step.insertion_offset_pc7 _ _ caller)
    apply Reaches.prepend (Step.insertion_offset_pc6 _ _ caller)
    apply Reaches.prepend (Step.insertion_offset_pc5 _ _ caller)
    apply Reaches.prepend (Step.insertion_offset_pc4 _ _ caller)
    apply (ModuleCall.summary import_2_simulates _ caller call.2).trans
    apply Reaches.prepend (Step.insertion_offset_pc3 _ _ caller)
    apply Reaches.prepend (Step.insertion_offset_pc2 _ _ caller)
    exact Reaches.single (Step.insertion_offset_pc1 _ _ caller)

/-- No sorting or searching proof is repeated at this third reuse layer. -/
theorem summary (heap : Heap) (source : SeqRef) (lo hi key : Int) (valid : source < heap.nextRef) :
    ∃ after result, insertion_offset.Call heap (source, lo, hi, key) after result ∧
      OffsetSpec heap after source lo hi key result := by
  obtain ⟨after, position, call, specification⟩ := GeneralSortThenSearchAnalysis.summary heap source lo hi key valid
  have bounds : lo ≤ position ∧ position ≤ lo + ((hi - lo).toNat : Int) := by
    obtain ⟨ordered, _, _, partition, _⟩ := specification
    exact ⟨partition.1, partition.2.1⟩
  refine ⟨after, position - lo, compose heap after source lo hi key position call, by omega, by omega, ?_⟩
  have equal : lo + (position - lo) = position := by omega
  simpa only [equal] using specification

theorem terminates (heap : Heap) (source : SeqRef) (lo hi key : Int) (valid : source < heap.nextRef) :
    ∃ after result, insertion_offset.Run heap (source, lo, hi, key) after result ∧
      OffsetSpec heap after source lo hi key result := by
  obtain ⟨after, result, call, specification⟩ := summary heap source lo hi key valid
  exact ⟨after, result, call.run, specification⟩

-- Main result: Correctness
theorem correct {heap after : Heap} {source : SeqRef} {lo hi key result : Int}
    (execution : insertion_offset.Run heap (source, lo, hi, key) after result) :
    OffsetSpec heap after source lo hi key result := by
  obtain ⟨expectedHeap, expectedResult, call, specification⟩ := summary heap source lo hi key execution.1
  obtain ⟨sameHeap, sameResult⟩ := execution.eq_of_call call
  subst after
  subst result
  exact specification

end GeneralConsumerAnalysis
