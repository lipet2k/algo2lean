import Algo.general_lower_bound.Generated
import Algo.general_lower_bound.Facts
import Algo2LeanLib.SequenceModel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable linear-search contract.
- `correct`: Lower-bound correctness and linear cost.
-/

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.SequenceModel
open Algo.general_lower_bound

namespace GeneralLowerBoundAnalysis

theorem empty_summary (heap : Heap) (ref : SeqRef) (lo hi key : Int)
    (valid : ref < heap.nextRef) (empty : hi ≤ lo) :
    lower_bound.Call heap (ref, lo, hi, key) heap lo := by
  open Algo.general_lower_bound.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.lower_bound_pc15 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc14_true _ _ caller (by simpa using empty))
    apply Reaches.prepend (Step.lower_bound_pc13 _ _ caller)
    exact Reaches.single (Step.lower_bound_pc12 _ _ caller)

theorem hit_summary (heap : Heap) (ref : SeqRef) (lo hi key : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) (hit : key ≤ heap.read ref lo) :
    lower_bound.Call heap (ref, lo, hi, key) (heap.tick "search_comparisons") lo := by
  open Algo.general_lower_bound.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.lower_bound_pc15 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc14_false _ _ caller (by simp; omega))
    apply Reaches.prepend (Step.lower_bound_pc11 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc10 _ _ caller (by simpa using valid))
    apply Reaches.prepend (Step.lower_bound_pc9_true _ _ caller (by simpa using hit))
    apply Reaches.prepend (Step.lower_bound_pc8 _ _ caller)
    exact Reaches.single (Step.lower_bound_pc7 _ _ caller)

/-- A recursive search step reuses a summary for the remaining interval. -/
theorem continue_summary (heap finalHeap : Heap) (ref : SeqRef) (lo hi key result : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) (miss : heap.read ref lo < key)
    (tail : lower_bound.Call (heap.tick "search_comparisons")
      (ref, lo + 1, hi, key) finalHeap result) :
    lower_bound.Call heap (ref, lo, hi, key) finalHeap result := by
  open Algo.general_lower_bound.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.lower_bound_pc15 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc14_false _ _ caller (by simp; omega))
    apply Reaches.prepend (Step.lower_bound_pc11 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc10 _ _ caller (by simpa using valid))
    apply Reaches.prepend (Step.lower_bound_pc9_false _ _ caller (by simp; omega))
    apply Reaches.prepend (Step.lower_bound_pc6 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc5 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc4 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc3 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_pc2 _ _ caller)
    apply (tail.2 _).trans
    exact Reaches.single (Step.lower_bound_pc1 _ _ caller)

/-- A finite sorted interval has a lower bound, found with at most one
    comparison per entry. The entire heap is unchanged apart from that counter. -/
theorem count_summary (count : Nat) (heap : Heap) (ref : SeqRef) (first key : Int)
    (valid : ref < heap.nextRef) (sorted : Sorted (heap.store ref) first count) :
    ∃ comparisons result, comparisons ≤ count ∧
      lower_bound.Call heap (ref, first, first + (count : Int), key)
        (heap.tick "search_comparisons" comparisons) result ∧
      LowerBound (heap.store ref) first count key result := by
  induction count generalizing heap first with
  | zero =>
    refine ⟨0, first, by omega, ?_, ?_⟩
    · simpa using empty_summary heap ref first first key valid (by omega)
    · refine ⟨by omega, by omega, ?_, ?_⟩ <;> intro index low high <;> omega
  | succ count ih =>
    by_cases hit : key ≤ heap.read ref first
    · refine ⟨1, first, by omega, hit_summary heap ref first _ key valid (by omega) hit, ?_⟩
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro index low high; omega
      · intro index low high
        exact Int.le_trans hit (head_le _ _ _ sorted index low high)
    · have miss : heap.read ref first < key := by omega
      obtain ⟨comparisons, result, bound, call, partition⟩ :=
        ih (heap.tick "search_comparisons") (first + 1)
          (by simpa using valid) (by simpa using sorted_tail _ _ _ sorted)
      have endpoint : first + 1 + (count : Int) = first + ((count + 1 : Nat) : Int) := by omega
      have continued := continue_summary heap (heap.tick "search_comparisons" |>.tick "search_comparisons" comparisons)
        ref first (first + ((count + 1 : Nat) : Int)) key result valid (by omega) miss
        (by simpa only [endpoint] using call)
      refine ⟨comparisons + 1, result, by omega, ?_, ?_⟩
      · simpa [Heap.tick_add, Nat.add_comm] using continued
      · rcases partition with ⟨lower, upper, before, after⟩
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro index low high
          by_cases equal : index = first
          · simpa [equal] using! miss
          · exact before index (by omega) high
        · intro index low high
          exact after index low (by omega)

/-- Signed bounds include negative, empty and reversed intervals. -/
theorem summary (heap : Heap) (ref : SeqRef) (lo hi key : Int)
    (valid : ref < heap.nextRef) (sorted : Sorted (heap.store ref) lo (hi - lo).toNat) :
    ∃ comparisons result, comparisons ≤ (hi - lo).toNat ∧
      lower_bound.Call heap (ref, lo, hi, key)
        (heap.tick "search_comparisons" comparisons) result ∧
      LowerBound (heap.store ref) lo (hi - lo).toNat key result := by
  by_cases ordered : lo ≤ hi
  · have endpoint : lo + ((hi - lo).toNat : Int) = hi := by omega
    simpa only [endpoint] using count_summary (hi - lo).toNat heap ref lo key valid sorted
  · have empty : (hi - lo).toNat = 0 := by omega
    refine ⟨0, lo, by omega, ?_, ?_⟩
    · simpa using empty_summary heap ref lo hi key valid (by omega)
    · rw [empty]
      refine ⟨by omega, by omega, ?_, ?_⟩ <;> intro index low high <;> omega

-- Main result: Correctness and running time
/-- The correctness and linear comparison bound hold for every completed run. -/
theorem correct {heap after : Heap} {ref : SeqRef} {lo hi key result : Int}
    (sorted : Sorted (heap.store ref) lo (hi - lo).toNat)
    (execution : lower_bound.Run heap (ref, lo, hi, key) after result) :
    LowerBound (heap.store ref) lo (hi - lo).toNat key result ∧
      ∃ comparisons, comparisons ≤ (hi - lo).toNat ∧ after = heap.tick "search_comparisons" comparisons := by
  obtain ⟨comparisons, answer, bound, call, partition⟩ := summary heap ref lo hi key execution.1 sorted
  obtain ⟨sameHeap, sameResult⟩ := execution.eq_of_call call
  subst after
  subst result
  exact ⟨partition, comparisons, bound, rfl⟩

end GeneralLowerBoundAnalysis
