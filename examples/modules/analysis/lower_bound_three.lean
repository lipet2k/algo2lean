import Algo.lower_bound_three.Generated
import Algo.lower_bound_three.Facts

/-!
Analysis outline:
- `summary`: Reusable three-element search contract.
- `lower_bound`: Lower-bound correctness.
- `comparison_bound`: At most three comparisons.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.lower_bound_three

namespace LowerBoundThreeAnalysis

def position (heap : Heap) (ref : SeqRef) (first key : Int) : Int :=
  if key ≤ heap.read ref first then first
  else if key ≤ heap.read ref (first + 1) then first + 1
  else if key ≤ heap.read ref (first + 2) then first + 2
  else first + 3

def comparisons (heap : Heap) (ref : SeqRef) (first key : Int) : Nat :=
  if key ≤ heap.read ref first then 1
  else if key ≤ heap.read ref (first + 1) then 2
  else 3

/-- The returned insertion point separates values below the key from values
    at least the key, including duplicate keys and an absent key. -/
def LowerBound (heap : Heap) (ref : SeqRef) (first key result : Int) : Prop :=
  first ≤ result ∧ result ≤ first + 3 ∧
    (∀ index, first ≤ index → index < result → heap.read ref index < key) ∧
    (∀ index, result ≤ index → index < first + 3 → key ≤ heap.read ref index)

theorem comparison_bound (heap : Heap) (ref : SeqRef) (first key : Int) :
    1 ≤ comparisons heap ref first key ∧ comparisons heap ref first key ≤ 3 := by
  unfold comparisons
  split
  · decide
  · split <;> decide

theorem lower_bound (heap : Heap) (ref : SeqRef) (first key : Int)
    (sorted : heap.read ref first ≤ heap.read ref (first + 1) ∧
      heap.read ref (first + 1) ≤ heap.read ref (first + 2)) :
    LowerBound heap ref first key (position heap ref first key) := by
  rcases sorted with ⟨orderedFirst, orderedLast⟩
  unfold position
  split
  · unfold LowerBound
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro index low high; omega
    · intro index low high
      have cases : index = first ∨ index = first + 1 ∨ index = first + 2 := by omega
      rcases cases with equal | equal | equal <;> subst index <;> omega
  · split
    · unfold LowerBound
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro index low high
        have equal : index = first := by omega
        subst index; omega
      · intro index low high
        have cases : index = first + 1 ∨ index = first + 2 := by omega
        rcases cases with equal | equal <;> subst index <;> omega
    · split
      · unfold LowerBound
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro index low high
          have cases : index = first ∨ index = first + 1 := by omega
          rcases cases with equal | equal <;> subst index <;> omega
        · intro index low high
          have equal : index = first + 2 := by omega
          subst index; omega
      · unfold LowerBound
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro index low high
          have cases : index = first ∨ index = first + 1 ∨ index = first + 2 := by omega
          rcases cases with equal | equal | equal <;> subst index <;> omega
        · intro index low high; omega

/-- The search proof is independent of every sorting implementation. It gives
    an exact result and comparison count while preserving all program data. -/
theorem summary (heap : Heap) (ref : SeqRef) (first key : Int) (valid : ref < heap.nextRef) :
    lower_bound_three.Call heap (ref, first, key)
      (heap.tick "search_comparisons" (comparisons heap ref first key))
      (position heap ref first key) := by
  open Algo.lower_bound_three.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.lower_bound_three_pc17 _ _ caller)
    apply Reaches.prepend (Step.lower_bound_three_pc16 _ _ caller (by simpa using valid))
    by_cases firstHit : key ≤ heap.read ref first
    · simp only [position, comparisons, if_pos firstHit]
      apply Reaches.prepend (Step.lower_bound_three_pc15_true _ _ caller (by simpa using firstHit))
      apply Reaches.prepend (Step.lower_bound_three_pc14 _ _ caller)
      exact Reaches.single (Step.lower_bound_three_pc13 _ _ caller)
    · simp only [position, comparisons, if_neg firstHit]
      apply Reaches.prepend (Step.lower_bound_three_pc15_false _ _ caller (by simp [firstHit]))
      apply Reaches.prepend (Step.lower_bound_three_pc12 _ _ caller)
      apply Reaches.prepend (Step.lower_bound_three_pc11 _ _ caller (by simpa using valid))
      by_cases secondHit : key ≤ heap.read ref (first + 1)
      · simp only [if_pos secondHit]
        apply Reaches.prepend (Step.lower_bound_three_pc10_true _ _ caller (by simpa using secondHit))
        apply Reaches.prepend (Step.lower_bound_three_pc9 _ _ caller)
        simpa only [Heap.tick_add] using Reaches.single (Step.lower_bound_three_pc8 _ _ caller)
      · simp only [if_neg secondHit]
        apply Reaches.prepend (Step.lower_bound_three_pc10_false _ _ caller (by simp [secondHit]))
        apply Reaches.prepend (Step.lower_bound_three_pc7 _ _ caller)
        apply Reaches.prepend (Step.lower_bound_three_pc6 _ _ caller (by simpa using valid))
        by_cases thirdHit : key ≤ heap.read ref (first + 2)
        · simp only [if_pos thirdHit]
          apply Reaches.prepend (Step.lower_bound_three_pc5_true _ _ caller (by simpa using thirdHit))
          apply Reaches.prepend (Step.lower_bound_three_pc4 _ _ caller)
          simpa only [Heap.tick_add] using Reaches.single (Step.lower_bound_three_pc3 _ _ caller)
        · simp only [if_neg thirdHit]
          apply Reaches.prepend (Step.lower_bound_three_pc5_false _ _ caller (by simp [thirdHit]))
          apply Reaches.prepend (Step.lower_bound_three_pc2 _ _ caller)
          simpa only [Heap.tick_add] using Reaches.single (Step.lower_bound_three_pc1 _ _ caller)

end LowerBoundThreeAnalysis
