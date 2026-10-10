import Algo.compare_exchange.Generated
import Algo.compare_exchange.Facts

/-!
Analysis outline:
- `summary`: Reusable compare-exchange contract.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.compare_exchange

namespace CompareExchangeAnalysis

/-- The exact heap effect of one comparison and an optional exchange. -/
def exchanged (heap : Heap) (ref : SeqRef) (left right : Int) : Heap :=
  if heap.read ref left ≤ heap.read ref right then heap.tick "sort_comparisons"
  else ((heap.tick "sort_comparisons").write ref left (heap.read ref right)).write ref right (heap.read ref left)

@[simp] theorem nextRef (heap : Heap) (ref : SeqRef) (left right : Int) :
    (exchanged heap ref left right).nextRef = heap.nextRef := by
  unfold exchanged
  split <;> simp

theorem clocks (heap : Heap) (ref : SeqRef) (left right : Int) :
    (exchanged heap ref left right).clocks = (heap.tick "sort_comparisons").clocks := by
  unfold exchanged
  split <;> rfl

theorem left_value (heap : Heap) (ref : SeqRef) (left right : Int) (distinct : left ≠ right) :
    (exchanged heap ref left right).read ref left = min (heap.read ref left) (heap.read ref right) := by
  unfold exchanged
  split <;> simp_all [Int.min_def] <;> omega

theorem right_value (heap : Heap) (ref : SeqRef) (left right : Int) (_distinct : left ≠ right) :
    (exchanged heap ref left right).read ref right = max (heap.read ref left) (heap.read ref right) := by
  unfold exchanged
  split <;> simp_all [Int.max_def] <;> omega

theorem untouched (heap : Heap) (ref other : SeqRef) (left right index : Int)
    (outside : other ≠ ref ∨ (index ≠ left ∧ index ≠ right)) :
    (exchanged heap ref left right).read other index = heap.read other index := by
  unfold exchanged
  split
  · simp
  · rcases outside with different | ⟨notLeft, notRight⟩
    · simp [different]
    · simp [Heap.read, Heap.write, notLeft, notRight]

/-- The independently compiled helper sorts a pair under every caller stack,
    preserving its object identity and charging exactly one comparison. -/
theorem summary (heap : Heap) (ref : SeqRef) (left right : Int)
    (valid : ref < heap.nextRef) :
    compare_exchange.Call heap (ref, left, right) (exchanged heap ref left right) () := by
  open Algo.compare_exchange.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.compare_exchange_pc9 _ _ caller)
    apply Reaches.prepend (Step.compare_exchange_pc8 _ _ caller (by simpa using valid))
    apply Reaches.prepend (Step.compare_exchange_pc7 _ _ caller (by simpa using valid))
    apply Reaches.prepend (Step.compare_exchange_pc6 _ _ caller)
    by_cases ordered : heap.read ref left ≤ heap.read ref right
    · simp only [exchanged, if_pos ordered]
      apply Reaches.prepend (Step.compare_exchange_pc5_false _ _ caller (by simp; omega))
      apply Reaches.prepend (Step.compare_exchange_pc2 _ _ caller)
      exact Reaches.single (Step.compare_exchange_pc1 _ _ caller)
    · simp only [exchanged, if_neg ordered]
      apply Reaches.prepend (Step.compare_exchange_pc5_true _ _ caller (by simp; omega))
      apply Reaches.prepend (Step.compare_exchange_pc4 _ _ caller (by simpa using valid))
      apply Reaches.prepend (Step.compare_exchange_pc3 _ _ caller (by simpa using valid))
      apply Reaches.prepend (Step.compare_exchange_pc2 _ _ caller)
      simpa using Reaches.single (Step.compare_exchange_pc1 _ _ caller)

end CompareExchangeAnalysis
