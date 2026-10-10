import Algo.sort_three.Generated
import Algo.sort_three.Facts
import Algo.compare_exchange.Analysis
import Init.Data.List.Perm

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable three-element sorting contract.
- `sorted_permutation`: Sorted permutation of three elements.
- `untouched`: Values outside the three positions are preserved.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.sort_three

namespace SortThreeAnalysis

open CompareExchangeAnalysis

/-- The three compared positions; the surrounding infinite sequence is untouched. -/
def values (heap : Heap) (ref : SeqRef) (first : Int) : List Int :=
  [heap.read ref first, heap.read ref (first + 1), heap.read ref (first + 2)]

def Sorted (heap : Heap) (ref : SeqRef) (first : Int) : Prop :=
  heap.read ref first ≤ heap.read ref (first + 1) ∧
    heap.read ref (first + 1) ≤ heap.read ref (first + 2)

def sortedHeap (heap : Heap) (ref : SeqRef) (first : Int) : Heap :=
  let one := exchanged heap ref first (first + 1)
  let two := exchanged one ref (first + 1) (first + 2)
  exchanged two ref first (first + 1)

@[simp] theorem nextRef (heap : Heap) (ref : SeqRef) (first : Int) :
    (sortedHeap heap ref first).nextRef = heap.nextRef := by simp [sortedHeap]

theorem clocks (heap : Heap) (ref : SeqRef) (first : Int) (clock : String) :
    (sortedHeap heap ref first).clocks clock =
      heap.clocks clock + if clock = "sort_comparisons" then 3 else 0 := by
  by_cases same : clock = "sort_comparisons"
  · subst clock; simp [sortedHeap, CompareExchangeAnalysis.clocks, Heap.tick, Nat.add_assoc]
  · simp [sortedHeap, CompareExchangeAnalysis.clocks, Heap.tick, same]

theorem untouched (heap : Heap) (ref other : SeqRef) (first index : Int)
    (outside : other ≠ ref ∨ index < first ∨ first + 3 ≤ index) :
    (sortedHeap heap ref first).read other index = heap.read other index := by
  have one : other ≠ ref ∨ (index ≠ first ∧ index ≠ first + 1) := by
    rcases outside with different | low | high
    · exact Or.inl different
    · right; constructor <;> omega
    · right; constructor <;> omega
  have two : other ≠ ref ∨ (index ≠ first + 1 ∧ index ≠ first + 2) := by
    rcases outside with different | low | high
    · exact Or.inl different
    · right; constructor <;> omega
    · right; constructor <;> omega
  simp only [sortedHeap, CompareExchangeAnalysis.untouched _ _ _ _ _ _ one,
    CompareExchangeAnalysis.untouched _ _ _ _ _ _ two]

private theorem entries (heap : Heap) (ref : SeqRef) (first : Int) :
    let x := heap.read ref first
    let y := heap.read ref (first + 1)
    let z := heap.read ref (first + 2)
    (sortedHeap heap ref first).read ref first = min (min x y) (min (max x y) z) ∧
    (sortedHeap heap ref first).read ref (first + 1) = max (min x y) (min (max x y) z) ∧
    (sortedHeap heap ref first).read ref (first + 2) = max (max x y) z := by
  simp (disch := omega) [sortedHeap, CompareExchangeAnalysis.left_value,
    CompareExchangeAnalysis.right_value, CompareExchangeAnalysis.untouched]

private theorem pair_permutation (x y : Int) : [min x y, max x y].Perm [x, y] := by
  by_cases order : x ≤ y
  · simp [Int.min_def, Int.max_def, order]
  · simp only [Int.min_def, Int.max_def, if_neg order]
    exact List.Perm.swap _ _ _

/-- Correctness includes duplicate values, all integer offsets, and permutation. -/
theorem sorted_permutation (heap : Heap) (ref : SeqRef) (first : Int) :
    Sorted (sortedHeap heap ref first) ref first ∧
      (values (sortedHeap heap ref first) ref first).Perm (values heap ref first) := by
  obtain ⟨low, middle, high⟩ := entries heap ref first
  refine ⟨?_, ?_⟩
  · unfold Sorted
    rw [low, middle, high]
    constructor
    · exact Int.le_trans (Int.min_le_left _ _) (Int.le_max_left _ _)
    · apply Int.max_le.mpr
      constructor
      · exact Int.le_trans (Int.min_le_left _ _) (Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _))
      · exact Int.le_trans (Int.min_le_right _ _) (Int.le_max_right _ _)
  · unfold values
    rw [low, middle, high]
    let x := heap.read ref first
    let y := heap.read ref (first + 1)
    let z := heap.read ref (first + 2)
    have firstPair := (pair_permutation x y).append_right [z]
    have secondPair := (pair_permutation (max x y) z).cons (min x y)
    have thirdPair := (pair_permutation (min x y) (min (max x y) z)).append_right [max (max x y) z]
    exact thirdPair.trans (secondPair.trans firstPair)

/-- The helper's original proof is applied three times; no helper transition
    is reopened in this module. The resulting summary is reusable in turn. -/
theorem summary (heap : Heap) (ref : SeqRef) (first : Int) (valid : ref < heap.nextRef) :
    sort_three.Call heap (ref, first) (sortedHeap heap ref first) () := by
  open Algo.sort_three.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.sort_three_pc14 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc13 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc12 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc11 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller
      (CompareExchangeAnalysis.summary heap ref first (first + 1) valid).2).trans
    apply Reaches.prepend (Step.sort_three_pc10 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc9 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc8 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc7 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller
      (CompareExchangeAnalysis.summary _ ref (first + 1) (first + 2) (by simpa using valid)).2).trans
    apply Reaches.prepend (Step.sort_three_pc6 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc5 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc4 _ _ caller)
    apply Reaches.prepend (Step.sort_three_pc3 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller
      (CompareExchangeAnalysis.summary _ ref first (first + 1) (by simpa using valid)).2).trans
    apply Reaches.prepend (Step.sort_three_pc2 _ _ caller)
    exact Reaches.single (Step.sort_three_pc1 _ _ caller)

end SortThreeAnalysis
