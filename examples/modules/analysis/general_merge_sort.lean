import Algo.general_merge_sort.Points
import Algo.general_merge_sort.Facts
import Algo2LeanLib.SequenceModel
import Init.Data.List.Sort.Lemmas
import Algo2LeanLib.MergeSortCost

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Correctness and running time of merge sort over mutable integer sequences.

Main results: `every_output_correct` (correctness), `running_time` (runtime bound).

The final theorems `terminates`, `every_output_correct`,
`execution_preserves_objects`, and `every_execution_correct` cover every finite
integer interval, including negative, empty, and reversed bounds. They establish
termination, sortedness, permutation (including duplicates), preservation outside
the interval, valid returned references, and preservation of every old heap object.

Proof outline:
1. `interval`, `writeValues`, and `mergeValues` connect finite lists to infinite
   sequences and use the standard library's list-merge results.
2. `right_tail_summary`, `left_tail_summary`, and `merge_loop_summary` verify the
   three named source loops, yielding `merge_summary`.
3. `split_sort_summary` composes the recursive calls. `sort_count_summary` proves
   termination and the specification by induction on interval length.
4. Determinism transfers that constructed specification to every valid output.

The theorem and helper statements use mathematical objects and the public
algorithm interface. Generated instructions and fields occur only in proofs.
The runtime counts sort calls and merged output writes, treating sequence copies
as constant-time mathematical snapshots. It excludes integer bit complexity.
No stability theorem for distinguishable equal keys is claimed.
-/

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.SequenceModel
open Algo.general_merge_sort Algo.general_merge_sort.Algo2LeanGenerated
namespace GeneralMergeSortAnalysis

/-- Store a finite list consecutively, charging one merge-sort unit per element. -/
def writeValues (heap : Heap) (object : SeqRef) (first : Int) : List Int → Heap
  | [] => heap
  | value :: rest => writeValues ((heap.write object first value).tick "merge_sort") object (first + 1) rest

@[simp] theorem writeValues_nextRef (heap : Heap) (object : SeqRef) (first : Int) (values : List Int) :
    (writeValues heap object first values).nextRef = heap.nextRef := by
  induction values generalizing heap first with
  | nil => rfl
  | cons value rest ih => simp [writeValues, ih, Heap.write]

/-- Writing one object's interval preserves every other object's entire contents. -/
theorem writeValues_other (heap : Heap) (object other : SeqRef) (first : Int) (values : List Int)
    (different : other ≠ object) :
    (writeValues heap object first values).store other = heap.store other := by
  induction values generalizing heap first with
  | nil => rfl
  | cons value rest ih =>
    rw [writeValues, ih]
    funext i
    simp [Heap.write, different]

/-- Every integer position outside the written interval retains its old value. -/
theorem writeValues_outside (heap : Heap) (object : SeqRef) (first i : Int) (values : List Int)
    (outside : i < first ∨ first + (values.length : Int) ≤ i) :
    (writeValues heap object first values).store object i = heap.store object i := by
  induction values generalizing heap first with
  | nil => rfl
  | cons value rest ih =>
    rw [writeValues, ih]
    · have different : i ≠ first := by simp only [List.length_cons] at outside; omega
      simp [Heap.write, different]
    · simp only [List.length_cons] at outside
      omega

/-- Reading the entire interval just written recovers the list exactly. -/
theorem interval_writeValues (heap : Heap) (object : SeqRef) (first : Int) (values : List Int) :
    interval ((writeValues heap object first values).store object) first values.length = values := by
  induction values generalizing heap first with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.length_cons, writeValues, interval]
    rw [writeValues_outside _ _ _ _ _ (Or.inl (by omega)), ih]
    simp [Heap.write]

/-- Consecutive batches of stores equal a single concatenated batch. -/
theorem writeValues_append (heap : Heap) (object : SeqRef) (first : Int) (xs ys : List Int) :
    writeValues heap object first (xs ++ ys) =
      writeValues (writeValues heap object first xs) object (first + (xs.length : Int)) ys := by
  induction xs generalizing heap first with
  | nil => simp [writeValues]
  | cons value rest ih =>
    simpa [writeValues, Int.add_assoc, Int.add_comm, Int.add_left_comm] using
      ih ((heap.write object first value).tick "merge_sort") (first + 1)

/-- Each stored element contributes one unit to the merge-sort counter. -/
theorem writeValues_clocks (heap : Heap) (object : SeqRef) (first : Int) (values : List Int) :
    (writeValues heap object first values).clocks "merge_sort" =
      heap.clocks "merge_sort" + values.length := by
  induction values generalizing heap first with
  | nil => simp [writeValues]
  | cons value rest ih => simp [writeValues, ih, Nat.add_assoc, Nat.add_comm 1]

/-- Mathematical stable merge: ties are taken from the left list. -/
def mergeValues (left right : List Int) : List Int :=
  List.merge left right (fun a b => decide (a ≤ b))

@[simp] theorem mergeValues_length (left right : List Int) :
    (mergeValues left right).length = left.length + right.length :=
  List.length_merge _ _ _

/-- Mathematical merging preserves the multiset, including duplicates. -/
theorem mergeValues_permutation (left right : List Int) :
    (mergeValues left right).Perm (left ++ right) :=
  List.merge_perm_append _

/-- Two sorted input lists merge into a sorted list. -/
theorem mergeValues_sorted (left right : List Int)
    (leftSorted : left.Pairwise (· ≤ ·)) (rightSorted : right.Pairwise (· ≤ ·)) :
    (mergeValues left right).Pairwise (· ≤ ·) := by
  have result := List.pairwise_merge (le := fun a b : Int => decide (a ≤ b))
    (by intros; simp_all; omega) (by intros; simp; omega) left right
    (by simpa using leftSorted) (by simpa using rightSorted)
  simpa [mergeValues] using result

/-- An extension may allocate new objects but preserves every earlier object. -/
def Extends (before after : Heap) : Prop :=
  before.nextRef ≤ after.nextRef ∧
  ∀ object, object < before.nextRef → after.store object = before.store object

theorem Extends.refl (heap : Heap) : Extends heap heap := ⟨by omega, by intros; rfl⟩

theorem Extends.trans {first middle last : Heap}
    (left : Extends first middle) (right : Extends middle last) : Extends first last := by
  refine ⟨Nat.le_trans left.1 right.1, ?_⟩
  intro object allocated
  rw [right.2 object (Nat.lt_of_lt_of_le allocated left.1), left.2 object allocated]

/-- Copy the remaining right suffix into consecutive output positions and return.
    The input and destination are distinct allocated objects. -/
theorem right_tail_summary (count : Nat) (state : Configuration)
    (source result : SeqRef) (right output : Int)
    (location : merge.At.right_remaining state)
    (readSource : merge.Local.a state = some source)
    (readResult : merge.Local.result state = some result)
    (readRight : merge.Local.right state = some right)
    (readEnd : merge.Local.hi state = some (right + (count : Int)))
    (readOutput : merge.Local.output state = some output)
    (sourceValid : source < state.heap.nextRef) (resultValid : result < state.heap.nextRef)
    (distinct : source ≠ result) :
    merge.CallFrom state
      (writeValues state.heap result output (interval (state.heap.store source) right count)) result := by
  cases state with
  | done => cases location
  | active heap frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_merge_sort => cases location
    | fn_demo_merge_sort => cases location
    | fn_merge pc s =>
      have atLoop : pc = 4 := by unfold merge.At.right_remaining at location; split at location <;> simp_all
      subst pc
      simp [merge.Local.a, merge.Local.result, merge.Local.right, merge.Local.hi,
        merge.Local.output] at readSource readResult readRight readEnd readOutput
      dsimp only [Config.heap] at sourceValid resultValid ⊢
      induction count generalizing heap s right output with
      | zero =>
        intro stack
        apply Reaches.trans (Reaches.single (Step.merge_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega)))
        apply Reaches.trans (Reaches.single (Step.merge_pc2 ..))
        simpa [interval, writeValues, readResult] using
          Reaches.single (Step.merge_pc1 heap _ stack (by simpa [readResult] using resultValid))
      | succ count ih =>
        have next := ih (heap := (heap.write result output (heap.read source right)).tick "merge_sort")
          (s := { s with v6 := right + 1, v7 := output + 1, t9 := decide (s.v6 < s.v3) })
          (right := right + 1) (output := output + 1)
          (location := True.intro) (readSource := readSource) (readResult := readResult)
          (readRight := rfl) (readEnd := by simp; omega) (readOutput := rfl)
          (sourceValid := sourceValid) (resultValid := resultValid)
        intro stack
        apply Reaches.trans (Reaches.single (Step.merge_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc3_true _ _ _
          (by simp only [decide_eq_true_eq]; omega)))
        apply Reaches.trans (Reaches.single (Step.merge_pc8 _ _ _
          ⟨by simpa [readSource] using sourceValid, by simpa [readResult] using resultValid⟩))
        apply Reaches.trans (Reaches.single (Step.merge_pc7 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc6 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc5 ..))
        have untouched : (heap.write result output (heap.store source right)).store source = heap.store source := by
          funext i; simp [Heap.write, distinct]
        simpa [interval, writeValues, readSource, readResult, readRight, readOutput,
          Heap.read, untouched] using next stack

/-- Finish by copying the left suffix and then the right suffix. -/
theorem left_tail_summary (leftCount rightCount : Nat) (state : Configuration)
    (source result : SeqRef) (left right output : Int)
    (location : merge.At.left_remaining state)
    (readSource : merge.Local.a state = some source)
    (readResult : merge.Local.result state = some result)
    (readLeft : merge.Local.left state = some left)
    (readMiddle : merge.Local.mid state = some (left + (leftCount : Int)))
    (readRight : merge.Local.right state = some right)
    (readEnd : merge.Local.hi state = some (right + (rightCount : Int)))
    (readOutput : merge.Local.output state = some output)
    (sourceValid : source < state.heap.nextRef) (resultValid : result < state.heap.nextRef)
    (distinct : source ≠ result) :
    merge.CallFrom state
      (writeValues state.heap result output
        (interval (state.heap.store source) left leftCount ++
         interval (state.heap.store source) right rightCount)) result := by
  cases state with
  | done => cases location
  | active heap frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_merge_sort => cases location
    | fn_demo_merge_sort => cases location
    | fn_merge pc s =>
      have atLoop : pc = 10 := by unfold merge.At.left_remaining at location; split at location <;> simp_all
      subst pc
      simp [merge.Local.a, merge.Local.result, merge.Local.left, merge.Local.mid,
        merge.Local.right, merge.Local.hi, merge.Local.output] at readSource readResult readLeft readMiddle readRight readEnd readOutput
      dsimp only [Config.heap] at sourceValid resultValid ⊢
      induction leftCount generalizing heap s left output with
      | zero =>
        have rest := right_tail_summary rightCount
          (.active heap (.fn_merge 4 { s with t10 := decide (s.v5 < s.v2) }) originalStack)
          source result right output True.intro
          (by simpa [merge.Local.a] using readSource)
          (by simpa [merge.Local.result] using readResult)
          (by simpa [merge.Local.right] using readRight)
          (by simpa [merge.Local.hi] using readEnd)
          (by simpa [merge.Local.output] using readOutput)
          sourceValid resultValid distinct
        intro stack
        apply Reaches.trans (Reaches.single (Step.merge_pc10 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc9_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega)))
        simpa [interval] using! rest stack
      | succ leftCount ih =>
        have next := ih (heap := (heap.write result output (heap.read source left)).tick "merge_sort")
          (s := { s with v5 := left + 1, v7 := output + 1, t10 := decide (s.v5 < s.v2) })
          (left := left + 1) (output := output + 1)
          (location := True.intro) (readSource := readSource) (readResult := readResult)
          (readLeft := rfl) (readMiddle := by simp; omega) (readOutput := rfl)
          (readRight := readRight) (readEnd := readEnd)
          (sourceValid := sourceValid) (resultValid := resultValid)
        intro stack
        apply Reaches.trans (Reaches.single (Step.merge_pc10 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc9_true _ _ _
          (by simp only [decide_eq_true_eq]; omega)))
        apply Reaches.trans (Reaches.single (Step.merge_pc14 _ _ _
          ⟨by simpa [readSource] using sourceValid, by simpa [readResult] using resultValid⟩))
        apply Reaches.trans (Reaches.single (Step.merge_pc13 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc12 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc11 ..))
        have untouched : (heap.write result output (heap.store source left)).store source = heap.store source := by
          funext i; simp [Heap.write, distinct]
        simpa [interval, writeValues, readSource, readResult, readLeft, readOutput,
          Heap.read, untouched] using next stack

/-- Merge both remaining suffixes by comparing their heads, then copy the tail.
    This correspondence needs no sortedness assumption: it implements list merge. -/
theorem merge_loop_summary (leftCount rightCount : Nat) (state : Configuration)
    (source result : SeqRef) (left right output : Int)
    (location : merge.At.both_remaining state)
    (readSource : merge.Local.a state = some source)
    (readResult : merge.Local.result state = some result)
    (readLeft : merge.Local.left state = some left)
    (readMiddle : merge.Local.mid state = some (left + (leftCount : Int)))
    (readRight : merge.Local.right state = some right)
    (readEnd : merge.Local.hi state = some (right + (rightCount : Int)))
    (readOutput : merge.Local.output state = some output)
    (sourceValid : source < state.heap.nextRef) (resultValid : result < state.heap.nextRef)
    (distinct : source ≠ result) :
    merge.CallFrom state
      (writeValues state.heap result output
        (mergeValues (interval (state.heap.store source) left leftCount)
          (interval (state.heap.store source) right rightCount))) result := by
  cases state with
  | done => cases location
  | active heap frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_merge_sort => cases location
    | fn_demo_merge_sort => cases location
    | fn_merge pc s =>
      have atLoop : pc = 16 := by unfold merge.At.both_remaining at location; split at location <;> simp_all
      subst pc
      simp [merge.Local.a, merge.Local.result, merge.Local.left, merge.Local.mid,
        merge.Local.right, merge.Local.hi, merge.Local.output] at readSource readResult readLeft readMiddle readRight readEnd readOutput
      dsimp only [Config.heap] at sourceValid resultValid ⊢
      by_cases empty : leftCount = 0 ∨ rightCount = 0
      · have rest := left_tail_summary leftCount rightCount
          (.active heap (.fn_merge 10
            { s with t11 := decide (s.v5 < s.v2) && decide (s.v6 < s.v3) }) originalStack)
          source result left right output True.intro
          (by simpa [merge.Local.a] using readSource)
          (by simpa [merge.Local.result] using readResult)
          (by simpa [merge.Local.left] using readLeft)
          (by simpa [merge.Local.mid] using readMiddle)
          (by simpa [merge.Local.right] using readRight)
          (by simpa [merge.Local.hi] using readEnd)
          (by simpa [merge.Local.output] using readOutput)
          sourceValid resultValid distinct
        intro stack
        apply Reaches.trans (Reaches.single (Step.merge_pc16 ..))
        apply Reaches.trans (Reaches.single (Step.merge_pc15_false _ _ _
          (by simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)))
        rcases empty with empty | empty <;> subst_vars <;>
          simpa [mergeValues, interval] using! rest stack
      · have leftPositive : 0 < leftCount := by omega
        have rightPositive : 0 < rightCount := by omega
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : leftCount ≠ 0)
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rightCount ≠ 0)
        by_cases takeLeft : heap.store source left ≤ heap.store source right
        · let nextState : Configuration :=
            .active ((heap.write result output (heap.read source left)).tick "merge_sort")
              (.fn_merge 16 { s with
                v5 := left + 1, v7 := output + 1,
                t11 := decide (s.v5 < s.v2) && decide (s.v6 < s.v3),
                t12 := decide (heap.read s.v0 s.v5 ≤ heap.read s.v0 s.v6) }) originalStack
          have next := merge_loop_summary n (m + 1) nextState source result (left + 1) right (output + 1)
            True.intro
            (by simpa [nextState, merge.Local.a] using readSource)
            (by simpa [nextState, merge.Local.result] using readResult)
            (by simp [nextState, merge.Local.left])
            (by simp [nextState, merge.Local.mid]; omega)
            (by simpa [nextState, merge.Local.right] using readRight)
            (by simpa [nextState, merge.Local.hi] using readEnd)
            (by simp [nextState, merge.Local.output])
            sourceValid resultValid distinct
          intro stack
          apply Reaches.trans (Reaches.single (Step.merge_pc16 ..))
          apply Reaches.trans (Reaches.single (Step.merge_pc15_true _ _ _
            (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)))
          apply Reaches.trans (Reaches.single (Step.merge_pc24 _ _ _ (by simpa [readSource] using sourceValid)))
          apply Reaches.trans (Reaches.single (Step.merge_pc23_true _ _ _
            (by simpa [Heap.read, readSource, readLeft, readRight] using takeLeft)))
          apply Reaches.trans (Reaches.single (Step.merge_pc20 _ _ _
            ⟨by simpa [readSource] using sourceValid, by simpa [readResult] using resultValid⟩))
          apply Reaches.trans (Reaches.single (Step.merge_pc19 ..))
          apply Reaches.trans (Reaches.single (Step.merge_pc18 ..))
          apply Reaches.trans (Reaches.single (Step.merge_pc17 ..))
          have untouched : (heap.write result output (heap.store source left)).store source = heap.store source := by
            funext i; simp [Heap.write, distinct]
          simpa [nextState, Config.heap, interval, mergeValues, List.merge, writeValues,
            readSource, readResult, readLeft, readRight, readOutput, Heap.read, untouched, takeLeft] using next stack
        · let nextState : Configuration :=
            .active ((heap.write result output (heap.read source right)).tick "merge_sort")
              (.fn_merge 16 { s with
                v6 := right + 1, v7 := output + 1,
                t11 := decide (s.v5 < s.v2) && decide (s.v6 < s.v3),
                t12 := decide (heap.read s.v0 s.v5 ≤ heap.read s.v0 s.v6) }) originalStack
          have next := merge_loop_summary (n + 1) m nextState source result left (right + 1) (output + 1)
            True.intro
            (by simpa [nextState, merge.Local.a] using readSource)
            (by simpa [nextState, merge.Local.result] using readResult)
            (by simpa [nextState, merge.Local.left] using readLeft)
            (by simpa [nextState, merge.Local.mid] using readMiddle)
            (by simp [nextState, merge.Local.right])
            (by simp [nextState, merge.Local.hi]; omega)
            (by simp [nextState, merge.Local.output])
            sourceValid resultValid distinct
          intro stack
          apply Reaches.trans (Reaches.single (Step.merge_pc16 ..))
          apply Reaches.trans (Reaches.single (Step.merge_pc15_true _ _ _
            (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)))
          apply Reaches.trans (Reaches.single (Step.merge_pc24 _ _ _ (by simpa [readSource] using sourceValid)))
          apply Reaches.trans (Reaches.single (Step.merge_pc23_false _ _ _
            (by simpa [Heap.read, readSource, readLeft, readRight] using takeLeft)))
          apply Reaches.trans (Reaches.single (Step.merge_pc22 _ _ _
            ⟨by simpa [readSource] using sourceValid, by simpa [readResult] using resultValid⟩))
          apply Reaches.trans (Reaches.single (Step.merge_pc21 ..))
          apply Reaches.trans (Reaches.single (Step.merge_pc18 ..))
          apply Reaches.trans (Reaches.single (Step.merge_pc17 ..))
          have untouched : (heap.write result output (heap.store source right)).store source = heap.store source := by
            funext i; simp [Heap.write, distinct]
          simpa [nextState, Config.heap, interval, mergeValues, List.merge, writeValues,
            readSource, readResult, readLeft, readRight, readOutput, Heap.read, untouched, takeLeft] using next stack
termination_by leftCount + rightCount
decreasing_by all_goals omega

/-- The fresh copy with the merged interval written into it. -/
def mergedHeap (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat) : Heap :=
  writeValues (heap.allocate (heap.store source)) heap.nextRef first
    (mergeValues (interval (heap.store source) first leftCount)
      (interval (heap.store source) (first + (leftCount : Int)) rightCount))

/-- A merge writes exactly the total length of its two input intervals. -/
theorem mergedHeap_clocks (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat) :
    (mergedHeap heap source first leftCount rightCount).clocks "merge_sort" =
      heap.clocks "merge_sort" + (leftCount + rightCount) := by
  simp [mergedHeap, writeValues_clocks]

/-- The source merge terminates and implements mathematical list merge. -/
theorem merge_summary (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat)
    (allocated : source < heap.nextRef) :
    merge.Call heap
      (source, first, first + (leftCount : Int), first + (leftCount : Int) + (rightCount : Int))
      (mergedHeap heap source first leftCount rightCount) heap.nextRef := by
  refine ⟨allocated, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.merge_pc30 ..))
  apply Reaches.trans (Reaches.single (Step.merge_pc29 _ _ _ allocated))
  apply Reaches.trans (Reaches.single (Step.merge_pc28 ..))
  apply Reaches.trans (Reaches.single (Step.merge_pc27 ..))
  apply Reaches.trans (Reaches.single (Step.merge_pc26 ..))
  apply Reaches.trans (Reaches.single (Step.merge_pc25 ..))
  have rest := merge_loop_summary leftCount rightCount
    (.active (heap.allocate (heap.store source))
      (.fn_merge 16 {
        v0 := source, v1 := first, v2 := first + (leftCount : Int),
        v3 := first + (leftCount : Int) + (rightCount : Int),
        v4 := heap.nextRef, v5 := first, v6 := first + (leftCount : Int), v7 := first,
        t13 := heap.nextRef, t14 := source }) stack)
    source heap.nextRef first (first + (leftCount : Int)) first
    True.intro rfl rfl rfl rfl rfl rfl rfl
    (Nat.lt_succ_of_lt allocated) (by simp [Config.heap]) (Nat.ne_of_lt allocated)
  have sourceUnchanged : (heap.allocate (heap.store source)).store source = heap.store source := by
    funext i
    exact Heap.read_allocate_old heap _ source i allocated
  simpa [mergedHeap, Config.heap, sourceUnchanged] using rest stack

/-- Merge changes no existing object, because it writes only into its fresh copy. -/
theorem mergedHeap_extends (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat) :
    Extends heap (mergedHeap heap source first leftCount rightCount) := by
  refine ⟨by simp [mergedHeap], ?_⟩
  intro object allocated
  rw [mergedHeap, writeValues_other _ _ _ _ _ (Nat.ne_of_lt allocated)]
  funext i
  exact Heap.read_allocate_old heap _ object i allocated

/-- The newly returned merge object is allocated. -/
theorem mergedHeap_valid (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat) :
    heap.nextRef < (mergedHeap heap source first leftCount rightCount).nextRef := by
  simp [mergedHeap]

/-- The returned object's interval is precisely the list merge. -/
theorem mergedHeap_interval (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat) :
    interval ((mergedHeap heap source first leftCount rightCount).store heap.nextRef)
      first (leftCount + rightCount) =
    mergeValues (interval (heap.store source) first leftCount)
      (interval (heap.store source) (first + (leftCount : Int)) rightCount) := by
  have length : leftCount + rightCount =
      (mergeValues (interval (heap.store source) first leftCount)
        (interval (heap.store source) (first + (leftCount : Int)) rightCount)).length := by simp
  rw [length]
  exact interval_writeValues _ _ _ _

/-- The fresh copy keeps every value outside the merge interval. -/
theorem mergedHeap_outside (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat)
    (i : Int) (outside : i < first ∨ first + ((leftCount + rightCount : Nat) : Int) ≤ i) :
    (mergedHeap heap source first leftCount rightCount).store heap.nextRef i = heap.store source i := by
  unfold mergedHeap
  rw [writeValues_outside _ _ _ _ _ (by simpa using outside)]
  exact Heap.read_allocate_new heap _ i

/-- Sorted adjacent intervals are merged into one sorted permutation. -/
theorem merge_correct (heap : Heap) (source : SeqRef) (first : Int) (leftCount rightCount : Nat)
    (leftSorted : (interval (heap.store source) first leftCount).Pairwise (· ≤ ·))
    (rightSorted : (interval (heap.store source) (first + (leftCount : Int)) rightCount).Pairwise (· ≤ ·)) :
    SortedPermutation (heap.store source)
      ((mergedHeap heap source first leftCount rightCount).store heap.nextRef)
      first (leftCount + rightCount) := by
  refine ⟨?_, ?_, mergedHeap_outside heap source first leftCount rightCount⟩
  · rw [mergedHeap_interval]
    exact mergeValues_sorted _ _ leftSorted rightSorted
  · rw [mergedHeap_interval, interval_append]
    exact mergeValues_permutation _ _

/-- Sorting the right interval preserves the sorted left interval. Together the
    two calls preserve the full interval's multiset and every outside value. -/
theorem adjacent_sorts (before leftSorted bothSorted : Seq) (first : Int) (leftCount rightCount : Nat)
    (leftResult : SortedPermutation before leftSorted first leftCount)
    (rightResult : SortedPermutation leftSorted bothSorted (first + (leftCount : Int)) rightCount) :
    (interval bothSorted first leftCount).Pairwise (· ≤ ·) ∧
    (interval bothSorted (first + (leftCount : Int)) rightCount).Pairwise (· ≤ ·) ∧
    (interval bothSorted first (leftCount + rightCount)).Perm
      (interval before first (leftCount + rightCount)) ∧
    (∀ i, i < first ∨ first + ((leftCount + rightCount : Nat) : Int) ≤ i → bothSorted i = before i) := by
  have leftUnchanged : interval bothSorted first leftCount = interval leftSorted first leftCount :=
    interval_congr _ _ _ _ (fun i low high => rightResult.2.2 i (Or.inl high))
  have rightOriginal : interval leftSorted (first + (leftCount : Int)) rightCount =
      interval before (first + (leftCount : Int)) rightCount :=
    interval_congr _ _ _ _ (fun i low high => leftResult.2.2 i (Or.inr low))
  refine ⟨by rw [leftUnchanged]; exact leftResult.1, rightResult.1, ?_, ?_⟩
  · rw [interval_append, interval_append, leftUnchanged]
    exact leftResult.2.1.append (by simpa [rightOriginal] using rightResult.2.1)
  · intro i outside
    rw [rightResult.2.2 i (by omega), leftResult.2.2 i (by omega)]

/-- A sequence is already sorted on an interval containing at most one element. -/
theorem short_interval_sorted (a : Seq) (first : Int) (count : Nat) (short : count ≤ 1) :
    SortedPermutation a a first count := by
  refine ⟨?_, List.Perm.refl _, by intros; rfl⟩
  cases count with
  | zero => simp [interval]
  | succ count =>
    have zero : count = 0 := by omega
    subst count
    simp [interval]

/-- Reuse the two recursive sorting calls and the final merge call. -/
theorem split_sort_summary (heap leftHeap rightHeap finalHeap : Heap)
    (source leftObject rightObject result : SeqRef) (lo mid hi : Int)
    (large : 1 < hi - lo) (middle : mid = lo + Int.fdiv (hi - lo) 2)
    (leftCall : merge_sort.Call (heap.tick "merge_sort") (source, lo, mid) leftHeap leftObject)
    (rightCall : merge_sort.Call leftHeap (leftObject, mid, hi) rightHeap rightObject)
    (mergeCall : merge.Call rightHeap (rightObject, lo, mid, hi) finalHeap result)
    (resultValid : result < finalHeap.nextRef) :
    merge_sort.Call heap (source, lo, hi) finalHeap result := by
  refine ⟨leftCall.1, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc22 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc21 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc20_false _ _ _
    (by simp only [decide_eq_false_iff_not]; omega)))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc17 _ _ _ (by decide)))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc16 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc15 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc14 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc13 ..))
  simp only [← middle]
  apply Reaches.trans (leftCall.2 _)
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc12 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc11 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc10 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc9 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc8 ..))
  apply Reaches.trans (rightCall.2 _)
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc7 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc6 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc5 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc4 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc3 ..))
  apply Reaches.trans (Reaches.single (Step.merge_sort_pc2 ..))
  apply Reaches.trans (mergeCall.2 _)
  exact Reaches.single (Step.merge_sort_pc1 _ _ _ resultValid)

/-- The base case preserves all stored values and charges one sorting call. -/
theorem base_case_summary (heap : Heap) (a : SeqRef) (lo hi : Int)
    (allocated : a < heap.nextRef) (short : hi - lo ≤ 1) :
    merge_sort.Call heap (a, lo, hi) (heap.tick "merge_sort") a := by
  refine ⟨allocated, ?_⟩
  intro stack
  apply Exists.intro
  apply Algo2LeanCore.Valid.cons (Step.merge_sort_pc22 _ _ _)
  apply Algo2LeanCore.Valid.cons (Step.merge_sort_pc21 _ _ _)
  apply Algo2LeanCore.Valid.cons (Step.merge_sort_pc20_true _ _ _ (by simpa using short))
  apply Algo2LeanCore.Valid.cons (Step.merge_sort_pc19 _ _ _)
  exact Algo2LeanCore.Valid.cons (Step.merge_sort_pc18 _ _ _ allocated) (.single _)

/-- A base-case execution returns the input reference after its one-unit charge. -/
theorem base_case_execution (heap : Heap) (a : SeqRef) (lo hi : Int)
    (allocated : a < heap.nextRef) (short : hi - lo ≤ 1) :
    merge_sort.Run heap (a, lo, hi) (heap.tick "merge_sort") a := by
  obtain ⟨valid, summary⟩ := base_case_summary heap a lo hi allocated short
  exact ⟨valid, Algo2LeanCore.Summary.root summary⟩

/-- Equality of whole sequences covers all integer positions, including those
    outside the supplied interval. There are no assumptions on the contents. -/
theorem base_case_identity (a : Seq) (lo hi : Int) (short : hi - lo ≤ 1) :
    merge_sort.Returns (a, lo, hi) a := by
  refine ⟨(merge_sort.load (a, lo, hi)).1.tick "merge_sort", 0, ?_, ?_⟩
  · exact base_case_execution _ _ lo hi (by simp [merge_sort.load, Heap.allocate]) short
  · funext i
    simp [merge_sort.load, Heap.allocate]

/-- A singleton is sorted without inspecting or changing its value. -/
theorem singleton_identity (a : Seq) (lo : Int) :
    merge_sort.Returns (a, lo, lo + 1) a :=
  base_case_identity a lo (lo + 1) (by omega)

/-- Empty and reversed intervals also preserve the entire sequence. -/
theorem empty_or_reversed_identity (a : Seq) (lo hi : Int) (empty : hi ≤ lo) :
    merge_sort.Returns (a, lo, hi) a :=
  base_case_identity a lo hi (by omega)


/-- Interval-length induction proves termination and all functional guarantees.
    Every pre-existing heap object is preserved, including the source object. -/
theorem sort_count_cost_summary (count : Nat) (heap : Heap) (source : SeqRef) (first : Int)
    (allocated : source < heap.nextRef) :
    ∃ finalHeap result,
      merge_sort.Call heap (source, first, first + (count : Int)) finalHeap result ∧
      Extends heap finalHeap ∧ result < finalHeap.nextRef ∧
      SortedPermutation (heap.store source) (finalHeap.store result) first count ∧
      finalHeap.clocks "merge_sort" = heap.clocks "merge_sort" + Algo2Lean.MergeSortCost.work count := by
  induction count using Nat.strongRecOn generalizing heap source first with
  | ind count ih =>
    by_cases short : count ≤ 1
    · refine ⟨heap.tick "merge_sort", source, base_case_summary heap source first (first + (count : Int)) allocated (by omega),
        ⟨by simp, by intros; rfl⟩, allocated, short_interval_sorted _ _ _ short, ?_⟩
      simp [Algo2Lean.MergeSortCost.work_base count short]
    · let leftCount := count / 2
      let rightCount := count - leftCount
      have leftSmaller : leftCount < count := by dsimp [leftCount]; omega
      have rightSmaller : rightCount < count := by dsimp [rightCount, leftCount]; omega
      have counts : leftCount + rightCount = count := by dsimp [rightCount, leftCount]; omega
      have endPoint : first + (leftCount : Int) + (rightCount : Int) = first + (count : Int) := by omega
      have midpoint : first + (leftCount : Int) = first + Int.fdiv (first + (count : Int) - first) 2 := by
        rw [show first + (count : Int) - first = (count : Int) by omega]
        exact congrArg (fun x : Int => first + x) (Int.ofNat_fdiv count 2)
      obtain ⟨leftHeap, leftObject, leftCall, leftExtends, leftValid, leftResult, leftCost⟩ :=
        ih leftCount leftSmaller (heap.tick "merge_sort") source first allocated
      obtain ⟨rightHeap, rightObject, rightCall, rightExtends, rightValid, rightResult, rightCost⟩ :=
        ih rightCount rightSmaller leftHeap leftObject (first + (leftCount : Int)) leftValid
      have halves := adjacent_sorts _ _ _ first leftCount rightCount leftResult rightResult
      have merged := merge_correct rightHeap rightObject first leftCount rightCount halves.1 halves.2.1
      refine ⟨mergedHeap rightHeap rightObject first leftCount rightCount, rightHeap.nextRef, ?_,
        (show Extends heap (heap.tick "merge_sort") from ⟨by simp, by intros; rfl⟩).trans
          (leftExtends.trans (rightExtends.trans (mergedHeap_extends _ _ _ _ _))),
        mergedHeap_valid _ _ _ _ _, ?_, ?_⟩
      · exact split_sort_summary heap leftHeap rightHeap _ source leftObject rightObject _ first
          (first + (leftCount : Int)) (first + (count : Int)) (by omega) midpoint leftCall
          (by simpa [endPoint] using rightCall)
          (by simpa [endPoint] using merge_summary rightHeap rightObject first leftCount rightCount rightValid)
          (mergedHeap_valid _ _ _ _ _)
      · rw [← counts]
        refine ⟨merged.1, merged.2.1.trans halves.2.2.1, ?_⟩
        intro i outside
        exact (merged.2.2 i outside).trans (halves.2.2.2 i outside)
      · rw [mergedHeap_clocks, rightCost, leftCost]
        simp only [Heap.clocks_tick_same]
        rw [Algo2Lean.MergeSortCost.work_step count (by omega)]
        dsimp [leftCount, rightCount] at *
        omega

/-- The functional summary is a projection of the shared correctness-and-cost proof. -/
theorem sort_count_summary (count : Nat) (heap : Heap) (source : SeqRef) (first : Int)
    (allocated : source < heap.nextRef) :
    ∃ finalHeap result,
      merge_sort.Call heap (source, first, first + (count : Int)) finalHeap result ∧
      Extends heap finalHeap ∧ result < finalHeap.nextRef ∧
      SortedPermutation (heap.store source) (finalHeap.store result) first count := by
  obtain ⟨finalHeap, result, run, preserved, valid, sorted, _⟩ :=
    sort_count_cost_summary count heap source first allocated
  exact ⟨finalHeap, result, run, preserved, valid, sorted⟩

/-- General signed bounds: every finite interval terminates; reversed intervals
    are interpreted as empty and leave the sequence unchanged. -/
theorem sort_summary (heap : Heap) (source : SeqRef) (lo hi : Int)
    (allocated : source < heap.nextRef) :
    ∃ finalHeap result,
      merge_sort.Call heap (source, lo, hi) finalHeap result ∧
      Extends heap finalHeap ∧ result < finalHeap.nextRef ∧
      SortedPermutation (heap.store source) (finalHeap.store result) lo (hi - lo).toNat := by
  by_cases ordered : lo ≤ hi
  · have endpoint : lo + ((hi - lo).toNat : Int) = hi := by omega
    simpa only [endpoint] using sort_count_summary (hi - lo).toNat heap source lo allocated
  · have empty : (hi - lo).toNat = 0 := by omega
    refine ⟨heap.tick "merge_sort", source, base_case_summary heap source lo hi allocated (by omega),
      ⟨by simp, by intros; rfl⟩, allocated, ?_⟩
    rw [empty]
    exact short_interval_sorted _ _ _ (by omega)

/-- Value-facing total correctness: a sorted permutation exists, and every
    integer position outside the requested interval retains its original value. -/
theorem sort_correct (a : Seq) (lo hi : Int) :
    ∃ result, merge_sort.Returns (a, lo, hi) result ∧
      (interval result lo (hi - lo).toNat).Pairwise (· ≤ ·) ∧
      (interval result lo (hi - lo).toNat).Perm (interval a lo (hi - lo).toNat) ∧
      ∀ i, i < lo ∨ hi ≤ i → result i = a i := by
  let heap := ({} : Heap).allocate a
  obtain ⟨finalHeap, object, summary, preserved, valid, specification⟩ :=
    sort_summary heap 0 lo hi (by simp [heap])
  have original : heap.store 0 = a := by funext i; exact Heap.read_allocate_new {} a i
  have spec : SortedPermutation a (finalHeap.store object) lo (hi - lo).toNat := by
    simpa [original] using specification
  refine ⟨finalHeap.store object, ⟨finalHeap, object, ⟨summary.1, summary.2.root⟩, rfl⟩,
    spec.1, spec.2.1, ?_⟩
  intro i outside
  by_cases ordered : lo ≤ hi
  · exact spec.2.2 i (by omega)
  · have empty : (hi - lo).toNat = 0 := by omega
    exact spec.2.2 i (by rw [empty]; omega)

/-- Individual transitions are deterministic, independently of termination. -/
theorem transitions_deterministic : Deterministic Step :=
  Algo.general_merge_sort.Algo2LeanGenerated.deterministic

/-- Two completed executions from the same input agree on both final heap and
    returned object identity. The theorem does not assume either run terminates
    without its supplied execution proof. -/
theorem execution_unique (heap firstHeap secondHeap : Heap)
    (input firstResult secondResult : SeqRef) (lo hi : Int)
    (first : merge_sort.Run heap (input, lo, hi) firstHeap firstResult)
    (second : merge_sort.Run heap (input, lo, hi) secondHeap secondResult) :
    firstHeap = secondHeap ∧ firstResult = secondResult := by
  have same := Reaches.eq_of_terminal (step := Step)
    transitions_deterministic first.2 second.2
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

/-- Ordinary outputs are equal as whole infinite sequences, at every integer
    position. No interval, sortedness, or termination assumption is needed. -/
theorem output_unique (input firstResult secondResult : Algo2LeanGenerated.Seq)
    (lo hi : Int)
    (first : merge_sort.Returns (input, lo, hi) firstResult)
    (second : merge_sort.Returns (input, lo, hi) secondResult) :
    firstResult = secondResult := by
  obtain ⟨firstHeap, firstReference, firstRun, firstContents⟩ := first
  obtain ⟨secondHeap, secondReference, secondRun, secondContents⟩ := second
  obtain ⟨sameHeap, sameReference⟩ := execution_unique
    (merge_sort.load (input, lo, hi)).1 firstHeap secondHeap
    (merge_sort.load (input, lo, hi)).2.1 firstReference secondReference lo hi
    firstRun secondRun
  subst secondHeap
  subst secondReference
  exact firstContents.symm.trans secondContents


-- Main result: Correctness
/-- Every accepted output is sorted, is a permutation of the input interval,
    and agrees with the input at every integer position outside that interval. -/
theorem every_output_correct (a result : Seq) (lo hi : Int)
    (execution : merge_sort.Returns (a, lo, hi) result) :
    (interval result lo (hi - lo).toNat).Pairwise (· ≤ ·) ∧
    (interval result lo (hi - lo).toNat).Perm (interval a lo (hi - lo).toNat) ∧
    ∀ i, i < lo ∨ hi ≤ i → result i = a i := by
  obtain ⟨expected, run, specification⟩ := sort_correct a lo hi
  have equal := output_unique a result expected lo hi execution run
  simpa only [equal] using specification

/-- Every pair of finite integer bounds has a completed output, including
    negative bounds, empty intervals, and reversed intervals. -/
theorem terminates (a : Seq) (lo hi : Int) :
    ∃ result, merge_sort.Returns (a, lo, hi) result := by
  obtain ⟨result, execution, _⟩ := sort_correct a lo hi
  exact ⟨result, execution⟩

/-- Every completed heap-level execution returns an allocated object and leaves
    every object allocated before the call unchanged, including aliased inputs. -/
theorem execution_preserves_objects (heap finalHeap : Heap) (source result : SeqRef)
    (lo hi : Int) (execution : merge_sort.Run heap (source, lo, hi) finalHeap result) :
    result < finalHeap.nextRef ∧ heap.nextRef ≤ finalHeap.nextRef ∧
    (∀ object, object < heap.nextRef → finalHeap.store object = heap.store object) ∧
    finalHeap.store source = heap.store source := by
  obtain ⟨expectedHeap, expectedResult, summary, preserved, allocated, _⟩ :=
    sort_summary heap source lo hi execution.1
  obtain ⟨sameHeap, sameObject⟩ := execution_unique heap finalHeap expectedHeap source result expectedResult
    lo hi execution ⟨summary.1, summary.2.root⟩
  subst finalHeap
  subst result
  exact ⟨allocated, preserved.1, preserved.2, preserved.2 source execution.1⟩

/-- Heap inputs can share references with other callers; their returned sequence
    is a sorted permutation on the requested interval and preserves every outside value. -/
theorem every_execution_correct (heap finalHeap : Heap) (source result : SeqRef)
    (lo hi : Int) (execution : merge_sort.Run heap (source, lo, hi) finalHeap result) :
    (interval (finalHeap.store result) lo (hi - lo).toNat).Pairwise (· ≤ ·) ∧
    (interval (finalHeap.store result) lo (hi - lo).toNat).Perm
      (interval (heap.store source) lo (hi - lo).toNat) ∧
    ∀ i, i < lo ∨ hi ≤ i → finalHeap.store result i = heap.store source i := by
  obtain ⟨expectedHeap, expectedResult, summary, _, _, specification⟩ :=
    sort_summary heap source lo hi execution.1
  obtain ⟨sameHeap, sameObject⟩ := execution_unique heap finalHeap expectedHeap source result expectedResult
    lo hi execution ⟨summary.1, summary.2.root⟩
  subst finalHeap
  subst result
  refine ⟨specification.1, specification.2.1, ?_⟩
  intro i outside
  by_cases ordered : lo ≤ hi
  · exact specification.2.2 i (by omega)
  · have empty : (hi - lo).toNat = 0 := by omega
    exact specification.2.2 i (by rw [empty]; omega)

/-- Exact operation count: one unit per sort call and merged output element. -/
abbrev runtime : Nat → Nat := Algo2Lean.MergeSortCost.work

/-- A concrete logarithmic envelope, also valid for an empty interval. -/
def runtimeBound (n : Nat) : Nat := 2 * n * (Nat.log2 n + 1) + 1

/-- Correctness and costs arise from the same terminating call, with arbitrary
    initial clocks. Negative-length intervals take the one-unit base case. -/
theorem sort_cost_summary (heap : Heap) (source : SeqRef) (lo hi : Int)
    (allocated : source < heap.nextRef) :
    ∃ finalHeap result, merge_sort.Call heap (source, lo, hi) finalHeap result ∧
      finalHeap.clocks "merge_sort" = heap.clocks "merge_sort" + runtime (hi - lo).toNat := by
  by_cases ordered : lo ≤ hi
  · have endpoint : lo + ((hi - lo).toNat : Int) = hi := by omega
    obtain ⟨finalHeap, result, run, _, _, _, cost⟩ :=
      sort_count_cost_summary (hi - lo).toNat heap source lo allocated
    exact ⟨finalHeap, result, by simpa only [endpoint] using run, cost⟩
  · refine ⟨heap.tick "merge_sort", source, base_case_summary heap source lo hi allocated (by omega), ?_⟩
    have empty : (hi - lo).toNat = 0 := by omega
    simp [empty, runtime]

/-- Every completed execution has the same exact cost as the reusable call.
    Heap.cost subtracts the initial counter, so callers may start with nonzero clocks. -/
theorem execution_cost (heap finalHeap : Heap) (source result : SeqRef) (lo hi : Int)
    (execution : merge_sort.Run heap (source, lo, hi) finalHeap result) :
    Heap.cost heap finalHeap "merge_sort" = runtime (hi - lo).toNat := by
  obtain ⟨expectedHeap, expectedResult, call, cost⟩ :=
    sort_cost_summary heap source lo hi execution.1
  obtain ⟨sameHeap, _⟩ := execution_unique heap finalHeap expectedHeap source result expectedResult
    lo hi execution call.run
  simp [Heap.cost, sameHeap, cost]

/-- Merge sort leaves every other named counter unchanged, enabling callers
    to combine this cost with independently instrumented algorithms. -/
theorem execution_clock_other (heap finalHeap : Heap) (source result : SeqRef) (lo hi : Int)
    (execution : merge_sort.Run heap (source, lo, hi) finalHeap result)
    (name : String) (other : name ≠ "merge_sort") :
    finalHeap.clocks name = heap.clocks name := by
  have resumeSame (h : Heap) (r : Result) (stack : Stack) :
      (resumeConfig h r stack).heap.clocks name = h.clocks name := by cases stack <;> rfl
  have stepSame {before after : Configuration} (transition : Step before after) :
      after.heap.clocks name = before.heap.clocks name := by
    cases transition <;> first | rfl | exact resumeSame _ _ _ | simp [Config.heap, other]
  exact execution.2.invariant (fun state => state.heap.clocks name = heap.clocks name) rfl
    (fun _ _ transition preserved => (stepSame transition).trans preserved)

/-- One reusable call supplies correctness, allocation validity, preservation
    of every old sequence, the exact sorting charge, and unchanged other clocks.
    Base cases may return the input itself; freshness is not claimed. -/
theorem summary (heap : Heap) (source : SeqRef) (lo hi : Int)
    (allocated : source < heap.nextRef) :
    ∃ finalHeap result, merge_sort.Call heap (source, lo, hi) finalHeap result ∧
      Extends heap finalHeap ∧ result < finalHeap.nextRef ∧
      SortedPermutation (heap.store source) (finalHeap.store result) lo (hi - lo).toNat ∧
      Heap.cost heap finalHeap "merge_sort" = runtime (hi - lo).toNat ∧
      (∀ clock, clock ≠ "merge_sort" → finalHeap.clocks clock = heap.clocks clock) := by
  obtain ⟨after, result, call, preserved, valid, sorted⟩ := sort_summary heap source lo hi allocated
  exact ⟨after, result, call, preserved, valid, sorted,
    execution_cost heap after source result lo hi call.run,
    execution_clock_other heap after source result lo hi call.run⟩

/-- The value-facing cost relation records the exact operation count, independent
    of input order and repeated values. -/
theorem output_cost (a result : Seq) (lo hi : Int) (costs : Clocks)
    (execution : merge_sort.ReturnsWithCost (a, lo, hi) result costs) :
    costs "merge_sort" = runtime (hi - lo).toNat := by
  obtain ⟨heap, object, run, _, recorded⟩ := execution
  rw [← recorded]
  exact execution_cost _ heap 0 object lo hi run

-- Main result: Running time
/-- For n = max(hi-lo, 0), every execution charges at most 2n(log₂ n+1)+1
    units. Units count recursive calls and merged output writes; sequence copies
    are abstract constant-time snapshots, and integer bit complexity is excluded. -/
theorem running_time (a result : Seq) (lo hi : Int) (costs : Clocks)
    (execution : merge_sort.ReturnsWithCost (a, lo, hi) result costs) :
    costs "merge_sort" ≤ runtimeBound (hi - lo).toNat := by
  rw [output_cost a result lo hi costs execution]
  exact Algo2Lean.MergeSortCost.work_le_logarithmic _

end GeneralMergeSortAnalysis
