-- A nonconstant infinite input: only positions 0 and 1 need sorting.
def swapInput : Algo2LeanGenerated.Seq :=
  fun i => if i = 0 then 2 else if i = 1 then 1 else i * 1000 + 9

def swapOutput : Algo2LeanGenerated.Seq :=
  fun i => if i = 1 then 2 else if i = 0 then 1 else swapInput i

def swapInitialHeap : Heap := ({} : Heap).allocate swapInput
def swapFinalHeap : Heap :=
  let calls := ((swapInitialHeap.tick "merge_sort").tick "merge_sort").tick "merge_sort"
  ((((calls.allocate swapInput).write 1 0 1).tick "merge_sort").write 1 1 2).tick "merge_sort"

-- Sorting interval [0, 2) returns fresh reference 1 with the swapped contents
-- recorded in swapFinalHeap.
theorem merge_sort_two_elements_execution :
    merge_sort.Run swapInitialHeap (0, 0, 2) swapFinalHeap 1 := by
  unfold merge_sort.Run
  algo_steps

-- The value-view proposition projects the returned object's final contents.
theorem merge_sort_two_elements :
    merge_sort.Returns (swapInput, 0, 2) swapOutput := by
  unfold merge_sort.Returns
  refine ⟨swapFinalHeap, 1, merge_sort_two_elements_execution, ?_⟩
  funext i
  simp [swapFinalHeap, swapInitialHeap, Heap.write, Heap.allocate, swapOutput]

theorem merge_sort_two_elements_sorted : swapOutput 0 = 1 ∧ swapOutput 1 = 2 := by
  decide

-- Copying also preserves the original object in the final heap.
theorem merge_sort_two_elements_preserves_input_object (i : Int) :
    swapFinalHeap.read 0 i = swapInput i := by
  simp [swapFinalHeap, swapInitialHeap, Heap.read, Heap.write, Heap.allocate]

-- Sorting interval [0, 2) preserves every integer index outside that interval.
theorem merge_sort_two_elements_preserves_outside (i : Int)
    (outside : i < 0 ∨ 2 ≤ i) : swapOutput i = swapInput i := by
  have not_zero : i ≠ 0 := by omega
  have not_one : i ≠ 1 := by omega
  simp [swapOutput, not_zero, not_one]

-- Three sorting calls and two merged writes give five units of measured work.
theorem merge_sort_two_elements_cost :
    Heap.cost swapInitialHeap swapFinalHeap "merge_sort" = 5 := by decide
