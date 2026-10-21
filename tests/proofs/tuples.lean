open Algo2LeanCore Algo2LeanGenerated

-- Tuple fields and typed sequence elements round-trip through mutable storage.
example : stored_values.Returns () 9 := by
  unfold stored_values.Returns
  algo_steps

-- Repeating a reference in a tuple preserves the shared sequence/object identity.
example : shared_sequences.Returns () 7 := by
  unfold shared_sequences.Returns
  algo_steps

example : shared_objects.Returns () 8 := by
  unfold shared_objects.Returns
  algo_steps

example : stored_aliases.Returns () 20 := by
  unfold stored_aliases.Returns
  algo_steps

-- Tuple entries run left to right; the unpacked function call runs exactly once.
def evaluationCosts : Clocks := fun name =>
  if name = "entries" then 2 else if name = "pairs" then 1 else 0

def evaluationHeap : Heap :=
  let cell := create_Cell ({} : Heap) 0
  let heap := set_Cell_value (cell.1.tick "pairs") cell.2 1
  let heap := set_Cell_value (heap.tick "entries") cell.2 12
  heap.tick "entries"

example : evaluation_order.ReturnsWithCost () (1, 12, 12) evaluationCosts := by
  refine ⟨evaluationHeap, ?_, ?_⟩
  · unfold evaluationHeap
    algo_steps
  · funext name
    by_cases entries : name = "entries"
    · simp [evaluationCosts, evaluationHeap, evaluation_order.load, create_Cell, set_Cell_value,
        Heap.cost, Heap.tick, entries]
    · by_cases pairs : name = "pairs" <;>
        simp [evaluationCosts, evaluationHeap, evaluation_order.load, create_Cell, set_Cell_value,
          Heap.cost, Heap.tick, entries, pairs]

-- Both right-hand values are captured before either unpacked name is overwritten.
example : swap.Returns () (2, 1) := by
  unfold swap.Returns
  algo_steps

example : shapes.Returns () 11 := by
  unfold shapes.Returns
  algo_steps

-- A null entry remains null; it cannot become a fabricated reference to object zero.
example : nullable_entry.Returns (({} : Heap), none) (({} : Heap), (none, 3)) := by
  unfold nullable_entry.Returns
  algo_steps
