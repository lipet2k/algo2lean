import Algo.integer.Generated

open Algo2LeanCore Algo2LeanGenerated

namespace IntegerHelper
open Algo.integer.Algo2LeanGenerated

/-- A Std-only contract describes the exact sequence mutation and clock increment. -/
theorem increment_call (heap : Heap) (ref : SeqRef) (index : Int)
    (valid : Algo.integer.increment.ValidInput heap (ref, index)) :
    Algo.integer.increment.Call heap (ref, index)
      ((heap.write ref index (heap.read ref index + 1)).tick "work")
      (heap.read ref index + 1) := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.increment_pc4 heap { v0 := ref, v1 := index } caller ⟨valid, valid⟩)
  apply Reaches.prepend (Step.increment_pc3 _ _ caller)
  apply Reaches.prepend (Step.increment_pc2
    ((heap.write ref index (heap.read ref index + 1)).tick "work")
    { v0 := ref, v1 := index } caller valid)
  simpa [Heap.read, Heap.write, Heap.tick] using
    Reaches.single (Step.increment_pc1
      ((heap.write ref index (heap.read ref index + 1)).tick "work")
      { v0 := ref, v1 := index, t2 := heap.read ref index + 1 } caller)

end IntegerHelper
