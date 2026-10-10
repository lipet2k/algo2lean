import Algo.callable_direct.Generated
import Algo.callable_direct.Facts

/-!
Analysis outline:
- `summary`: Reusable successor and exact-cost contract.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.callable_direct

namespace CallableDirectAnalysis

/-- An ordinary function theorem, with no knowledge of callable adapters. -/
theorem summary (heap : Heap) (value : Int) :
    successor.Call heap value (heap.tick "callable_work") (value + 1) := by
  open Algo.callable_direct.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro caller
    apply Reaches.prepend (Step.successor_pc3 _ _ caller)
    apply Reaches.prepend (Step.successor_pc2 _ _ caller)
    exact Reaches.single (Step.successor_pc1 _ _ caller)

end CallableDirectAnalysis
