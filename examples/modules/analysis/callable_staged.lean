import Algo.callable_staged.Generated
import Algo.callable_staged.Facts

/-!
Analysis outline:
- `summary`: Reusable successor and exact-cost contract.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.callable_staged

namespace CallableStagedAnalysis

/-- The staged successor returns the input plus one and charges two units of
    `callable_work`. The contract applies independently of any callable adapter. -/
theorem summary (heap : Heap) (value : Int) :
    successor.Call heap value (heap.tick "callable_work" 2) (value + 1) := by
  open Algo.callable_staged.Algo2LeanGenerated in
    have result : value + 2 - 1 = value + 1 := by omega
    refine ⟨trivial, ?_⟩
    intro caller
    apply Reaches.prepend (Step.successor_pc4 _ _ caller)
    apply Reaches.prepend (Step.successor_pc3 _ _ caller)
    apply Reaches.prepend (Step.successor_pc2 _ _ caller)
    simpa only [result] using Reaches.single
      (Step.successor_pc1 (heap.tick "callable_work" 2)
        { v0 := value, v1 := value + 2, t2 := value + 2 - 1 } caller)

end CallableStagedAnalysis
