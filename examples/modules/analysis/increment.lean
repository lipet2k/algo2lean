import Algo.increment.Generated
import Algo.increment.Facts
import Algo2LeanLib.CallCost

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable increment contract.
- `output_cost`: Increment result and exact cost.
-/

open Algo2LeanCore Algo2LeanGenerated
open Algo.increment

namespace IncrementAnalysis

/-- The increment contract works inside any caller and starts from its actual
    heap: the existing counters and all program data are retained. -/
theorem summary (heap : Heap) (value : Int) :
    increment.Call heap value (heap.tick "increments") (value + 1) := by
  open Algo.increment.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro caller
    apply Reaches.prepend (Step.increment_pc3 _ _ caller)
    apply Reaches.prepend (Step.increment_pc2 _ _ caller)
    exact Reaches.single (Step.increment_pc1 _ _ caller)

-- Main result: Correctness and running time
/-- The result and cost are witnessed by one completed execution. -/
theorem output_cost (value : Int) :
    increment.ReturnsWithCost value (value + 1) (Clocks.single "increments" 1) := by
  refine ⟨({} : Heap).tick "increments", (summary {} value).run, ?_⟩
  change Heap.cost ({} : Heap) (({} : Heap).tick "increments") = _
  rw [← Heap.charge_single, Heap.cost_charge]

end IncrementAnalysis
