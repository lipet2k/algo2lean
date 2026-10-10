import Algo.twice.Generated
import Algo.twice.Facts
import Algo.increment.Analysis

/-!
Analysis outline:
- `summary`: Reusable two-increment contract.
- `output_cost`: Two increments and exact cost.
-/

open Algo2LeanCore Algo2LeanGenerated
open Algo.twice

namespace TwiceAnalysis

/-- Two imported increment calls return the input plus two and add their exact
    clock charges. The resulting call contract can be reused by other modules. -/
theorem summary (heap : Heap) (value : Int) :
    twice.Call heap value (heap.tick "increments" 2) (value + 2) := by
  suffices calls : twice.Call heap value
      ((heap.tick "increments").tick "increments") ((value + 1) + 1) by
    simpa [Heap.tick_add, Int.add_assoc] using calls
  open Algo.twice.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro caller
    apply Reaches.prepend (Step.twice_pc6 _ _ caller)
    apply Reaches.prepend (Step.twice_pc5 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller
      (IncrementAnalysis.summary heap value).2).trans
    apply Reaches.prepend (Step.twice_pc4 _ _ caller)
    apply Reaches.prepend (Step.twice_pc3 _ _ caller)
    apply Reaches.prepend (Step.twice_pc2 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller
      (IncrementAnalysis.summary (heap.tick "increments") (value + 1)).2).trans
    exact Reaches.single (Step.twice_pc1 _ _ caller)

-- Main result: Correctness and running time
theorem output_cost (value : Int) :
    twice.ReturnsWithCost value (value + 2) (Clocks.single "increments" 2) := by
  refine ⟨({} : Heap).tick "increments" 2, (summary {} value).run, ?_⟩
  change Heap.cost ({} : Heap) (({} : Heap).tick "increments" 2) = _
  rw [← Heap.charge_single, Heap.cost_charge]

end TwiceAnalysis
