import Algo.pipeline.Generated
import Algo.pipeline.Facts
import Algo.twice.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable four-increment contract.
- `correct`: Pipeline correctness.
- `output_cost`: Pipeline result and exact costs.
-/

open Algo2LeanCore Algo2LeanGenerated
open Algo.pipeline

namespace PipelineAnalysis

/-- The grandcaller imports the already-proved caller. It never unfolds the
    increment implementation or repeats its correctness or runtime proof. -/
theorem summary (heap : Heap) (value : Int) :
    advance_four.Call heap value
      ((heap.tick "batches").tick "increments" 4) (value + 4) := by
  suffices calls : advance_four.Call heap value
      (((heap.tick "batches").tick "increments" 2).tick "increments" 2) ((value + 2) + 2) by
    simpa [Heap.tick_add, Int.add_assoc] using calls
  open Algo.pipeline.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro caller
    apply Reaches.prepend (Step.advance_four_pc7 _ _ caller)
    apply Reaches.prepend (Step.advance_four_pc6 _ _ caller)
    apply Reaches.prepend (Step.advance_four_pc5 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller
      (TwiceAnalysis.summary (heap.tick "batches") value).2).trans
    apply Reaches.prepend (Step.advance_four_pc4 _ _ caller)
    apply Reaches.prepend (Step.advance_four_pc3 _ _ caller)
    apply Reaches.prepend (Step.advance_four_pc2 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller
      (TwiceAnalysis.summary ((heap.tick "batches").tick "increments" 2) (value + 2)).2).trans
    exact Reaches.single (Step.advance_four_pc1 _ _ caller)

/-- Two named counters compose without assuming either started at zero. -/
theorem execution_cost (heap : Heap) (value : Int) :
    ∃ after, advance_four.Run heap value after (value + 4) ∧
      heap.Increments after (Clocks.add (Clocks.single "batches" 1) (Clocks.single "increments" 4)) := by
  refine ⟨(heap.tick "batches").tick "increments" 4,
    (summary heap value).run, ?_⟩
  simpa only [Heap.charge_single] using
    (Heap.Increments.charge heap (Clocks.single "batches" 1)).trans
      (Heap.Increments.charge (heap.charge (Clocks.single "batches" 1)) (Clocks.single "increments" 4))

-- Main result: Correctness and running time
/-- Every completed execution has the proved result and exact clock effects.
    The optional Facts module composes determinism across both import layers. -/
theorem correct {heap after : Heap} {value output : Int}
    (execution : advance_four.Run heap value after output) :
    output = value + 4 ∧
      heap.Increments after (Clocks.add (Clocks.single "batches" 1) (Clocks.single "increments" 4)) := by
  obtain ⟨finalHeap, result⟩ := execution.eq_of_call (summary heap value)
  refine ⟨result, ?_⟩
  rw [finalHeap]
  simpa only [Heap.charge_single] using
    (Heap.Increments.charge heap (Clocks.single "batches" 1)).trans
      (Heap.Increments.charge (heap.charge (Clocks.single "batches" 1)) (Clocks.single "increments" 4))

theorem output_cost (value : Int) :
    advance_four.ReturnsWithCost value (value + 4)
      (Clocks.add (Clocks.single "batches" 1) (Clocks.single "increments" 4)) := by
  obtain ⟨after, execution, effect⟩ := execution_cost {} value
  exact ⟨after, execution, effect.cost⟩

end PipelineAnalysis
