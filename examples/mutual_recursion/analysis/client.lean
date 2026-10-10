import Algo.client.Generated
import Algo.client.Facts
import Algo.parity.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
The client imports one function from a mutually recursive source group.
Its proof reuses the group's call theorem without examining either recursive
function's transitions or repeating their simultaneous induction.
-/

open Algo2LeanCore _root_.Algo2LeanGenerated Algo.client

namespace ParityClientAnalysis

/-- The client preserves the imported function's output and exact heap effect. -/
theorem call (heap : Heap) (n : Nat) :
    classify.Call heap (n : Int) (heap.tick "work" (2 * (n + 1)))
      (ParityAnalysis.evenValue n) := by
  open Algo.client.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro stack
    apply Reaches.prepend (Step.classify_pc3 ..)
    apply Reaches.prepend (Step.classify_pc2 ..)
    apply (ModuleCall.summary import_0_simulates _ stack
      (ParityAnalysis.calls heap n).1.2).trans
    exact Reaches.single (Step.classify_pc1 ..)

-- Main result: Correctness
/-- Every completed client run agrees with the imported parity specification. -/
theorem correct (heap final : Heap) (n : Nat) (output : Bool)
    (execution : classify.Run heap (n : Int) final output) :
    final = heap.tick "work" (2 * (n + 1)) ∧ output = ParityAnalysis.evenValue n :=
  classify.Run.eq_of_call execution (call heap n)

-- Main result: Running time
/-- The client adds no ticks; its exact cost is the imported parity call's cost. -/
theorem output_cost (n : Nat) :
    classify.ReturnsWithCost (n : Int) (ParityAnalysis.evenValue n)
      (Clocks.single "work" (2 * (n + 1))) := by
  refine ⟨({} : Heap).tick "work" (2 * (n + 1)), (call {} n).run, ?_⟩
  change Heap.cost ({} : Heap) (({} : Heap).tick "work" (2 * (n + 1))) = _
  rw [← Heap.charge_single, Heap.cost_charge]

end ParityClientAnalysis
