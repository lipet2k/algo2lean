import Algo.consumer.advance_twice.Generated
import Algo.consumer.advance_twice.Facts
import Algo.use_direct.Analysis

/-!
Analysis outline:
- `summary`: Reusable two-increment contract.
- `correct`: Two-increment correctness.
-/

open Algo2LeanCore _root_.Algo2LeanGenerated Algo.consumer.advance_twice

namespace CounterConsumerAnalysis

/-- A linked generic component is an ordinary reusable call to its next client. -/
theorem calls {before middle after : Heap} {counter : ObjectRef} {first second : Int}
    (one : Algo.use_direct.advance.Call before counter middle first)
    (two : Algo.use_direct.advance.Call middle counter after second) :
    advance_twice.Call before counter after second := by
  open Algo.consumer.advance_twice.Algo2LeanGenerated in
    refine ⟨one.1, ?_⟩
    intro caller
    apply Reaches.prepend (Step.advance_twice_pc5 _ _ caller)
    apply Reaches.prepend (Step.advance_twice_pc4 _ _ caller)
    apply (ModuleCall.summary import_3_simulates _ caller one.2).trans
    apply Reaches.prepend (Step.advance_twice_pc3 _ _ caller)
    apply Reaches.prepend (Step.advance_twice_pc2 _ _ caller)
    apply (ModuleCall.summary import_3_simulates _ caller two.2).trans
    exact Reaches.single (Step.advance_twice_pc1 _ _ caller)

/-- Repeated calls share one object and its postcondition. The client neither
    reopens its implementation nor resets its clocks or represented state. -/
theorem summary {before : Heap} {counter : ObjectRef} {value : Int}
    (represented : DirectAnalysis.Represents before counter value) :
    ∃ after, advance_twice.Call before counter after (value + 2) ∧
      DirectAnalysis.Represents after counter (value + 2) ∧
      before.Increments after (Clocks.single "counter_work" 4) := by
  obtain ⟨middle, first, advanced, firstCost⟩ := DirectClientAnalysis.summary represented
  obtain ⟨after, second, advancedAgain, secondCost⟩ := DirectClientAnalysis.summary advanced
  have result : (value + 1) + 1 = value + 2 := by omega
  have budget : Clocks.add (Clocks.single "counter_work" 2) (Clocks.single "counter_work" 2) =
      Clocks.single "counter_work" 4 := by
    funext clock
    by_cases same : clock = "counter_work" <;> simp [Clocks.add, Clocks.single, same]
  refine ⟨after, ?_, ?_, ?_⟩
  · simpa only [result] using calls first second
  · simpa only [result] using advancedAgain
  · simpa only [budget] using firstCost.trans secondCost

-- Main result: Correctness and running time
/-- The application-facing statement mentions just represented values,
    the concrete execution, and its clock increments. -/
theorem correct {before after : Heap} {counter : ObjectRef} {value output : Int}
    (represented : DirectAnalysis.Represents before counter value)
    (execution : advance_twice.Run before counter after output) :
    output = value + 2 ∧ DirectAnalysis.Represents after counter (value + 2) ∧
      before.Increments after (Clocks.single "counter_work" 4) := by
  obtain ⟨finalHeap, call, updated, cost⟩ := summary represented
  obtain ⟨rfl, rfl⟩ := advance_twice.Run.eq_of_call execution call
  exact ⟨rfl, updated, cost⟩

end CounterConsumerAnalysis
