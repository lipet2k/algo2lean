import Algo.use_direct.Generated
import Algo.use_direct.Facts
import Algo.direct.Analysis
import Algo.increment.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable concrete-counter increment contract.
- `correct`: Concrete-counter increment correctness.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.use_direct

namespace DirectClientAnalysis

/-- A small adapter applies the existing backend proofs; no backend transition
    rules or storage details occur in this linking proof. -/
def contract : CounterContract Direct_as_Counter where
  Represents := DirectAnalysis.Represents
  readCost := 1
  writeCost := 1
  valid := by
    intro heap ref value represented
    simpa [Direct_as_Counter] using represented.1
  read := by
    intro heap ref value represented
    obtain ⟨after, run, same, cost, frame⟩ := DirectAnalysis.read represented
    exact ⟨after, Direct_as_Counter_summary_get run, same, cost, frame⟩
  write := by
    intro heap ref old value represented
    obtain ⟨after, run, updated, cost, frame⟩ := DirectAnalysis.write value represented
    exact ⟨after, Direct_as_Counter_summary_put run, updated, cost, frame⟩

/-- Only the wrapper's own call boundary needs a local execution proof. -/
theorem call {before after : Heap} {ref : ObjectRef} {output : Int}
    (valid : Algo.direct.Algo2LeanGenerated.is_Direct before ref)
    (run : Algo.increment.increment.Call use_increment_0 before ref after output) :
    advance.Call before ref after output := by
  open Algo.use_direct.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.advance_pc3 _ _ caller)
    apply Reaches.prepend (Step.advance_pc2 _ _ caller)
    apply (ModuleCall.summary import_2_use_increment_0_simulates _ caller run.2).trans
    exact Reaches.single (Step.advance_pc1 _ _ caller)

/-- The original generic analysis supplies both the result and runtime law. -/
theorem summary {before : Heap} {ref : ObjectRef} {value : Int}
    (represented : DirectAnalysis.Represents before ref value) :
    ∃ after, advance.Call before ref after (value + 1) ∧
      DirectAnalysis.Represents after ref (value + 1) ∧
      before.Increments after (Clocks.single "counter_work" 2) ∧
      before.Modifies after [] [ref] := by
  obtain ⟨after, run, updated, cost, frame⟩ :=
    IncrementAnalysis.summary use_increment_0 contract represented
  exact ⟨after, call represented.1 run, updated, cost, frame⟩

-- Main result: Correctness and running time
/-- Every concrete execution has the proved value, mutation, and cost. There
    are no unproved generic-contract assumptions in this theorem. -/
theorem correct {before after : Heap} {ref : ObjectRef} {value output : Int}
    (represented : DirectAnalysis.Represents before ref value)
    (execution : advance.Run before ref after output) :
    output = value + 1 ∧ DirectAnalysis.Represents after ref (value + 1) ∧
      before.Increments after (Clocks.single "counter_work" 2) ∧
      before.Modifies after [] [ref] := by
  obtain ⟨finalHeap, run, updated, cost, frame⟩ := summary represented
  obtain ⟨rfl, rfl⟩ := execution.eq_of_call run
  exact ⟨rfl, updated, cost, frame⟩

end DirectClientAnalysis
