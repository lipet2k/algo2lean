import Algo.increment.Generated
import Algo.increment.Facts
import Algo.counter.Analysis

/-!
Analysis outline:
- `summary`: Reusable abstract-counter increment contract.
- `correct`: Increment correctness for every execution.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.counter Algo.increment

namespace IncrementAnalysis

/-- The client calls the two public operations; it knows no counter layout. -/
theorem calls (dependencies : Dependencies) {before middle after : Heap}
    {ref : ObjectRef} {value : Int}
    (read : Counter.get.Call dependencies.Counter before ref middle value)
    (write : Counter.put.Call dependencies.Counter middle (ref, value + 1) after ()) :
    increment.Call dependencies before ref after (value + 1) := by
  open Algo.increment.Algo2LeanGenerated in
    refine ⟨read.1, ?_⟩
    intro caller
    apply Reaches.prepend (Step.increment_pc10 _ _ caller)
    apply Reaches.prepend (Step.increment_pc9 _ _ caller (by exact read.1))
    apply Reaches.prepend (Step.increment_pc8 _ _ caller)
    apply (ModuleCall.summary (interface_Counter_simulates dependencies) _ caller read.2).trans
    apply Reaches.prepend (Step.increment_pc7 _ _ caller)
    apply Reaches.prepend (Step.increment_pc6 _ _ caller)
    apply Reaches.prepend (Step.increment_pc5 _ _ caller (by exact write.1))
    apply Reaches.prepend (Step.increment_pc4 _ _ caller)
    apply Reaches.prepend (Step.increment_pc3 _ _ caller)
    apply (ModuleCall.summary (interface_Counter_simulates dependencies) _ caller write.2).trans
    apply Reaches.prepend (Step.increment_pc2 _ _ caller)
    exact Reaches.single (Step.increment_pc1 _ _ caller)

/-- Increment terminates, stores the incremented value, and sums the read/write
    costs supplied by the counter contract, independently of its representation. -/
theorem summary (dependencies : Dependencies) (contract : CounterContract dependencies.Counter)
    {before : Heap} {ref : ObjectRef} {value : Int}
    (represented : contract.Represents before ref value) :
    ∃ after, increment.Call dependencies before ref after (value + 1) ∧
      contract.Represents after ref (value + 1) ∧
      before.Increments after (Clocks.single "counter_work" (contract.readCost + contract.writeCost)) := by
  obtain ⟨middle, read, unchanged, readCost⟩ := contract.read represented
  obtain ⟨after, write, updated, writeCost⟩ := contract.write (value + 1) unchanged
  refine ⟨after, calls dependencies read write, updated, ?_⟩
  have cost := readCost.trans writeCost
  intro clock
  have effect := cost clock
  by_cases same : clock = "counter_work" <;>
    simpa [Clocks.add, Clocks.single, same] using effect

-- Main result: Correctness and running time
/-- Optional uniqueness evidence extends the constructive law to every completed
    execution. The statement uses the public execution relation. -/
theorem correct (dependencies : Dependencies) (facts : DependencyFacts dependencies)
    (contract : CounterContract dependencies.Counter)
    {before after : Heap} {ref : ObjectRef} {value output : Int}
    (represented : contract.Represents before ref value)
    (execution : increment.Run dependencies before ref after output) :
    output = value + 1 ∧ contract.Represents after ref (value + 1) ∧
      before.Increments after (Clocks.single "counter_work" (contract.readCost + contract.writeCost)) := by
  obtain ⟨finalHeap, run, updated, cost⟩ := summary dependencies contract represented
  obtain ⟨rfl, rfl⟩ := increment.Run.eq_of_call facts execution run
  exact ⟨rfl, updated, cost⟩

end IncrementAnalysis
