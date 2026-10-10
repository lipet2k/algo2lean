import Algo.direct.Generated
import Algo2LeanLib.CallCost

/-!
Analysis outline:
- `read`: Reusable counter-read contract.
- `write`: Reusable counter-write contract.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.direct Algo.direct.Algo2LeanGenerated

namespace DirectAnalysis

/-- The representation is private to this backend; the generic client does
    not depend on its storage field or encoding. -/
def Represents (heap : Heap) (ref : ObjectRef) (value : Int) : Prop :=
  is_Direct heap ref ∧ field_Direct_value heap ref = some (value)

/-- Reading terminates and preserves the represented value and all other data. -/
theorem read_summary {heap : Heap} {ref : ObjectRef} {value : Int}
    (represented : Represents heap ref value) :
    Direct.get.Call heap ref (heap.tick "counter_work" 1) value := by
  have observed : field_Direct_value (heap.tick "counter_work" 1) ref = some (value) := by
    simpa [field_Direct_value, is_Direct, Heap.tick, Heap.charge] using represented.2
  refine ⟨represented.1, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Direct_get_pc3 _ _ caller)
  apply Reaches.prepend (Step.Direct_get_pc2 _ _ caller (by simp [observed]))
  simpa [observed] using
    (Reaches.single (Step.Direct_get_pc1 (heap.tick "counter_work" 1)
      ({ v0 := ref, t1 := value } : State_Direct_get) caller))

theorem read {heap : Heap} {ref : ObjectRef} {value : Int}
    (represented : Represents heap ref value) :
    ∃ after, Direct.get.Call heap ref after value ∧ Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" 1) := by
  refine ⟨heap.tick "counter_work" 1, read_summary represented, ?_, ?_⟩
  · simpa [Represents, field_Direct_value, is_Direct, Heap.tick, Heap.charge] using represented
  · simpa only [Heap.charge_single] using
      Heap.Increments.charge heap (Clocks.single "counter_work" 1)

/-- Writing exposes a postcondition another call can consume, with the same
    clocks and heap effects as the original compiled operation. -/
theorem write_summary {heap : Heap} {ref : ObjectRef} (value : Int)
    (valid : is_Direct heap ref) :
    Direct.put.Call heap (ref, value)
      (set_Direct_value (heap.tick "counter_work" 1) ref (value)) () := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Direct_put_pc4 _ _ caller)
  apply Reaches.prepend (Step.Direct_put_pc3 _ _ caller (by
    simpa [is_Direct, Heap.tick, Heap.charge] using valid))
  apply Reaches.prepend (Step.Direct_put_pc2 _ _ caller)
  exact Reaches.single (Step.Direct_put_pc1 _ _ caller)

theorem write {heap : Heap} {ref : ObjectRef} {old : Int} (value : Int)
    (represented : Represents heap ref old) :
    ∃ after, Direct.put.Call heap (ref, value) after () ∧ Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" 1) := by
  refine ⟨set_Direct_value (heap.tick "counter_work" 1) ref (value),
    write_summary value represented.1, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [is_Direct, set_Direct_value, Heap.tick, Heap.charge] using represented.1
    · apply field_Direct_value_set
      simpa [is_Direct, Heap.tick, Heap.charge] using represented.1
  · intro clock
    by_cases same : clock = "counter_work" <;>
      simp [set_Direct_value, Heap.writeField, Heap.tick, Clocks.single, same]

end DirectAnalysis
