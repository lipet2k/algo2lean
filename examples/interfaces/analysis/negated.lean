import Algo.negated.Generated
import Algo2LeanLib.CallCost
import Algo2LeanLib.HeapFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `read`: Reusable counter-read contract.
- `write`: Reusable counter-write contract.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.negated Algo.negated.Algo2LeanGenerated

namespace NegatedAnalysis

/-- The representation is private to this backend; the generic client does
    not depend on its storage field or encoding. -/
def Represents (heap : Heap) (ref : ObjectRef) (value : Int) : Prop :=
  is_Negated heap ref ∧ field_Negated_opposite heap ref = some (-value)

/-- Reading terminates and preserves the represented value and all other data. -/
theorem read_summary {heap : Heap} {ref : ObjectRef} {value : Int}
    (represented : Represents heap ref value) :
    Negated.get.Call heap ref (heap.tick "counter_work" 2) value := by
  have observed : field_Negated_opposite (heap.tick "counter_work" 2) ref = some (-value) := by
    simpa [field_Negated_opposite, is_Negated, Heap.tick, Heap.charge] using! represented.2
  refine ⟨represented.1, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Negated_get_pc3 _ _ caller)
  apply Reaches.prepend (Step.Negated_get_pc2 _ _ caller (by simp [observed]))
  simpa [observed] using
    (Reaches.single (Step.Negated_get_pc1 (heap.tick "counter_work" 2)
      ({ v0 := ref, t1 := value } : State_Negated_get) caller))

theorem read {heap : Heap} {ref : ObjectRef} {value : Int}
    (represented : Represents heap ref value) :
    ∃ after, Negated.get.Call heap ref after value ∧ Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" 2) ∧
      heap.Modifies after [] [ref] := by
  refine ⟨heap.tick "counter_work" 2, read_summary represented, ?_, ?_, ?_⟩
  · simpa [Represents, field_Negated_opposite, is_Negated, Heap.tick, Heap.charge] using! represented
  · simpa only [Heap.charge_single] using
      Heap.Increments.charge heap (Clocks.single "counter_work" 2)
  · exact (Heap.Modifies.refl heap [] [ref]).tick "counter_work" 2

/-- Writing exposes a postcondition another call can consume, with the same
    clocks and heap effects as the original compiled operation. -/
theorem write_summary {heap : Heap} {ref : ObjectRef} (value : Int)
    (valid : is_Negated heap ref) :
    Negated.put.Call heap (ref, value)
      (set_Negated_opposite (heap.tick "counter_work" 2) ref (-value)) () := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Negated_put_pc4 _ _ caller)
  apply Reaches.prepend (Step.Negated_put_pc3 _ _ caller (by
    simpa [is_Negated, Heap.tick, Heap.charge] using! valid))
  apply Reaches.prepend (Step.Negated_put_pc2 _ _ caller)
  exact Reaches.single (Step.Negated_put_pc1 _ _ caller)

theorem write {heap : Heap} {ref : ObjectRef} {old : Int} (value : Int)
    (represented : Represents heap ref old) :
    ∃ after, Negated.put.Call heap (ref, value) after () ∧ Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" 2) ∧
      heap.Modifies after [] [ref] := by
  refine ⟨set_Negated_opposite (heap.tick "counter_work" 2) ref (-value),
    write_summary value represented.1, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [is_Negated, set_Negated_opposite, Heap.tick, Heap.charge] using! represented.1
    · apply field_Negated_opposite_set
      simpa [is_Negated, Heap.tick, Heap.charge] using! represented.1
  · intro clock
    by_cases same : clock = "counter_work" <;>
      simp [set_Negated_opposite, Heap.writeField, Heap.tick, Clocks.single, same]
  · exact ((Heap.Modifies.refl heap [] [ref]).tick "counter_work" 2).writeField
      ref "opposite" (.intValue (-value)) (by simp)

end NegatedAnalysis
