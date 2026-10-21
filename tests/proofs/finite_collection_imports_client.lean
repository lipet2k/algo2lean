import Algo.client.Generated
import Algo.helper.Analysis

open Algo2LeanCore Algo2LeanGenerated

namespace FiniteClient

/-- The client uses the imported call contract and a typed lookup law. -/
theorem run_call (heap : Heap) (values : CollectionRef) (key value : Int)
    (valid : Algo.client.run.ValidInput heap (values, key, value)) :
    Algo.client.run.Call heap (values, key, value)
      (Algo.client.Algo2LeanGenerated.«dict[Int, Int]».set heap values key value) value := by
  open Algo.client.Algo2LeanGenerated in
    have updated := DictType.valid_set «dict[Int, Int]» heap values key value valid
    have lookup := DictType.get_set_same «dict[Int, Int]» heap values key value valid
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.run_pc6 _ _ caller)
    apply Reaches.prepend (Step.run_pc5 _ _ caller)
    apply Reaches.prepend (Step.run_pc4 _ _ caller)
    apply Reaches.prepend (Step.run_pc3 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller
      (FiniteHelper.put_call heap values key value valid).2).trans
    rw [show Algo.helper.Algo2LeanGenerated.«dict[Int, Int]» = «dict[Int, Int]» from rfl]
    apply Reaches.prepend (Step.run_pc2 _ _ caller ⟨updated, by simp [lookup]⟩)
    rw [lookup]
    exact Reaches.single (Step.run_pc1 _ _ caller)

end FiniteClient
