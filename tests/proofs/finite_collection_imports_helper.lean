import Algo.helper.Generated

open Algo2LeanCore Algo2LeanGenerated

namespace FiniteHelper

/-- Updating one entry is a reusable call contract over the caller's actual heap. -/
theorem put_call (heap : Heap) (values : CollectionRef) (key value : Int)
    (valid : Algo.helper.put.ValidInput heap (values, key, value)) :
    Algo.helper.put.Call heap (values, key, value)
      (Algo.helper.Algo2LeanGenerated.«dict[Int, Int]».set heap values key value) () := by
  open Algo.helper.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.put_pc3 heap
      { v0 := values, v1 := key, v2 := value } caller valid)
    apply Reaches.prepend (Step.put_pc2 _ _ caller)
    exact Reaches.single (Step.put_pc1 _ _ caller)

end FiniteHelper
