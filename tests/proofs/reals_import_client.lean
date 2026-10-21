import Algo.scale.Generated
import Algo.halves.Analysis

open Algo2LeanCore Algo2LeanGenerated

namespace RealClient

/-- Integer arguments are promoted before reusing the exact-real contract. -/
theorem scale_call (heap : Heap) (value : Int) :
    Algo.scale.scale.Call heap value heap ((value : ℝ) / 2) := by
  open Algo.scale.Algo2LeanGenerated in
    refine ⟨True.intro, ?_⟩
    intro caller
    apply Reaches.prepend (Step.scale_pc3 heap { v0 := value } caller)
    apply Reaches.prepend (Step.scale_pc2 _ _ caller)
    apply (ModuleCall.summary import_0_simulates _ caller
      (RealHelper.half_call heap value).2).trans
    exact Reaches.single (Step.scale_pc1 _ _ caller)

end RealClient
