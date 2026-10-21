import Algo.halves.Generated

open Algo2LeanCore Algo2LeanGenerated

namespace RealHelper

/-- Halving an exact real leaves the caller's heap unchanged. -/
theorem half_call (heap : Heap) (value : ℝ) :
    Algo.halves.half.Call heap value heap (value / 2) := by
  open Algo.halves.Algo2LeanGenerated in
    refine ⟨True.intro, ?_⟩
    intro caller
    apply Reaches.prepend (Step.half_pc2 heap { v0 := value } caller (by simp))
    simpa using Reaches.single (Step.half_pc1 heap { v0 := value, t1 := value / 2 } caller)

end RealHelper
