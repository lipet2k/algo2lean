import Algo.client.Probability
import Algo.sampler.Analysis
import Algo2LeanProbability.CallContext

/-!
The imported module has both `bit : Int` and `other : Bool`. The existing bit
analysis is reused unchanged. A wrong-tag source return is an unobserved halt,
while the generated caller rejects that tag with an invalid frame and failure.
The transport theorem accepts this difference without an unreachable-state
invariant or inspection of the sampler's transition rules.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace ModuleTransportAnalysis
open Algo2LeanGenerated Algo.client Algo.client.Algo2LeanGenerated
open Algo2LeanCore Algo2LeanProbability
open scoped ENNReal

private def insideSampler : Frame → Bool
  | .import_0 _ _ _ => true
  | _ => false

/-- The bit contract is usable even when the supplier has other result tags. -/
theorem imported_bit (heap : Heap) (pc : Nat) (locals : Int → State_pair)
    (reward : Heap × (Int × Int) → ENNReal) :
    callExpected nextChoice pair.outcome
      (.active heap (.import_0 (Algo.sampler.entry_bit ()) []
        (fun result => match result with
          | .fn_bit value => .fn_pair pc (locals value)
          | .fn_other _ => .invalid)) []) reward =
      ∑ value ∈ Finset.Ico (0 : Int) 2,
        callExpected nextChoice pair.outcome
          (.active (heap.tick "draws") (.fn_pair pc (locals value)) []) reward *
          (2 : ENNReal)⁻¹ := by
  let resume : Algo.sampler.Algo2LeanGenerated.Result → Frame :=
    fun result => match result with
      | .fn_bit value => .fn_pair pc (locals value)
      | .fn_other _ => .invalid
  let continuation : Heap × Int → ENNReal := fun result =>
    callExpected nextChoice pair.outcome (.active result.1 (.fn_pair pc (locals result.2)) []) reward
  have reuse := callExpected_import Algo.sampler.Algo2LeanGenerated.nextChoice nextChoice
    Algo.sampler.bit.outcome pair.outcome Frame.import_0 insideSampler resume []
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intro result; cases result <;> rfl)
    heap (Algo.sampler.entry_bit ()) reward continuation
    (by
      intro h result
      cases result with
      | fn_bit value => rfl
      | fn_other value =>
          exact callExpected_fail nextChoice pair.outcome (.active h .invalid []) rfl rfl reward)
  apply reuse.trans
  have contract := SamplerAnalysis.bit_hasLaw heap continuation
  simp only [if_pos (show Algo.sampler.bit.ValidInput heap () from trivial)] at contract
  change callExpected Algo.sampler.Algo2LeanGenerated.nextChoice Algo.sampler.bit.outcome
    (.active heap (Algo.sampler.entry_bit ()) []) continuation =
    pmfExpected (SamplerAnalysis.bitLaw heap) continuation at contract
  rw [contract, SamplerAnalysis.bitLaw, pmfExpected_map, pmfExpected_uniformInt]
  norm_num [Int.toNat, continuation]

end ModuleTransportAnalysis
