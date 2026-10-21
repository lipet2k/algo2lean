import Algo.client.Probability
import Algo.helper.Analysis
import Algo2LeanProbability.CallContext

/-!
Two real imports reuse the unchanged deterministic proof. Only the caller's
own instructions and final draw are analyzed here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ClientAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo.client Algo.client.Algo2LeanGenerated
open Algo2LeanProbability HelperAnalysis
open scoped ENNReal

/-- Repeated mutations and their counters are retained jointly with the draw. -/
theorem sample_expected (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef)
    (reward : Heap → Int → ENNReal) :
    sample.expectedReturn heap a reward =
      ∑ draw ∈ Finset.Ico (0 : Int) 2,
        reward (updated (updated heap a) a) (heap.read a 0 + 2 + draw) *
          (2 : ENNReal)⁻¹ := by
  -- This operational helper is local to the proof; its details do not leak
  -- into the public contract or require a second analysis of bump.
  have imported (h : Heap) (existsA : a < h.nextRef) (pc : Nat)
      (locals : Int → State_sample) (payoff : Heap × Int → ENNReal) :
      callExpected nextChoice sample.outcome
        (.active h (.import_0 (Algo.helper.entry_bump a) []
          (fun result => match result with | .fn_bump value => .fn_sample pc (locals value))) [])
        payoff =
      callExpected nextChoice sample.outcome
        (.active (updated h a) (.fn_sample pc (locals (h.read a 0 + 1))) []) payoff := by
    let inside : Frame → Bool := fun frame => match frame with
      | .import_0 _ _ _ => true
      | _ => false
    let resume : Algo.helper.Algo2LeanGenerated.Result → Frame :=
      fun result => match result with | .fn_bump value => .fn_sample pc (locals value)
    let continuation : Heap → Int → ENNReal := fun final value =>
      callExpected nextChoice sample.outcome (.active final (.fn_sample pc (locals value)) []) payoff
    have reuse := callExpected_import Algo.helper.Algo2LeanGenerated.nextChoice nextChoice
      Algo.helper.bump.outcome sample.outcome Frame.import_0 inside resume []
      (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (by intros; rfl) (by intro result; cases result; rfl)
      h (Algo.helper.entry_bump a) payoff (fun result => continuation result.1 result.2)
      (by intro final result; cases result; rfl)
    apply reuse.trans
    have contract := Algo.helper.bump.Call.expectedReturn (bump_call h a existsA) continuation
    simpa only [Algo.helper.bump.expectedReturn, Algo.helper.bump.ValidInput, if_pos existsA,
      Algo.helper.bump.initial, Algo.helper.entry_bump, start, continuation] using contract
  simp only [sample.expectedReturn, sample.ValidInput, if_pos valid]
  repeat' rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
  rw [imported heap valid 10 (fun value => {v0 := a, t10 := value, t11 := a})]
  repeat' rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
  rw [imported (updated heap a) valid 7 (fun value =>
    {v0 := a, v1 := heap.read a 0 + 1, t8 := value, t9 := a,
      t10 := heap.read a 0 + 1, t11 := a})]
  repeat' rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
  rw [callExpected_uniform nextChoice sample.outcome _ 0 2 _ rfl rfl (by norm_num)]
  apply Finset.sum_congr rfl
  intro draw member
  repeat' rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
  rw [callExpected_return nextChoice sample.outcome _ _ rfl]
  simp [updated, Heap.read, Heap.write, Heap.tick, add_assoc]

def sampleLaw (heap : Heap) (a : SeqRef) : PMF (Heap × Int) :=
  (uniformInt 0 2 (by norm_num)).map (fun draw =>
    (updated (updated heap a) a, heap.read a 0 + 2 + draw))

/-- The composition exports the same law interface used by other randomized
algorithms; the deterministic helper proof is unchanged. -/
theorem sample_hasLaw (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef) :
    sample.HasLaw heap a (sampleLaw heap a) := by
  intro reward
  change sample.expectedReturn heap a (fun final value => reward (final, value)) =
    pmfExpected (sampleLaw heap a) reward
  rw [sample_expected heap a valid, sampleLaw, pmfExpected_map, pmfExpected_uniformInt]
  norm_num [Int.toNat]

/-- Both calls charge the original counter, even when it was already nonzero. -/
theorem expected_updates (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef) :
    sample.expectedReturn heap a (fun final _ => (Heap.cost heap final "updates" : ENNReal)) = 2 := by
  rw [sample_expected heap a valid]
  norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} by decide,
    updated, Heap.cost, Heap.write, Heap.tick, Nat.add_assoc]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

end ClientAnalysis
#print axioms Algo.helper.bump.Call.hasLaw
#print axioms ClientAnalysis.sample_hasLaw
#print axioms ClientAnalysis.expected_updates
