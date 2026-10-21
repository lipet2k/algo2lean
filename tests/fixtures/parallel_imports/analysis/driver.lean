import Algo.driver.Probability
import Algo.client.Analysis
import Algo2LeanProbability.CallContext

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ParallelRandomClient
open Algo2LeanCore Algo2LeanGenerated Algo.driver Algo.driver.Algo2LeanGenerated
open Algo2LeanProbability ImportedWrite ImportedPair
open scoped ENNReal

/-- The randomized caller reuses the imported parallel proof as a deterministic law. -/
theorem sample_expected (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef)
    (reward : Heap → Int → ENNReal) :
    sample.expectedReturn heap a reward =
      ∑ draw ∈ Finset.Ico (0 : Int) 2,
        reward (updated (updated heap a (-1) 7) a 3 9) (7 + draw) * (2 : ENNReal)⁻¹ := by
  obtain ⟨cost, access, pair, _, _⟩ := pair_call heap a valid
  have imported (pc : Nat) (locals : Int × Int → State_sample) (payoff : Heap × Int → ENNReal) :
      callExpected nextChoice sample.outcome
        (.active heap (.import_1 (Algo.client.entry_pair a) []
          (fun result => match result with
            | .fn_pair value => .fn_sample pc (locals value)
            | _ => .invalid)) []) payoff =
      callExpected nextChoice sample.outcome
        (.active (updated (updated heap a (-1) 7) a 3 9)
          (.fn_sample pc (locals (7, 9))) []) payoff := by
    let inside : Frame → Bool := fun frame => match frame with
      | .import_1 _ _ _ => true
      | _ => false
    let resume : Algo.client.Algo2LeanGenerated.Result → Frame :=
      fun result => match result with
        | .fn_pair value => .fn_sample pc (locals value)
        | _ => .invalid
    let continuation : Heap → Int × Int → ENNReal := fun final value =>
      callExpected nextChoice sample.outcome (.active final (.fn_sample pc (locals value)) []) payoff
    have reuse := callExpected_import Algo.client.Algo2LeanGenerated.nextChoice nextChoice
      Algo.client.pair.outcome sample.outcome Frame.import_1 inside resume []
      (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (by intros; rfl) (by intro result; cases result <;> rfl)
      heap (Algo.client.entry_pair a) payoff (fun result => continuation result.1 result.2)
      (by
        intro final result
        cases result <;> first
        | rfl
        | exact callExpected_fail nextChoice sample.outcome _ rfl rfl payoff)
    apply reuse.trans
    have contract := Algo.client.pair.Call.expectedReturn pair.call continuation
    simpa only [Algo.client.pair.expectedReturn, Algo.client.pair.ValidInput, if_pos valid,
      Algo.client.pair.initial, Algo.client.entry_pair, start, continuation] using contract
  simp only [sample.expectedReturn, sample.ValidInput, if_pos valid]
  rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
  rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
  trans callExpected nextChoice sample.outcome
    (.active (updated (updated heap a (-1) 7) a 3 9)
      (.fn_sample 7 {v0 := a, t7 := (7, 9), t8 := a}) []) (fun result => reward result.1 result.2)
  · convert imported 7 (fun value => {v0 := a, t7 := value, t8 := a})
      (fun result => reward result.1 result.2) using 1
    congr 3
  · repeat' rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
    rw [callExpected_uniform nextChoice sample.outcome _ 0 2 _ rfl rfl (by norm_num)]
    apply Finset.sum_congr rfl
    intro draw member
    repeat' rw [callExpected_next nextChoice sample.outcome _ _ rfl rfl]
    rw [callExpected_return nextChoice sample.outcome _ _ rfl]
    rfl

def sampleLaw (heap : Heap) (a : SeqRef) : PMF (Heap × Int) :=
  (uniformInt 0 2 (by norm_num)).map (fun draw =>
    (updated (updated heap a (-1) 7) a 3 9, 7 + draw))

theorem sample_hasLaw (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef) :
    sample.HasLaw heap a (sampleLaw heap a) := by
  intro reward
  change sample.expectedReturn heap a (fun final value => reward (final, value)) =
    pmfExpected (sampleLaw heap a) reward
  rw [sample_expected heap a valid, sampleLaw, pmfExpected_map, pmfExpected_uniformInt]
  norm_num [Int.toNat]

theorem expected_updates (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef) :
    sample.expectedReturn heap a (fun final _ => (Heap.cost heap final "updates" : ENNReal)) = 2 := by
  rw [sample_expected heap a valid]
  norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} by decide, updates]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

end ParallelRandomClient
#print axioms ParallelRandomClient.sample_hasLaw
#print axioms ParallelRandomClient.expected_updates
