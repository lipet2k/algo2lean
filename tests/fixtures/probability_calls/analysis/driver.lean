import Algo.driver.Probability
import Algo.client.Analysis
import Algo2LeanProbability.CallContext

/-!
A third module reuses the two-draw caller's published law. The original sampler
and caller analyses remain unchanged; only this module's continuation is proved.
The resulting contract preserves arbitrary initial counters and shared storage.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable
namespace DriverAnalysis
open Algo2LeanGenerated Algo.driver Algo.driver.Algo2LeanGenerated
open Algo2LeanCore Algo2LeanProbability
open scoped ENNReal

private def insideClient : Frame → Bool
  | .import_1 _ _ _ => true
  | _ => false

private theorem imported_pair (heap : Heap) (pc : Nat)
    (locals : (Int × Int) → State_sum_pair) (reward : Heap × Int → ENNReal) :
    callExpected nextChoice sum_pair.outcome
      (.active heap (.import_1 (Algo.client.entry_pair ()) []
        (fun result => match result with | .fn_pair value => .fn_sum_pair pc (locals value))) []) reward =
      pmfExpected (ClientAnalysis.pairLaw heap) (fun result =>
        callExpected nextChoice sum_pair.outcome
          (.active result.1 (.fn_sum_pair pc (locals result.2)) []) reward) := by
  let resume : Algo.client.Algo2LeanGenerated.Result → Frame :=
    fun result => match result with | .fn_pair value => .fn_sum_pair pc (locals value)
  let continuation : Heap × (Int × Int) → ENNReal := fun result =>
    callExpected nextChoice sum_pair.outcome (.active result.1 (.fn_sum_pair pc (locals result.2)) []) reward
  have reuse := callExpected_import Algo.client.Algo2LeanGenerated.nextChoice nextChoice
    Algo.client.pair.outcome sum_pair.outcome Frame.import_1 insideClient resume []
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intro result; cases result; rfl)
    heap (Algo.client.entry_pair ()) reward continuation
    (by intro h result; cases result; rfl)
  apply reuse.trans
  have contract := ClientAnalysis.pair_hasLaw heap continuation
  simp only [if_pos (show Algo.client.pair.ValidInput heap () from trivial)] at contract
  change callExpected Algo.client.Algo2LeanGenerated.nextChoice Algo.client.pair.outcome
    (.active heap (Algo.client.entry_pair ()) []) continuation =
    pmfExpected (ClientAnalysis.pairLaw heap) continuation at contract
  exact contract

/-- An arbitrary joint reward is obtained by applying this caller's deterministic
    continuation to the imported two-draw law. No sampler transition is unfolded. -/
theorem expected_return (heap : Heap) (reward : Heap → Int → ENNReal) :
    sum_pair.expectedReturn heap () reward =
      pmfExpected (ClientAnalysis.pairLaw heap) (fun result =>
        reward (result.1.tick "outer_calls") (result.2.1 + result.2.2)) := by
  let payoff : Heap × Int → ENNReal := fun result => reward result.1 result.2
  let locals (value : Int × Int) : State_sum_pair := {t2 := value}
  simp only [sum_pair.expectedReturn, if_pos (show sum_pair.ValidInput heap () from trivial)]
  rw [callExpected_next nextChoice sum_pair.outcome (sum_pair.initial heap ())
    (.active heap (.import_1 (Algo.client.entry_pair ()) []
      (fun result => match result with | .fn_pair value => .fn_sum_pair 4 (locals value))) [])
    rfl rfl payoff]
  rw [imported_pair]
  apply congrArg (pmfExpected (ClientAnalysis.pairLaw heap))
  funext result
  let saved : State_sum_pair := {v0 := result.2, t2 := result.2}
  let final := result.1.tick "outer_calls"
  rw [callExpected_next nextChoice sum_pair.outcome
    (.active result.1 (.fn_sum_pair 4 (locals result.2)) [])
    (.active result.1 (.fn_sum_pair 3 saved) []) rfl rfl payoff]
  rw [callExpected_next nextChoice sum_pair.outcome
    (.active result.1 (.fn_sum_pair 3 saved) [])
    (.active final (.fn_sum_pair 2 saved) []) rfl rfl payoff]
  rw [callExpected_next nextChoice sum_pair.outcome
    (.active final (.fn_sum_pair 2 saved) [])
    (.active final (.fn_sum_pair 1 {saved with t1 := result.2.1 + result.2.2}) []) rfl rfl payoff]
  rw [callExpected_next nextChoice sum_pair.outcome
    (.active final (.fn_sum_pair 1 {saved with t1 := result.2.1 + result.2.2}) [])
    (.done final (.fn_sum_pair (result.2.1 + result.2.2))) rfl rfl payoff]
  exact callExpected_return nextChoice sum_pair.outcome
    (.done final (.fn_sum_pair (result.2.1 + result.2.2)))
    (final, result.2.1 + result.2.2) rfl payoff

def sumLaw (heap : Heap) : PMF (Heap × Int) :=
  (ClientAnalysis.pairLaw heap).map (fun result =>
    (result.1.tick "outer_calls", result.2.1 + result.2.2))

/-- The third module exports the same reusable contract form as its suppliers. -/
theorem sum_hasLaw (heap : Heap) : sum_pair.HasLaw heap () (sumLaw heap) := by
  intro reward
  change sum_pair.expectedReturn heap () (fun final output => reward (final, output)) =
    pmfExpected (sumLaw heap) reward
  rw [expected_return, sumLaw, pmfExpected_map]

/-- Two different draws produce a sum of one with probability one half. -/
theorem sum_one_probability (heap : Heap) :
    sum_pair.returnProbability heap () (fun _ result => result = 1) = 1 / 2 := by
  rw [sum_pair.returnProbability_eq_expectedReturn heap () trivial, expected_return]
  simp only [ClientAnalysis.pairLaw, SamplerAnalysis.bitLaw, pmfExpected_bind,
    pmfExpected_map, pmfExpected_uniformInt]
  norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} from by decide, Int.toNat]
  rw [← add_mul, ← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- All three modules contribute to one shared set of counter increments. -/
theorem nested_costs (heap : Heap) :
    sum_pair.returnProbability heap () (fun final _ =>
      Heap.cost heap final "draws" = 2 ∧ Heap.cost heap final "outer_calls" = 1) = 1 := by
  rw [sum_pair.returnProbability_eq_expectedReturn heap () trivial, expected_return]
  simp only [ClientAnalysis.pairLaw, SamplerAnalysis.bitLaw, pmfExpected_bind,
    pmfExpected_map, pmfExpected_uniformInt]
  have costs : Heap.cost heap (((heap.tick "draws").tick "draws").tick "outer_calls") "draws" = 2 ∧
      Heap.cost heap (((heap.tick "draws").tick "draws").tick "outer_calls") "outer_calls" = 1 := by
    simp [Heap.cost, Heap.tick]
    omega
  simp only [costs]
  norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} from by decide, Int.toNat, ENNReal.mul_inv_cancel]

end DriverAnalysis
