import Algo2LeanProbability.Call

/-!
A rejection sampler has no deterministic bound on its number of draws. Its
probabilistic call contract nevertheless gives the complete return law and is
valid for arbitrary nonnegative rewards, including infinite rewards.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Algo2LeanProbability
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ProbabilityCallCore

private def retry (state : Bool) : Algo2LeanCore.Choice Bool :=
  if state then .halt else .uniform 0 2 (fun draw => decide (draw = 1))

private def outcome (state : Bool) : Option Unit :=
  if state then some () else none

private theorem completed_reward (reward : Unit → ℝ≥0∞) :
    callExpected retry outcome true reward = reward () :=
  callExpected_return retry outcome true () rfl reward

private theorem retry_equation (reward : Unit → ℝ≥0∞) :
    callExpected retry outcome false reward =
      callExpected retry outcome false reward * (2 : ℝ≥0∞)⁻¹ +
      reward () * (2 : ℝ≥0∞)⁻¹ := by
  have equation := callExpected_uniform retry outcome false 0 2 (fun draw => decide (draw = 1))
    rfl rfl (by norm_num) reward
  norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} by decide, completed_reward] at equation
  exact equation

private theorem retry_reward_bound (reward : Unit → ℝ≥0∞) :
    callExpected retry outcome false reward ≤ reward () := by
  apply Stopped.expected_le _ _ _ (fun _ => reward ())
  · rintro state ⟨current, result, rfl, seen⟩
    cases result
    simp [returnReward, seen]
  · intro state notReturned
    simp

/-- Repeated independent coin draws eventually succeed with probability one;
the theorem determines every output reward without a bounded unrolling. -/
theorem retry_hasLaw : HasLaw retry outcome false (PMF.pure ()) := by
  intro reward
  have equation := retry_equation reward
  have bound := retry_reward_bound reward
  have value : callExpected retry outcome false reward = reward () := by
    by_cases infinite : reward () = ∞
    · simpa [infinite] using equation
    · have finite : callExpected retry outcome false reward ≠ ∞ :=
        ne_top_of_le_ne_top infinite bound
      apply (ENNReal.toReal_eq_toReal_iff' finite infinite).mp
      have realEquation := congrArg ENNReal.toReal equation
      rw [ENNReal.toReal_add] at realEquation
      · norm_num [ENNReal.toReal_mul] at realEquation
        linarith
      · exact ENNReal.mul_ne_top finite (by simp)
      · exact ENNReal.mul_ne_top infinite (by simp)
  simpa using value

/-- This is the same probability-one event in the infinite-path semantics. -/
theorem retry_terminates :
    probability (execution retry false) (Event.returnsWhere outcome (fun _ => True)) = 1 := by
  rw [← callProbability_eq_execution retry outcome]
  · exact retry_hasLaw.termination
  · intro state result observed
    cases state <;> simp_all [outcome, retry]

/-- A nonterminating call contributes zero to completed-return rewards. Its
missing probability mass is not silently normalized into a successful return. -/
theorem diverging_return_reward (reward : Unit → ℝ≥0∞) :
    callExpected (fun _ : Unit => .next ()) (fun _ => (none : Option Unit)) () reward = 0 := by
  apply le_antisymm _ bot_le
  apply Stopped.expected_le _ _ _ (fun _ => 0)
  · rintro state ⟨current, output, same, impossible⟩
    cases impossible
  · intro state notReturned
    simp

end ProbabilityCallCore
