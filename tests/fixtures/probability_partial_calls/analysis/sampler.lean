import Algo.sampler.Probability
import Algo2LeanProbability.StoppedRules

/-! A partial randomized contract: one branch returns and one loops forever.
Every joint reward retains its true successful mass, including infinite rewards. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PartialSamplerAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability MeasureTheory
open Algo.sampler Algo.sampler.Algo2LeanGenerated
open scoped ENNReal

private def inLoop (sample : SampleState Configuration) : Prop :=
  ∃ heap locals,
    sample = some (.active heap (.fn_sometimes 4 locals) []) ∨
    sample = some (.active heap (.fn_sometimes 3 {locals with t2 := true}) []) ∨
    sample = some (.active heap (.fn_sometimes 5 {locals with t2 := true}) [])

private theorem loop_reward (heap : Heap) (locals : State_sometimes)
    (reward : Heap × Int → ℝ≥0∞) :
    callExpected nextChoice sometimes.outcome (.active heap (.fn_sometimes 4 locals) []) reward = 0 := by
  apply le_antisymm _ bot_le
  apply Stopped.expected_le_on (transition nextChoice) (completed sometimes.outcome)
    inLoop (returnReward sometimes.outcome reward) (fun _ => 0)
  · rintro sample ⟨h, s, entered⟩ _
    rcases entered with rfl | rfl | rfl
    · change ∀ᵐ (after : SampleState Configuration) ∂(PMF.pure (α := SampleState Configuration) (some (.active h (.fn_sometimes 3 {s with t2 := true}) []) : SampleState Configuration)).toMeasure,
        inLoop after
      rw [PMF.toMeasure_pure]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 ⟨h, s, Or.inr (Or.inl rfl)⟩
    · change ∀ᵐ (after : SampleState Configuration) ∂(PMF.pure (α := SampleState Configuration) (some (.active h (.fn_sometimes 5 {s with t2 := true}) []) : SampleState Configuration)).toMeasure,
        inLoop after
      rw [PMF.toMeasure_pure]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 ⟨h, s, Or.inr (Or.inr rfl)⟩
    · change ∀ᵐ (after : SampleState Configuration) ∂(PMF.pure (α := SampleState Configuration) (some (.active h (.fn_sometimes 4 {s with t2 := true}) []) : SampleState Configuration)).toMeasure,
        inLoop after
      rw [PMF.toMeasure_pure]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 ⟨h, {s with t2 := true}, Or.inl rfl⟩
  · rintro sample ⟨h, s, entered⟩ stopped
    rcases entered with rfl | rfl | rfl <;> exact le_rfl
  · intro sample valid outside
    simp
  · exact ⟨heap, locals, Or.inl rfl⟩

local macro "advance" : tactic =>
  `(tactic| rw [callExpected_next nextChoice sometimes.outcome _ _ rfl (by rfl)])

/-- Success has probability one half. The other half diverges after charging
one work tick; no normalized `HasLaw` is asserted for this partial function. -/
theorem sometimes_expected (heap : Heap) (reward : Heap → Int → ℝ≥0∞) :
    sometimes.expectedReturn heap () reward =
      reward (heap.tick "work") 7 * (2 : ℝ≥0∞)⁻¹ := by
  simp only [sometimes.expectedReturn, sometimes.ValidInput, if_true, sometimes.initial, start]
  advance
  advance
  advance
  rw [callExpected_uniform nextChoice sometimes.outcome _ 0 2 _ rfl rfl (by norm_num)]
  norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} by decide]
  have success : callExpected nextChoice sometimes.outcome
      (.active (heap.tick "work") (.fn_sometimes 10 {t5 := 0, t7 := 2}) [])
      (fun result => reward result.1 result.2) = reward (heap.tick "work") 7 := by
    advance
    advance
    advance
    advance
    advance
    rw [callExpected_return nextChoice sometimes.outcome _ (heap.tick "work", 7) rfl]
  have diverges : callExpected nextChoice sometimes.outcome
      (.active (heap.tick "work") (.fn_sometimes 10 {t5 := 1, t7 := 2}) [])
      (fun result => reward result.1 result.2) = 0 := by
    advance
    advance
    advance
    exact loop_reward _ _ _
  rw [success, diverges]
  simp

end PartialSamplerAnalysis
