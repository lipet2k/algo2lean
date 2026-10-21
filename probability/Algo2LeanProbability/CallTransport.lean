import Algo2LeanProbability.Call

/-!
Reusable call transport when a module has several result tags. An unobserved
terminal tag has zero return reward in the source, although its caller may
reject it by failing rather than by repeating the terminal state. Stop the
transport at all module exits and compare their continuation rewards; the two
implementations need only preserve transitions while the callee is active.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Algo2LeanProbability

namespace Stopped

variable {State : Type*} [MeasurableSpace State] [DiscreteMeasurableSpace State]

/-- Only values at the stopping boundary affect the stopped reward. -/
theorem expected_congr_on_boundary (step : State → PMF State) (boundary : State → Prop)
    (first second : State → ℝ≥0∞)
    (same : ∀ state, boundary state → first state = second state) (initial : State) :
    expected step boundary first initial = expected step boundary second initial := by
  have finite : ∀ time state, within step boundary first time state =
      within step boundary second time state := by
    intro time
    induction time with
    | zero =>
        intro state
        simp only [within]
        by_cases stop : boundary state <;> simp [stop, same state]
    | succ time ih =>
        intro state
        simp only [within]
        by_cases stop : boundary state
        · simp [stop, same state stop]
        · simp only [stop, ↓reduceIte]
          exact lintegral_congr ih
  simp only [expected, finite]

/-- A self-loop outside the return boundary has zero completed-call reward,
    including when the proposed reward takes infinite values elsewhere. -/
theorem expected_eq_zero_of_self_loop (step : State → PMF State) (boundary : State → Prop)
    (reward : State → ℝ≥0∞) (initial : State) (outside : ¬ boundary initial)
    (loops : step initial = PMF.pure initial) : expected step boundary reward initial = 0 := by
  have finite : ∀ time, within step boundary reward time initial = 0 := by
    intro time
    induction time with
    | zero => simp [within, outside]
    | succ time ih =>
        simp only [within, outside, ↓reduceIte, loops, PMF.toMeasure_pure]
        rw [lintegral_dirac' _ Measurable.of_discrete, ih]
  simp [expected, finite]

end Stopped

private theorem returnReward_eq_zero_of_not_completed {State Output : Type*}
    (observe : State → Option Output) (payoff : Output → ℝ≥0∞)
    (sample : SampleState State) (absent : ¬ completed observe sample) :
    returnReward observe payoff sample = 0 := by
  cases sample with
  | none => rfl
  | some state =>
      cases seen : observe state with
      | none => simp [returnReward, seen]
      | some output => exact False.elim (absent ⟨state, output, rfl, seen⟩)

/-- Add absorbing, unobserved exits to a call's stopping boundary without
    changing any completed-return reward. Such exits contribute zero. -/
theorem callExpected_stop_at_exits {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (exits : SampleState State → Prop)
    (includes : ∀ sample, completed observe sample → exits sample)
    (unobserved : ∀ sample, exits sample → ¬ completed observe sample →
      transition next sample = PMF.pure sample)
    (initial : State) (payoff : Output → ℝ≥0∞) :
    callExpected next observe initial payoff =
      Stopped.expected (transition next) exits (returnReward observe payoff) (some initial) := by
  unfold callExpected
  rw [Stopped.expected_first_return _ exits (completed observe) includes]
  apply Stopped.expected_congr_on_boundary
  intro sample atExit
  by_cases returned : completed observe sample
  · exact Stopped.expected_boundary _ _ _ _ returned
  · rw [Stopped.expected_eq_zero_of_self_loop _ _ _ _ returned (unobserved sample atExit returned),
      returnReward_eq_zero_of_not_completed observe payoff sample returned]

/-- A rejected local operation has zero completed-call reward. Charged work
    before rejection remains visible through the separate full-path cost API. -/
theorem callExpected_fail {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (absent : observe initial = none) (fails : next initial = .fail)
    (payoff : Output → ℝ≥0∞) : callExpected next observe initial payoff = 0 := by
  have notCompleted : ¬ completed observe (some initial) := by
    rintro ⟨state, output, same, seen⟩
    cases same
    simp [absent] at seen
  unfold callExpected
  rw [Stopped.expected_unfold, if_neg notCompleted]
  simp only [transition, fails, choiceLaw_fail, PMF.toMeasure_pure]
  rw [lintegral_dirac' _ Measurable.of_discrete]
  exact Stopped.expected_eq_zero_of_self_loop (State := SampleState State)
    (transition next) (completed observe) (returnReward observe payoff) none
    (by simp [completed]) rfl

/-- Transport a callee through every module exit. Only active-callee
    transitions must agree; unobserved exits may fail in the caller provided
    their continuation has zero completed-return reward. -/
theorem callExpected_in_context_stopped {State Output Target : Type*}
    [MeasurableSpace Target] [DiscreteMeasurableSpace Target]
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (exits : SampleState State → Prop)
    (includes : ∀ sample, completed observe sample → exits sample)
    (unobserved : ∀ sample, exits sample → ¬ completed observe sample →
      transition next sample = PMF.pure sample)
    (targetStep : Target → PMF Target) (embed : SampleState State → Target)
    (earlier final : Target → Prop) (contained : ∀ state, final state → earlier state)
    (steps : ∀ sample, ¬ exits sample → targetStep (embed sample) =
      (transition next sample).map embed)
    (boundaries : ∀ sample, earlier (embed sample) ↔ exits sample)
    (reward : Target → ℝ≥0∞) (payoff : Output → ℝ≥0∞)
    (continuation : ∀ sample, exits sample →
      Stopped.expected targetStep final reward (embed sample) = returnReward observe payoff sample) :
    Stopped.expected targetStep final reward (embed (some initial)) =
      callExpected next observe initial payoff := by
  rw [Stopped.expected_first_return targetStep earlier final contained,
    callExpected_stop_at_exits next observe exits includes unobserved]
  exact Stopped.expected_map (transition next) targetStep embed exits earlier steps boundaries
    (returnReward observe payoff) (Stopped.expected targetStep final reward) continuation (some initial)

/-- A function's original joint law can be reused unchanged in a caller even
    when other functions in its module have different, rejected result tags. -/
theorem HasLaw.in_context_stopped {State Output Target : Type*}
    [MeasurableSpace Target] [DiscreteMeasurableSpace Target]
    {next : State → Algo2LeanCore.Choice State} {observe : State → Option Output}
    {initial : State} {law : PMF Output} (contract : HasLaw next observe initial law)
    (exits : SampleState State → Prop)
    (includes : ∀ sample, completed observe sample → exits sample)
    (unobserved : ∀ sample, exits sample → ¬ completed observe sample →
      transition next sample = PMF.pure sample)
    (targetStep : Target → PMF Target) (embed : SampleState State → Target)
    (earlier final : Target → Prop) (contained : ∀ state, final state → earlier state)
    (steps : ∀ sample, ¬ exits sample → targetStep (embed sample) =
      (transition next sample).map embed)
    (boundaries : ∀ sample, earlier (embed sample) ↔ exits sample)
    (reward : Target → ℝ≥0∞) (payoff : Output → ℝ≥0∞)
    (continuation : ∀ sample, exits sample →
      Stopped.expected targetStep final reward (embed sample) = returnReward observe payoff sample) :
    Stopped.expected targetStep final reward (embed (some initial)) = pmfExpected law payoff := by
  rw [callExpected_in_context_stopped next observe initial exits includes unobserved targetStep
    embed earlier final contained steps boundaries reward payoff continuation]
  exact contract payoff

end Algo2LeanProbability
