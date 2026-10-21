import Algo2LeanProbability.Call

/-!
Rules for solving stopped-expectation equations. A recurrence alone need not
determine an unbounded execution's result. Bounded solutions become unique
when the stopping boundary is reached almost surely; arbitrary nonnegative
rewards can then be approached by the increasing truncations in `expected_iSup`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped ENNReal

namespace Algo2LeanProbability.Stopped

variable {State : Type*} [MeasurableSpace State] [DiscreteMeasurableSpace State]

/-- Bound a stopped expectation by checking the local equations only on states
    satisfying an invariant. Probability-zero transitions need no obligations. -/
theorem expected_le_on (step : State → PMF State) (boundary invariant : State → Prop)
    (reward bound : State → ℝ≥0∞)
    (preserved : ∀ state, invariant state → ¬ boundary state →
      ∀ᵐ after ∂(step state).toMeasure, invariant after)
    (atBoundary : ∀ state, invariant state → boundary state → reward state ≤ bound state)
    (advance : ∀ state, invariant state → ¬ boundary state →
      (∫⁻ after, bound after ∂(step state).toMeasure) ≤ bound state)
    (initial : State) (valid : invariant initial) :
    expected step boundary reward initial ≤ bound initial := by
  apply iSup_le
  intro time
  induction time generalizing initial with
  | zero =>
      by_cases stop : boundary initial
      · simpa [within, stop] using atBoundary initial valid stop
      · simp [within, stop]
  | succ time ih =>
      by_cases stop : boundary initial
      · simpa [within, stop] using atBoundary initial valid stop
      · simp only [within, stop, ↓reduceIte]
        apply le_trans _ (advance initial valid stop)
        apply lintegral_mono_ae
        filter_upwards [preserved initial valid stop] with after validAfter
        exact ih after validAfter

/-- Almost-sure stopping makes a bounded solution of the local expectation
    equations unique on a preserved invariant. Unreachable or malformed states
    outside the invariant require no equations or bounds. -/
theorem expected_unique_on (step : State → PMF State) (boundary invariant : State → Prop)
    (reward candidate : State → ℝ≥0∞) (bound : ℝ≥0∞) (finite : bound ≠ ∞)
    (preserved : ∀ state, invariant state → ¬ boundary state →
      ∀ᵐ after ∂(step state).toMeasure, invariant after)
    (bounded : ∀ state, invariant state → candidate state ≤ bound)
    (atBoundary : ∀ state, invariant state → boundary state → candidate state = reward state)
    (advance : ∀ state, invariant state → ¬ boundary state →
      candidate state = ∫⁻ after, candidate after ∂(step state).toMeasure)
    (initial : State) (valid : invariant initial)
    (terminates : expected step boundary (fun _ => 1) initial = 1) :
    candidate initial = expected step boundary reward initial := by
  have comparison : ∀ time state, invariant state →
      candidate state + bound * within step boundary (fun _ => 1) time state ≤
        within step boundary reward time state + bound := by
    intro time
    induction time with
    | zero =>
        intro state validState
        by_cases stop : boundary state
        · simp [within, stop, atBoundary state validState stop]
        · simpa [within, stop] using bounded state validState
    | succ time ih =>
        intro state validState
        by_cases stop : boundary state
        · simp [within, stop, atBoundary state validState stop]
        · simp only [within, stop, ↓reduceIte, advance state validState stop]
          have comparisonAE : ∀ᵐ after ∂(step state).toMeasure,
              candidate after + bound * within step boundary (fun _ => 1) time after ≤
                within step boundary reward time after + bound := by
            filter_upwards [preserved state validState stop] with after validAfter
            exact ih after validAfter
          have integrated := lintegral_mono_ae comparisonAE
          simpa only [lintegral_add_left Measurable.of_discrete,
            lintegral_const_mul bound Measurable.of_discrete, lintegral_const,
            measure_univ, mul_one] using integrated
  have limit : candidate initial + bound * expected step boundary (fun _ => 1) initial ≤
      expected step boundary reward initial + bound := by
    rw [expected, ENNReal.mul_iSup, ENNReal.add_iSup]
    apply iSup_le
    intro time
    exact (comparison time initial valid).trans
      (add_le_add (le_iSup (fun time => within step boundary reward time initial) time) le_rfl)
  apply le_antisymm
  · apply ENNReal.le_of_add_le_add_right finite
    simpa only [terminates, mul_one] using limit
  · exact expected_le_on step boundary invariant reward candidate preserved
      (fun state validState stop => (atBoundary state validState stop).symm.le)
      (fun state validState outside => (advance state validState outside).symm.le)
      initial valid

/-- Almost-sure stopping makes a globally bounded solution unique. The stopping
    premise is essential: a diverging chain can have many bounded harmonic
    functions but zero completed-return reward. -/
theorem expected_unique (step : State → PMF State) (boundary : State → Prop)
    (reward candidate : State → ℝ≥0∞) (bound : ℝ≥0∞) (finite : bound ≠ ∞)
    (bounded : ∀ state, candidate state ≤ bound)
    (atBoundary : ∀ state, boundary state → candidate state = reward state)
    (advance : ∀ state, ¬ boundary state →
      candidate state = ∫⁻ after, candidate after ∂(step state).toMeasure)
    (initial : State) (terminates : expected step boundary (fun _ => 1) initial = 1) :
    candidate initial = expected step boundary reward initial :=
  expected_unique_on step boundary (fun _ => True) reward candidate bound finite
    (by simp) (fun state _ => bounded state) (fun state _ => atBoundary state)
    (fun state _ => advance state) initial trivial terminates

end Algo2LeanProbability.Stopped
