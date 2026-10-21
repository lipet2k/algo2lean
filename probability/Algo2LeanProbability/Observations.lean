import Algo2LeanProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
Measurable observations of complete executions. These operations apply to any
execution law, including laws of computations that can fail or diverge. Runtime
is the supremum of charged costs over finite prefixes, so costs paid before a
failure and costs on nonterminating paths are retained.

Return rewards belong to the stopped-call interface. The observations here can
also depend on the entire path, multiple counters, and nonlinear cost functions.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Algo2LeanProbability

universe u

namespace Observable

variable {State : Type u}

/-- Apply a measurable nonnegative function to an observation. This supports
    rewards beyond linear costs, such as powers and bounded penalties. -/
def map (observation : Observable State) (reward : ℝ≥0∞ → ℝ≥0∞)
    (measurable : Measurable reward) : Observable State :=
  ⟨reward ∘ observation.value, measurable.comp observation.measurable⟩

/-- Observe two quantities jointly, without an independence assumption. For
    example, a reward may depend on both comparisons and allocated cells. -/
def combine (first second : Observable State) (reward : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞)
    (measurable : Measurable reward) : Observable State :=
  ⟨fun run => reward (first.value run, second.value run),
    measurable.comp (first.measurable.prodMk second.measurable)⟩

/-- Multiply observations on the same run, retaining their correlation. -/
def mul (first second : Observable State) : Observable State :=
  ⟨fun run => first.value run * second.value run,
    first.measurable.mul second.measurable⟩

/-- The natural power of an observation, used for runtime moments. -/
def pow (observation : Observable State) (power : ℕ) : Observable State :=
  ⟨fun run => observation.value run ^ power, observation.measurable.pow_const power⟩

/-- An event as a zero-or-one nonnegative observation. Its expectation is the
    unconditional probability of the event. -/
def ofEvent (event : Event State) : Observable State :=
  ⟨event.states.indicator (fun _ => 1), measurable_const.indicator event.measurable⟩

@[simp] theorem map_value (observation : Observable State) (reward : ℝ≥0∞ → ℝ≥0∞)
    (measurable : Measurable reward) (run : Run State) :
    (observation.map reward measurable).value run = reward (observation.value run) := rfl

@[simp] theorem mul_value (first second : Observable State) (run : Run State) :
    (first.mul second).value run = first.value run * second.value run := rfl

@[simp] theorem pow_value (observation : Observable State) (power : ℕ) (run : Run State) :
    (observation.pow power).value run = observation.value run ^ power := rfl

/-- Exceeding a total-cost threshold is witnessed by a finite prefix. This
    remains true for an infinite total cost and requires no termination premise. -/
theorem total_exceeds_iff (counter : State → ℕ) (threshold : ℝ≥0∞) (run : Run State) :
    threshold < (total counter).value run ↔
      ∃ time state, run time = some state ∧ threshold < (counter state : ℝ≥0∞) := by
  simp only [total, lt_iSup_iff]
  constructor
  · rintro ⟨time, reached⟩
    cases found : run time with
    | none => simp [found] at reached
    | some state => exact ⟨time, state, found, by simpa [found] using reached⟩
  · rintro ⟨time, state, found, reached⟩
    exact ⟨time, by simpa [found] using reached⟩

theorem total_mono (first second : State → ℕ) (bound : ∀ state, first state ≤ second state)
    (run : Run State) : (total first).value run ≤ (total second).value run := by
  apply iSup_mono
  intro time
  cases run time with
  | none => exact le_rfl
  | some state =>
    change (first state : ℝ≥0∞) ≤ (second state : ℝ≥0∞)
    exact_mod_cast bound state

end Observable

namespace Event

variable {State : Type u}

/-- An arbitrary observation strictly exceeds the supplied threshold. -/
def exceeds (observation : Observable State) (threshold : ℝ≥0∞) : Event State :=
  ⟨{run | threshold < observation.value run},
    measurableSet_lt measurable_const observation.measurable⟩

/-- An arbitrary observation reaches or exceeds the supplied threshold. -/
def atLeast (observation : Observable State) (threshold : ℝ≥0∞) : Event State :=
  ⟨{run | threshold ≤ observation.value run},
    measurableSet_le measurable_const observation.measurable⟩

end Event

@[simp] theorem expected_ofEvent {State : Type u} (law : Measure (Run State))
    (event : Event State) : expected law (Observable.ofEvent event) = probability law event :=
  lintegral_indicator_one event.measurable

/-- Almost-sure bounds suffice for comparing expectations. This avoids imposing
    an invariant on impossible paths in the ambient space of infinite sequences. -/
theorem expected_mono_ae {State : Type u} (law : Measure (Run State))
    (first second : Observable State)
    (bound : ∀ᵐ run ∂law, first.value run ≤ second.value run) :
    expected law first ≤ expected law second := lintegral_mono_ae bound

theorem expected_congr_ae {State : Type u} (law : Measure (Run State))
    (first second : Observable State)
    (same : ∀ᵐ run ∂law, first.value run = second.value run) :
    expected law first = expected law second := lintegral_congr_ae same

/-- Finite expectation implies an almost-sure finite observation. Applied to a
    tick counter this proves finite charged cost, not termination: a diverging
    computation can have finite cost if it eventually stops charging ticks. -/
theorem ae_finite_of_expected_ne_top {State : Type u} (law : Measure (Run State))
    (observation : Observable State) (finite : expected law observation ≠ ∞) :
    ∀ᵐ run ∂law, observation.value run < ∞ :=
  ae_lt_top observation.measurable finite

/-- Markov's inequality without division, valid even at zero and infinity. -/
theorem threshold_mul_probability_atLeast_le {State : Type u}
    (law : Measure (Run State)) (observation : Observable State) (threshold : ℝ≥0∞) :
    threshold * probability law (Event.atLeast observation threshold) ≤ expected law observation :=
  mul_meas_ge_le_lintegral observation.measurable threshold

/-- Any nonnegative observable gives a tail bound from its expectation. -/
theorem probability_atLeast_le {State : Type u} (law : Measure (Run State))
    (observation : Observable State) (threshold : ℝ≥0∞)
    (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    probability law (Event.atLeast observation threshold) ≤ expected law observation / threshold :=
  meas_ge_le_lintegral_div observation.measurable.aemeasurable positive finite

/-- The usual strict runtime-tail form of Markov's inequality. -/
theorem probability_exceeds_le {State : Type u} (law : Measure (Run State))
    (observation : Observable State) (threshold : ℝ≥0∞)
    (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    probability law (Event.exceeds observation threshold) ≤ expected law observation / threshold := by
  calc
    probability law (Event.exceeds observation threshold) ≤
        probability law (Event.atLeast observation threshold) :=
      measure_mono (fun _ reached =>
        (show threshold < observation.value _ from reached).le)
    _ ≤ _ := probability_atLeast_le law observation threshold positive finite

/-- Higher moments give tail bounds in the same interface as ordinary expected
    runtime. In particular, power two yields `Pr[X > t] ≤ E[X²] / t²`. -/
theorem probability_exceeds_le_moment {State : Type u} (law : Measure (Run State))
    (observation : Observable State) (threshold : ℝ≥0∞) (power : ℕ)
    (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    probability law (Event.exceeds observation threshold) ≤
      expected law (observation.pow power) / threshold ^ power := by
  calc
    probability law (Event.exceeds observation threshold) ≤
        probability law (Event.atLeast (observation.pow power) (threshold ^ power)) := by
      apply measure_mono
      intro run reached
      change threshold ^ power ≤ observation.value run ^ power
      exact pow_le_pow_left' (show threshold < observation.value run from reached).le power
    _ ≤ _ := probability_atLeast_le law (observation.pow power) (threshold ^ power)
      (ENNReal.pow_ne_zero positive power) (ENNReal.pow_ne_top finite)

/-- Probability that the charged cost exceeds a threshold at any time, including
    on paths that subsequently fail or never return. The counter supplied here
    should subtract the caller's initial clock when measuring one invocation. -/
def costProbability {State : Type u} (law : Measure (Run State))
    (counter : State → ℕ) (threshold : ℝ≥0∞) : ℝ≥0∞ :=
  probability law (Event.exceeds (Observable.total counter) threshold)

/-- Total-cost tails can be proved with the ordinary local-event interface. -/
theorem costProbability_eq_ever {State : Type u} (law : Measure (Run State))
    (counter : State → ℕ) (threshold : ℝ≥0∞) :
    costProbability law counter threshold =
      probability law (Event.ever fun sample =>
        ∃ state, sample = some state ∧ threshold < (counter state : ℝ≥0∞)) := by
  unfold costProbability probability
  apply congrArg law
  ext run
  exact Observable.total_exceeds_iff counter threshold run

/-- Runtime-tail probabilities are increasing limits of bounded-time events.
    No successful-return hypothesis or conditioning is used. -/
theorem costProbability_eq_iSup_within {State : Type u} (law : Measure (Run State))
    (counter : State → ℕ) (threshold : ℝ≥0∞) :
    costProbability law counter threshold =
      ⨆ steps : ℕ, probability law (Event.within steps fun sample =>
        ∃ state, sample = some state ∧ threshold < (counter state : ℝ≥0∞)) := by
  rw [costProbability_eq_ever, probability_ever]

/-- A finite positive budget bounds the probability of excessive runtime by
    expected total charged cost divided by that budget. -/
theorem costProbability_le {State : Type u} (law : Measure (Run State))
    (counter : State → ℕ) (threshold : ℝ≥0∞)
    (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    costProbability law counter threshold ≤
      expected law (Observable.total counter) / threshold :=
  probability_exceeds_le law (Observable.total counter) threshold positive finite

/-- A nonlinear runtime moment can improve the runtime-tail guarantee. -/
theorem costProbability_le_moment {State : Type u} (law : Measure (Run State))
    (counter : State → ℕ) (threshold : ℝ≥0∞) (power : ℕ)
    (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    costProbability law counter threshold ≤
      expected law ((Observable.total counter).pow power) / threshold ^ power :=
  probability_exceeds_le_moment law (Observable.total counter) threshold power positive finite

end Algo2LeanProbability
