import TossesProbability

/-!
Two identical random expressions in a tuple make independent fresh draws.
The generated program returns each binary pair with probability one quarter,
retains the supplied heap, and terminates almost surely.
-/

noncomputable section
namespace TupleProbability
open Algo2LeanGenerated Algo2LeanProbability
open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def bit : PMF Int := uniformInt 0 2 (by omega)

/-- The second draw uses the same distribution independently of the first value. -/
private def pairLaw : PMF (Int × Int) :=
  bit.bind (fun first => bit.map (fun second => (first, second)))

private theorem pairLaw_mass (first second : Int) :
    pairLaw (first, second) = bit first * bit second := by
  classical
  have fixed (value : Int) :
      (bit.map (fun next => (value, next))) (first, second) =
        if first = value then bit second else 0 := by
    rw [PMF.map_apply]
    by_cases same : first = value
    · subst value
      simp
    · simp [same]
  rw [pairLaw, PMF.bind_apply]
  simp_rw [fixed]
  simp [mul_ite]

/-- The eight generated instructions retain two distinct random choices and
    construct their ordered pair only after both expressions have been evaluated. -/
private theorem finite_pair_law (heap : Heap) :
    finitePMF nextChoice (tosses.initial heap ()) 8 =
      pairLaw.map (fun pair => (some (.done heap (.fn_tosses pair)) : SampleState Configuration)) := by
  let firstBound : Configuration := .active heap (.fn_tosses 7 {}) []
  let firstReady : Configuration := .active heap (.fn_tosses 6 {t6 := 2}) []
  let firstDraw (first : Int) : Configuration :=
    .active heap (.fn_tosses 5 {t1 := first, t6 := 2}) []
  let secondBound (first : Int) : Configuration :=
    .active heap (.fn_tosses 4 {t1 := first, t6 := 2}) []
  let secondReady (first : Int) : Configuration :=
    .active heap (.fn_tosses 3 {t1 := first, t4 := 2, t6 := 2}) []
  let secondDraw (first second : Int) : Configuration :=
    .active heap (.fn_tosses 2 {t1 := first, t2 := second, t4 := 2, t6 := 2}) []
  let paired (first second : Int) : Configuration :=
    .active heap (.fn_tosses 1 {t0 := (first, second), t1 := first, t2 := second, t4 := 2, t6 := 2}) []
  let finish (pair : Int × Int) : SampleState Configuration :=
    some (.done heap (.fn_tosses pair))
  have step₀ : transition nextChoice (some (tosses.initial heap ())) =
      PMF.pure (some firstBound) := rfl
  have step₁ : transition nextChoice (some firstBound) =
      PMF.pure (some firstReady) := rfl
  have step₂ : transition nextChoice (some firstReady) =
      bit.map (fun first => some (firstDraw first)) := by
    exact choiceLaw_uniform firstReady 0 2 firstDraw (by omega)
  have step₃ (first : Int) : transition nextChoice (some (firstDraw first)) =
      PMF.pure (some (secondBound first)) := rfl
  have step₄ (first : Int) : transition nextChoice (some (secondBound first)) =
      PMF.pure (some (secondReady first)) := rfl
  have step₅ (first : Int) : transition nextChoice (some (secondReady first)) =
      bit.map (fun second => some (secondDraw first second)) := by
    exact choiceLaw_uniform (secondReady first) 0 2 (secondDraw first) (by omega)
  have step₆ (first second : Int) : transition nextChoice (some (secondDraw first second)) =
      PMF.pure (some (paired first second)) := rfl
  have step₇ (first second : Int) : transition nextChoice (some (paired first second)) =
      PMF.pure (finish (first, second)) := rfl
  simp only [finitePMF, PMF.pure_bind, step₀, step₁, step₂, PMF.bind_map,
    Function.comp_def, PMF.bind_bind, step₃, step₄, step₅, step₆, step₇]
  simp only [pairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

/-- A joint heap/output postcondition is measured against the product law of
    the two draws. This also records that every outcome preserves the heap. -/
theorem return_probability (heap : Heap) (post : Heap → (Int × Int) → Prop) :
    tosses.returnProbability heap () post = pairLaw.toMeasure {pair | post heap pair} := by
  classical
  let initial := tosses.initial heap ()
  let event : SampleState Configuration → Prop := fun state =>
    ∃ current output, state = some current ∧ tosses.outcome current = some output ∧ post output.1 output.2
  have preserve : ∀ state, event state →
      ∀ᵐ after ∂(transition nextChoice state).toMeasure, event after := by
    intro state valid
    obtain ⟨current, output, rfl, observed, accepted⟩ := valid
    cases current with
    | active h frame stack => simp [tosses.outcome] at observed
    | done h result =>
      have valid : event (some (.done h result)) := ⟨_, _, rfl, observed, accepted⟩
      change ∀ᵐ after ∂(PMF.pure (some (.done h result)) : PMF (SampleState Configuration)).toMeasure, event after
      rw [PMF.toMeasure_pure]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 valid
  let finish : (Int × Int) → SampleState Configuration := fun pair =>
    some (.done heap (.fn_tosses pair))
  have at_eight : finiteLaw nextChoice initial 8 = (pairLaw.map finish).toMeasure := by
    rw [finiteLaw_eq_toMeasure, finite_pair_law]
  have stopped : ∀ᵐ state ∂finiteLaw nextChoice initial 8,
      transition nextChoice state = PMF.pure state := by
    rw [at_eight, ← PMF.toMeasure_map finish _ Measurable.of_discrete]
    apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).2
    exact Filter.Eventually.of_forall (fun pair => rfl)
  have eventual := probability_ever_of_stopped nextChoice initial event preserve 8 stopped
  simp only [tosses.returnProbability, tosses.law, tosses.ValidInput, if_true, Event.returnsWhere]
  change probability (execution nextChoice initial) (Event.ever event) = _
  rw [eventual, at_eight, PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete]
  congr 1
  ext pair
  change event (finish pair) ↔ post heap pair
  constructor
  · rintro ⟨current, output, same, observed, accepted⟩
    have current_eq : current = .done heap (.fn_tosses pair) := Option.some.inj same.symm
    subst current
    have output_eq : output = (heap, pair) := Option.some.inj observed.symm
    simpa [output_eq] using accepted
  · exact fun accepted => ⟨_, _, rfl, rfl, accepted⟩

/-- Each binary pair is returned with probability one quarter. -/
theorem output_probability (first second : Int)
    (first_bit : 0 ≤ first ∧ first < 2) (second_bit : 0 ≤ second ∧ second < 2) :
    tosses.outputProbability () (first, second) = (4 : ENNReal)⁻¹ := by
  classical
  unfold tosses.outputProbability
  rw [return_probability]
  change pairLaw.toMeasure {pair | pair = (first, second)} = _
  rw [show {pair : Int × Int | pair = (first, second)} = {(first, second)} by ext pair; simp]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), pairLaw_mass]
  norm_num [bit, uniformInt_apply, first_bit, second_bit]
  change (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ = (4 : ENNReal)⁻¹
  rw [← ENNReal.mul_inv (a := 2) (b := 2) (Or.inl (by norm_num)) (Or.inr (by norm_num))]
  norm_num

/-- All outcomes return with the original heap; invalid outcomes have no mass. -/
theorem returns_with_unchanged_heap (heap : Heap) :
    tosses.returnProbability heap () (fun after _ => after = heap) = 1 := by
  rw [return_probability]
  simp

example : tosses.outputProbability () (0, 0) = (4 : ENNReal)⁻¹ :=
  output_probability 0 0 (by omega) (by omega)
example : tosses.outputProbability () (0, 1) = (4 : ENNReal)⁻¹ :=
  output_probability 0 1 (by omega) (by omega)
example : tosses.outputProbability () (1, 0) = (4 : ENNReal)⁻¹ :=
  output_probability 1 0 (by omega) (by omega)
example : tosses.outputProbability () (1, 1) = (4 : ENNReal)⁻¹ :=
  output_probability 1 1 (by omega) (by omega)

end TupleProbability
