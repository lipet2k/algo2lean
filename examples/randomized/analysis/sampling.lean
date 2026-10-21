import Algo.sampling.Probability

/-!
The die returns each integer from one through six with probability one sixth,
and terminates with probability one. The joint-postcondition theorem also shows
that the caller's heap is unchanged. These claims concern eventual returns in
the full execution law, including failure and divergence as possible events.
-/

noncomputable section
namespace SamplingAnalysis
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Algo2LeanProbability
open Algo.sampling Algo.sampling.Algo2LeanGenerated
open Algo2LeanGenerated

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The exact probability of any joint heap/output postcondition. A die draw
    preserves the supplied heap and is uniform on the half-open interval `[1, 7)`. -/
theorem die_return_probability (heap : Heap) (post : Heap → Int → Prop) :
    die.returnProbability heap () post =
      (uniformInt 1 7 (by omega)).toMeasure {value | post heap value} := by
  classical
  let initial := die.initial heap ()
  let event : SampleState Configuration → Prop := fun state =>
    ∃ current output, state = some current ∧ die.outcome current = some output ∧ post output.1 output.2
  -- Once this call returns, its outcome remains visible in the padded execution.
  have preserve : ∀ state, event state →
      ∀ᵐ after ∂(transition nextChoice state).toMeasure, event after := by
    intro state valid
    obtain ⟨current, output, rfl, observed, accepted⟩ := valid
    cases current with
    | active h frame stack => simp [die.outcome] at observed
    | done h result =>
      have valid : event (some (.done h result)) := ⟨_, _, rfl, observed, accepted⟩
      change ∀ᵐ after ∂(PMF.pure (some (.done h result)) : PMF (SampleState Configuration)).toMeasure, event after
      rw [PMF.toMeasure_pure]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 valid
  let finish : Int → SampleState Configuration := fun value => some (.done heap (.fn_die value))
  -- Evaluate both bounds, sample once, then return: four instructions in total.
  have at_four : finiteLaw nextChoice initial 4 =
      ((uniformInt 1 7 (by omega)).map finish).toMeasure := by
    let first : Configuration := .active heap (.fn_die 3 { t1 := 1 }) []
    let ready : Configuration := .active heap (.fn_die 2 { t1 := 1, t2 := 7 }) []
    let pending : Int → Configuration := fun value =>
      .active heap (.fn_die 1 { t0 := value, t1 := 1, t2 := 7 }) []
    have step₀ : transition nextChoice (some initial) = PMF.pure (some first) := rfl
    have step₁ : transition nextChoice (some first) = PMF.pure (some ready) := rfl
    have step₂ : transition nextChoice (some ready) =
        (uniformInt 1 7 (by omega)).map (fun value => some (pending value)) := by
      change choiceLaw ready (.uniform 1 7 pending) = _
      exact choiceLaw_uniform ready 1 7 pending (by omega)
    have step₃ (value : Int) : transition nextChoice (some (pending value)) =
        PMF.pure (finish value) := rfl
    rw [finiteLaw_eq_toMeasure]
    congr 1
    simp only [finitePMF, PMF.pure_bind, step₀, step₁, step₂, PMF.bind_map]
    change (uniformInt 1 7 (by omega)).bind (fun value => transition nextChoice (some (pending value))) = _
    simp_rw [step₃]
    rfl
  -- All four-step outcomes are successful final states; later steps preserve them.
  have stopped : ∀ᵐ state ∂finiteLaw nextChoice initial 4,
      transition nextChoice state = PMF.pure state := by
    rw [at_four, ← PMF.toMeasure_map finish _ Measurable.of_discrete]
    apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).2
    exact Filter.Eventually.of_forall (fun value => rfl)
  have eventual := probability_ever_of_stopped nextChoice initial event preserve 4 stopped
  simp only [die.returnProbability, die.law, die.ValidInput, if_true,
    Event.returnsWhere]
  change probability (execution nextChoice initial) (Event.ever event) = _
  rw [eventual, at_four, PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete]
  congr 1
  ext value
  change event (finish value) ↔ post heap value
  constructor
  · rintro ⟨current, output, same, observed, accepted⟩
    have current_eq : current = .done heap (.fn_die value) := Option.some.inj same.symm
    subst current
    have output_eq : output = (heap, value) := Option.some.inj observed.symm
    simpa [output_eq] using accepted
  · exact fun accepted => ⟨_, _, rfl, rfl, accepted⟩

-- Main result: Correctness
/-- Every face from one through six is returned with probability exactly one sixth.
    All other integer outputs have probability zero. -/
theorem die_output_probability (face : Int) :
    die.outputProbability () face =
      if 1 ≤ face ∧ face < 7 then (6 : ENNReal)⁻¹ else 0 := by
  classical
  unfold die.outputProbability
  rw [die_return_probability]
  change (uniformInt 1 7 (by omega)).toMeasure {value | value = face} = _
  rw [show {value : Int | value = face} = {face} by ext value; simp]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [uniformInt_apply]
  rfl

/-- The die returns with probability one for every initial heap. -/
theorem die_terminates_almost_surely (heap : Heap) :
    die.terminationProbability heap () = 1 := by
  unfold die.terminationProbability
  rw [die_return_probability]
  simp

end SamplingAnalysis
