import RealDrawProbability

/-!
A uniform integer from [0, 2) becomes an exact real after division by two.
The generated program returns 0 and 1/2 with equal probability, preserves its
actual input heap, and terminates almost surely without conditioning on success.
-/

noncomputable section
namespace RealProbability
open Algo2LeanGenerated Algo2LeanProbability
open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def bit : PMF Int := uniformInt 0 2 (by omega)

private theorem finite_draw_law (heap : Heap) :
    finitePMF nextChoice (draw.initial heap ()) 6 =
      bit.map (fun (value : Int) =>
        (some (.done heap (.fn_draw ((value : ℝ) / 2))) : SampleState Configuration)) := by
  let lower : Configuration := .active heap (.fn_draw 5 {}) []
  let ready : Configuration := .active heap (.fn_draw 4 { t4 := 2 }) []
  let sampled (value : Int) : Configuration :=
    .active heap (.fn_draw 3 { t1 := value, t4 := 2 }) []
  let divisor (value : Int) : Configuration :=
    .active heap (.fn_draw 2 { t1 := value, t2 := 2, t4 := 2 }) []
  let divided (value : Int) : Configuration :=
    .active heap (.fn_draw 1 { t0 := (value : ℝ) / 2, t1 := value, t2 := 2, t4 := 2 }) []
  let finish (value : Int) : SampleState Configuration :=
    some (.done heap (.fn_draw ((value : ℝ) / 2)))
  have step₀ : transition nextChoice (some (draw.initial heap ())) = PMF.pure (some lower) := rfl
  have step₁ : transition nextChoice (some lower) = PMF.pure (some ready) := rfl
  have step₂ : transition nextChoice (some ready) = bit.map (fun value => some (sampled value)) := by
    exact choiceLaw_uniform ready 0 2 sampled (by omega)
  have step₃ (value : Int) :
      transition nextChoice (some (sampled value)) = PMF.pure (some (divisor value)) := rfl
  have step₄ (value : Int) :
      transition nextChoice (some (divisor value)) = PMF.pure (some (divided value)) := by
    change choiceLaw (divisor value)
      (if (2 : ℝ) ≠ 0 then .next (divided value) else .fail) = _
    rw [if_pos (by norm_num)]
    rfl
  have step₅ (value : Int) :
      transition nextChoice (some (divided value)) = PMF.pure (finish value) := rfl
  simp only [finitePMF, PMF.pure_bind, step₀, step₁, step₂, PMF.bind_map,
    Function.comp_def, PMF.bind_bind, step₃, step₄, step₅]
  rfl

/-- Every joint heap/output event is the pushforward of the original integer draw. -/
theorem return_probability (heap : Heap) (post : Heap → ℝ → Prop) :
    draw.returnProbability heap () post =
      bit.toMeasure {value | post heap ((value : ℝ) / 2)} := by
  classical
  let initial := draw.initial heap ()
  let event : SampleState Configuration → Prop := fun state =>
    ∃ current output, state = some current ∧ draw.outcome current = some output ∧ post output.1 output.2
  have preserve : ∀ state, event state →
      ∀ᵐ after ∂(transition nextChoice state).toMeasure, event after := by
    intro state valid
    obtain ⟨current, output, rfl, observed, accepted⟩ := valid
    cases current with
    | active h frame stack => simp [draw.outcome] at observed
    | done h result =>
      have valid : event (some (.done h result)) := ⟨_, _, rfl, observed, accepted⟩
      change ∀ᵐ after ∂(PMF.pure (some (.done h result)) : PMF (SampleState Configuration)).toMeasure, event after
      rw [PMF.toMeasure_pure]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 valid
  let finish : Int → SampleState Configuration := fun value =>
    some (.done heap (.fn_draw ((value : ℝ) / 2)))
  have at_six : finiteLaw nextChoice initial 6 = (bit.map finish).toMeasure := by
    rw [finiteLaw_eq_toMeasure, finite_draw_law]
  have stopped : ∀ᵐ state ∂finiteLaw nextChoice initial 6,
      transition nextChoice state = PMF.pure state := by
    rw [at_six, ← PMF.toMeasure_map finish _ Measurable.of_discrete]
    apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).2
    exact Filter.Eventually.of_forall (fun value => rfl)
  have eventual := probability_ever_of_stopped nextChoice initial event preserve 6 stopped
  simp only [draw.returnProbability, draw.law, draw.ValidInput, if_true, Event.returnsWhere]
  change probability (execution nextChoice initial) (Event.ever event) = _
  rw [eventual, at_six, PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete]
  congr 1
  ext value
  change event (finish value) ↔ post heap ((value : ℝ) / 2)
  constructor
  · rintro ⟨current, output, same, observed, accepted⟩
    have current_eq : current = .done heap (.fn_draw ((value : ℝ) / 2)) := Option.some.inj same.symm
    subst current
    have output_eq : output = (heap, (value : ℝ) / 2) := Option.some.inj observed.symm
    simpa [output_eq] using accepted
  · exact fun accepted => ⟨_, _, rfl, rfl, accepted⟩

theorem output_probability (value : Int) (bounds : 0 ≤ value ∧ value < 2) :
    draw.outputProbability () ((value : ℝ) / 2) = (1 / 2 : ENNReal) := by
  classical
  unfold draw.outputProbability
  rw [return_probability]
  change bit.toMeasure {other | (other : ℝ) / 2 = (value : ℝ) / 2} = _
  rw [show {other : Int | (other : ℝ) / 2 = (value : ℝ) / 2} = {value} by
    ext other
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, div_left_inj' (by norm_num : (2 : ℝ) ≠ 0), Int.cast_inj]]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [bit, uniformInt_apply, bounds, Int.toNat]

theorem output_zero : draw.outputProbability () 0 = (1 / 2 : ENNReal) := by
  simpa using output_probability 0 (by omega)

theorem output_one_half : draw.outputProbability () (1 / 2) = (1 / 2 : ENNReal) := by
  simpa using output_probability 1 (by omega)

theorem returns_with_unchanged_heap (heap : Heap) :
    draw.returnProbability heap () (fun after _ => after = heap) = 1 := by
  rw [return_probability]
  simp

theorem terminates_almost_surely (heap : Heap) :
    draw.terminationProbability heap () = 1 := by
  rw [draw.terminationProbability, return_probability]
  simp

end RealProbability
