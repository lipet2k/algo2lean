import Algo2LeanProbability
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanCore Algo2LeanProbability MeasureTheory
open scoped ENNReal

namespace ProbabilityExamples

/-- One die draw, followed by successful termination. -/
def die : Option Int → Choice (Option Int)
  | none => .uniform 1 7 some
  | some _ => .halt

/-- Every die face has probability 1/6 in the full execution law. The upper
    endpoint 7 is excluded, and all other integers have probability zero. -/
theorem die_face (face : Int) :
    probability (execution die none) (Event.atTime 1 (fun state => state = some (some face))) =
      if 1 ≤ face ∧ face < 7 then (6 : ℝ≥0∞)⁻¹ else 0 := by
  rw [probability_atTime, finiteLaw_one]
  change (choiceLaw (none : Option Int) (.uniform 1 7 some)).toMeasure
    {state | state = some (some face)} = _
  rw [choiceLaw_uniform _ _ _ _ (by decide),
    PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete]
  have preimage : (fun value : Int => (some (some value) : SampleState (Option Int))) ⁻¹'
      {state | state = some (some face)} = {face} := by ext; simp
  have mapped := congrArg (fun event : Set Int => (uniformInt 1 7 (by decide)).toMeasure event) preimage
  calc
    _ = (uniformInt 1 7 (by decide)).toMeasure {face} := mapped
    _ = uniformInt 1 7 (by decide) face := PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    _ = _ := by rw [uniformInt_apply]; rfl

/-- An invalid interval fails with probability one after its first instruction. -/
theorem empty_interval_fails (bound : Int) :
    probability (execution (fun _ : Unit => Choice.uniform bound bound (fun _ => ())) ())
      (Event.atTime 1 (fun state => state = none)) = 1 := by
  rw [probability_atTime, finiteLaw_one]
  simp [choiceLaw, PMF.toMeasure_pure, Measure.dirac_apply']

/-- A deterministic instruction is a probability-one transition. -/
theorem deterministic_instruction (value : Int) :
    probability (execution (fun _ : Int => Choice.next value) 0)
      (Event.atTime 1 (fun state => state = some value)) = 1 := by
  rw [probability_atTime, finiteLaw_one]
  simp [choiceLaw, PMF.toMeasure_pure, Measure.dirac_apply']

end ProbabilityExamples
