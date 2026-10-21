import Algo2LeanProbability.Observations

/-! Regression proofs for complete-path observations, including failure,
nontermination, correlated counters, and nonlinear runtime bounds. -/

noncomputable section
open MeasureTheory Algo2LeanProbability
open scoped ENNReal

namespace ProbabilityObservations

-- A failing execution retains the seven ticks charged before its error.
def failedRun : Run Nat := fun time => if time = 0 then some 7 else none

theorem failedRun_cost : (Observable.total id).value failedRun = 7 := by
  apply le_antisymm
  · apply iSup_le
    intro time
    by_cases zero : time = 0 <;> simp [failedRun, zero]
  · exact le_iSup_of_le 0 (by simp [failedRun])

example : costProbability (Measure.dirac failedRun) id 6 = 1 := by
  unfold costProbability probability
  rw [Measure.dirac_apply' _ (Event.exceeds _ _).measurable]
  simp only [Event.exceeds, Set.indicator_apply, Set.mem_ofPred_eq]
  norm_num [failedRun_cost]

-- The same interface computes a nonlinear cost moment.
example : expected (Measure.dirac failedRun) ((Observable.total id).pow 2) = 49 := by
  unfold expected
  rw [lintegral_dirac' _ (Observable.pow _ _).measurable]
  rw [Observable.pow_value, failedRun_cost]
  norm_num

-- An execution that keeps ticking forever has infinite total charged cost.
def foreverRun : Run Nat := fun time => some time

example : (Observable.total id).value foreverRun = ∞ := by
  exact ENNReal.iSup_natCast

-- Two counters can be observed together; their correlation is not discarded.
example (law : Measure (Run Nat)) :
    expected law ((Observable.total id).combine (Observable.total (fun n => 2 * n))
      (fun pair => pair.1 * pair.2) (measurable_fst.mul measurable_snd)) =
    expected law ((Observable.total id).mul (Observable.total (fun n => 2 * n))) := rfl

example (law : Measure (Run Nat)) :
    costProbability law id 10 ≤ expected law ((Observable.total id).pow 2) / 100 := by
  convert costProbability_le_moment law id 10 2 (by norm_num) (by norm_num) using 1
  norm_num

end ProbabilityObservations
