import Algo.client.Probability
import Algo.sampler.Analysis
import Algo2LeanProbability.CallContext

/-! Reuse a partial callee contract without renormalizing its successful mass.
The full-path work lower bound also counts the branch that never returns. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PartialClientAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability MeasureTheory
open Algo.client Algo.client.Algo2LeanGenerated
open scoped ENNReal

private def insideSampler : Frame → Bool
  | .import_0 _ _ _ => true
  | _ => false

private def resume : Algo.sampler.Algo2LeanGenerated.Result → Frame
  | .fn_sometimes value => .fn_run 3 {t2 := value}

/-- The callee's unconditional reward contract is reused unchanged. Its missing
half of the probability mass remains missing after the caller continues. -/
theorem run_expected (heap : Heap) (reward : Heap → Int → ℝ≥0∞) :
    run.expectedReturn heap () reward = reward (heap.tick "work") 8 * (2 : ℝ≥0∞)⁻¹ := by
  let payoff : Heap × Int → ℝ≥0∞ := fun result => reward result.1 result.2
  let continuation : Heap × Int → ℝ≥0∞ := fun result =>
    callExpected nextChoice run.outcome (.active result.1 (.fn_run 3 {t2 := result.2}) []) payoff
  have reuse := callExpected_import Algo.sampler.Algo2LeanGenerated.nextChoice nextChoice
    Algo.sampler.sometimes.outcome run.outcome Frame.import_0 insideSampler resume []
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intro result; cases result; rfl)
    heap (Algo.sampler.entry_sometimes ()) payoff continuation
    (by intro h result; cases result; rfl)
  simp only [run.expectedReturn, run.ValidInput, if_true]
  rw [callExpected_next nextChoice run.outcome (run.initial heap ())
    (.active heap (.import_0 (Algo.sampler.entry_sometimes ()) [] resume) []) rfl rfl payoff]
  rw [reuse]
  have contract := PartialSamplerAnalysis.sometimes_expected heap
    (fun final value => continuation (final, value))
  simp only [Algo.sampler.sometimes.expectedReturn, Algo.sampler.sometimes.ValidInput, if_true] at contract
  change callExpected Algo.sampler.Algo2LeanGenerated.nextChoice Algo.sampler.sometimes.outcome
    (.active heap (Algo.sampler.entry_sometimes ()) []) continuation =
    continuation (heap.tick "work", 7) * (2 : ℝ≥0∞)⁻¹ at contract
  rw [contract]
  congr 1
  change callExpected nextChoice run.outcome
    (.active (heap.tick "work") (.fn_run 3 {t2 := 7}) []) payoff = _
  rw [callExpected_next nextChoice run.outcome _ _ rfl (by rfl)]
  rw [callExpected_next nextChoice run.outcome _ _ rfl (by rfl)]
  rw [callExpected_next nextChoice run.outcome _ _ rfl (by rfl)]
  exact callExpected_return nextChoice run.outcome _ (heap.tick "work", 8) rfl payoff

/-- Successful return has probability one half, rather than one after conditioning. -/
theorem successful_mass (heap : Heap) : run.terminationProbability heap () = 1 / 2 := by
  rw [run.terminationProbability, run.returnProbability_eq_expectedReturn heap () trivial, run_expected]
  norm_num

/-- Only the successful half contributes to completed-return work rewards. -/
theorem completed_work (heap : Heap) :
    run.expectedReturn heap () (fun final _ => (Heap.cost heap final "work" : ℝ≥0∞)) = 1 / 2 := by
  rw [run_expected]
  simp

/-- Within two caller instructions, every path has charged one work tick.
The lower bound uses a finite marginal of the actual generated path law;
it does not assume that the call eventually returns. -/
theorem retained_total_work (heap : Heap) : 1 ≤ run.expectedCost heap () "work" := by
  let charged : Configuration := .active (heap.tick "work")
    (.import_0 (.fn_sometimes 13 {}) [] resume) []
  let value : SampleState Configuration → ℝ≥0∞ := fun sample =>
    ((match sample with | none => 0 | some state => Heap.cost heap state.heap "work" : Nat) : ℝ≥0∞)
  have first : transition nextChoice (some (run.initial heap ())) =
      PMF.pure (some (.active heap (.import_0 (Algo.sampler.entry_sometimes ()) [] resume) [])) := rfl
  have second : transition nextChoice
      (some (.active heap (.import_0 (Algo.sampler.entry_sometimes ()) [] resume) [])) =
      PMF.pure (some charged) := rfl
  have atTwo : finitePMF nextChoice (run.initial heap ()) 2 = PMF.pure (some charged) := by
    simp only [finitePMF, PMF.pure_bind, first, second]
  have observed : expected (execution nextChoice (run.initial heap ()))
      (Observable.atTime 2 value) = 1 := by
    rw [expected_atTime, finiteLaw_eq_toMeasure, atTwo, PMF.toMeasure_pure,
      lintegral_dirac' _ Measurable.of_discrete]
    simp [value, charged, Config.heap]
  have lower := expected_mono (execution nextChoice (run.initial heap ()))
    (Observable.atTime 2 value) (run.cost heap "work") (fun path => by
      simp only [Observable.atTime, run.cost, Observable.total]
      apply le_iSup_of_le 2
      cases path 2 <;> simp [value])
  rw [observed] at lower
  simpa only [run.expectedCost, run.law, run.ValidInput, if_true] using lower

/-- A return-only runtime reward would lose the work on divergent executions. -/
theorem return_cost_is_not_total_cost (heap : Heap) :
    run.expectedReturn heap () (fun final _ => (Heap.cost heap final "work" : ℝ≥0∞)) <
      run.expectedCost heap () "work" := by
  rw [completed_work]
  exact lt_of_lt_of_le (by norm_num) (retained_total_work heap)

end PartialClientAnalysis
