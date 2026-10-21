import Algo.driver.Probability
import Algo.client.Analysis
import Algo2LeanProbability.CallContext

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace DriverAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo.driver Algo.driver.Algo2LeanGenerated
open Algo2LeanProbability

/-- A further source module reuses the whole mixed composition unchanged. -/
theorem run_hasLaw (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef) :
    run.HasLaw heap a (ClientAnalysis.sampleLaw heap a) := by
  intro reward
  change run.expectedReturn heap a (fun final value => reward (final, value)) =
    pmfExpected (ClientAnalysis.sampleLaw heap a) reward
  simp only [run.expectedReturn, run.ValidInput, if_pos valid]
  rw [callExpected_next nextChoice run.outcome _ _ rfl rfl]
  rw [callExpected_next nextChoice run.outcome _ _ rfl rfl]
  let inside : Frame → Bool := fun frame => match frame with
    | .import_1 _ _ _ => true
    | _ => false
  let resume : Algo.client.Algo2LeanGenerated.Result → Frame :=
    fun result => match result with
      | .fn_sample value => .fn_run 1 {v0 := a, t1 := value, t2 := a}
  have reuse := callExpected_import Algo.client.Algo2LeanGenerated.nextChoice nextChoice
    Algo.client.sample.outcome run.outcome Frame.import_1 inside resume []
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intro result; cases result; rfl)
    heap (Algo.client.entry_sample a) reward reward
    (by
      intro final result
      cases result
      rw [callExpected_next nextChoice run.outcome _ _ rfl rfl]
      exact callExpected_return nextChoice run.outcome _ _ rfl reward)
  apply reuse.trans
  have contract := ClientAnalysis.sample_hasLaw heap a valid reward
  simpa only [Algo.client.sample.HasLaw, Algo.client.sample.ValidInput, if_pos valid,
    Algo.client.sample.initial, Algo.client.entry_sample, start, pmfExpected] using contract

end DriverAnalysis
#print axioms DriverAnalysis.run_hasLaw
