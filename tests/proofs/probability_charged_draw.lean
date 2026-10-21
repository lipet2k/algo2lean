import ChargedDrawProbability
import Algo2LeanProbability.CallObservations

/-!
A generated random draw charges its sampled value to the `work` clock.
The joint return-reward theorem retains the original heap counters and proves
the exact second moment of the increment, together with a general path-tail
bound. Only the local operational helper inspects generated instructions.
-/

noncomputable section
namespace ChargedDrawAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem after_draw (heap : Heap) (value : Int) (nonnegative : 0 ≤ value)
    (reward : Heap → Int → ℝ≥0∞) :
    callExpected nextChoice charged_draw.outcome
      (.active heap (.fn_charged_draw 4 {t2 := value, t4 := 4}) [])
      (fun result => reward result.1 result.2) = reward (heap.tick "work" value.toNat) value := by
  let state : State_charged_draw := {v0 := value, t2 := value, t4 := 4}
  let after := heap.tick "work" value.toNat
  let payoff : Heap × Int → ℝ≥0∞ := fun result => reward result.1 result.2
  calc
    _ = callExpected nextChoice charged_draw.outcome
        (.active heap (.fn_charged_draw 3 state) []) payoff :=
      callExpected_next nextChoice charged_draw.outcome _ _ rfl rfl payoff
    _ = callExpected nextChoice charged_draw.outcome
        (.active after (.fn_charged_draw 2 state) []) payoff := by
      apply callExpected_next nextChoice charged_draw.outcome _ _ rfl
      change (if 0 ≤ value then _ else _) = _
      simp only [nonnegative, ↓reduceIte]
      rfl
    _ = callExpected nextChoice charged_draw.outcome
        (.active after (.fn_charged_draw 1 {state with t1 := value}) []) payoff :=
      callExpected_next nextChoice charged_draw.outcome _ _ rfl rfl payoff
    _ = callExpected nextChoice charged_draw.outcome
        (.done after (.fn_charged_draw value)) payoff :=
      callExpected_next nextChoice charged_draw.outcome _ _ rfl rfl payoff
    _ = _ := callExpected_return nextChoice charged_draw.outcome _ (after, value) rfl payoff

/-- Every nonnegative joint reward is averaged over the four outcomes. Because
    the final heap is retained, the reward can combine outputs, costs, and
    preserved caller storage without another execution proof. -/
theorem expected_reward (heap : Heap) (reward : Heap → Int → ℝ≥0∞) :
    charged_draw.expectedReturn heap () reward =
      ∑ value ∈ Finset.Ico (0 : Int) 4,
        reward (heap.tick "work" value.toNat) value * (4 : ℝ≥0∞)⁻¹ := by
  let first : Configuration := .active heap (.fn_charged_draw 6 {}) []
  let ready : Configuration := .active heap (.fn_charged_draw 5 {t4 := 4}) []
  let resume (value : Int) : Configuration :=
    .active heap (.fn_charged_draw 4 {t2 := value, t4 := 4}) []
  let payoff : Heap × Int → ℝ≥0∞ := fun result => reward result.1 result.2
  simp only [charged_draw.expectedReturn, charged_draw.ValidInput, if_true]
  rw [callExpected_next nextChoice charged_draw.outcome
    (charged_draw.initial heap ()) first rfl rfl payoff]
  rw [callExpected_next nextChoice charged_draw.outcome first ready rfl rfl payoff]
  rw [callExpected_uniform nextChoice charged_draw.outcome ready 0 4 resume rfl rfl
    (by omega) payoff]
  apply Finset.sum_congr rfl
  intro value member
  rw [show callExpected nextChoice charged_draw.outcome (resume value) payoff =
      reward (heap.tick "work" value.toNat) value from
    after_draw heap value (Finset.mem_Ico.mp member).1 reward]
  rfl

/-- The reusable law carries the charged final heap jointly with the draw. -/
def drawLaw (heap : Heap) : PMF (Heap × Int) :=
  (uniformInt 0 4 (by omega)).map (fun value => (heap.tick "work" value.toNat, value))

theorem call_law (heap : Heap) : charged_draw.HasLaw heap () (drawLaw heap) := by
  intro payoff
  change charged_draw.expectedReturn heap () (fun heap value => payoff (heap, value)) =
    pmfExpected (drawLaw heap) payoff
  rw [expected_reward, drawLaw, pmfExpected_map, pmfExpected_uniformInt]
  rfl

private theorem observed_halts (state : Configuration) (output : Heap × Int)
    (seen : charged_draw.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | active => simp [charged_draw.outcome] at seen
  | done => rfl

private theorem counter_advance (heap : Heap) (before after : Configuration)
    (allowed : (nextChoice before).Allows after) :
    Heap.cost heap before.heap "work" ≤ Heap.cost heap after.heap "work" := by
  cases choice_step.mp allowed with
  | charged_draw_pc1 h s stack => cases stack <;> exact le_rfl
  | charged_draw_pc2 => exact le_rfl
  | charged_draw_pc3 h s stack _ =>
      exact Nat.sub_le_sub_right (Heap.clocks_le_tick h "work" "work" s.v0.toNat) _
  | charged_draw_pc4 => exact le_rfl
  | charged_draw_pc5 => exact le_rfl
  | charged_draw_pc6 => exact le_rfl
  | charged_draw_pc7 => exact le_rfl

private theorem counter_agrees (heap : Heap) (state : Configuration) (output : Heap × Int)
    (seen : charged_draw.outcome state = some output) :
    Heap.cost heap state.heap "work" = Heap.cost heap output.1 "work" := by
  cases state with
  | active => simp [charged_draw.outcome] at seen
  | done h result =>
      cases result
      simp only [charged_draw.outcome, Option.some.injEq] at seen
      cases seen
      rfl

private theorem completes (heap : Heap) :
    callProbability nextChoice charged_draw.outcome (charged_draw.initial heap ()) (fun _ => True) = 1 := by
  have contract : HasLaw nextChoice charged_draw.outcome (charged_draw.initial heap ()) (drawLaw heap) := by
    simpa only [charged_draw.HasLaw, charged_draw.ValidInput, if_true] using call_law heap
  exact contract.termination

/-- Almost-sure completion connects every measurable total-work reward to the
    already proved joint return law, without another trajectory analysis. -/
theorem total_work_reward (heap : Heap) (reward : ℝ≥0∞ → ℝ≥0∞)
    (measurable : Measurable reward) :
    expected (charged_draw.law heap ()) ((charged_draw.cost heap "work").map reward measurable) =
      charged_draw.expectedReturn heap () (fun after _ => reward (Heap.cost heap after "work")) := by
  simp only [charged_draw.law, charged_draw.cost, charged_draw.expectedReturn,
    charged_draw.ValidInput, if_true]
  exact expected_total_eq_callExpected nextChoice charged_draw.outcome observed_halts
    (charged_draw.initial heap ()) (fun state => Heap.cost heap state.heap "work")
    (fun output => Heap.cost heap output.1 "work") (counter_advance heap)
    (counter_agrees heap) (completes heap) reward measurable

/-- The exact second moment of charged work is `(0² + 1² + 2² + 3²) / 4`.
    Initial counters may be nonzero; only this invocation's increment is used. -/
theorem returned_work_second_moment (heap : Heap) :
    charged_draw.expectedReturn heap ()
      (fun after _ => (Heap.cost heap after "work" : ℝ≥0∞) ^ 2) = 7 / 2 := by
  rw [expected_reward]
  norm_num [Int.toNat, show Finset.Ico (0 : Int) 4 = {0, 1, 2, 3} from by decide]
  apply (ENNReal.toReal_eq_toReal_iff'
    (by simp [ENNReal.mul_eq_top]) (by simp [ENNReal.div_eq_top])).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.mul_eq_top]

/-- The second moment is for total runtime on full paths, not a quantity
    conditioned on successful return. -/
theorem work_second_moment (heap : Heap) :
    expected (charged_draw.law heap ()) ((charged_draw.cost heap "work").pow 2) = 7 / 2 := by
  rw [show (charged_draw.cost heap "work").pow 2 =
    (charged_draw.cost heap "work").map (fun cost => cost ^ 2) (measurable_id.pow_const 2) from rfl]
  rw [total_work_reward, returned_work_second_moment]

/-- Expected total work is the average of the four possible charged values. -/
theorem expected_work (heap : Heap) : charged_draw.expectedCost heap () "work" = 3 / 2 := by
  change expected (charged_draw.law heap ())
    ((charged_draw.cost heap "work").map id measurable_id) = _
  rw [total_work_reward, expected_reward]
  norm_num [Int.toNat, show Finset.Ico (0 : Int) 4 = {0, 1, 2, 3} from by decide]
  apply (ENNReal.toReal_eq_toReal_iff'
    (by simp [ENNReal.mul_eq_top]) (by simp [ENNReal.div_eq_top])).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.mul_eq_top]

/-- Runtime tails reuse the same joint reward theorem as ordinary moments. -/
theorem work_tail_two (heap : Heap) :
    charged_draw.costProbability heap () "work" 2 = (4 : ℝ≥0∞)⁻¹ := by
  classical
  have tail := costProbability_eq_callProbability nextChoice charged_draw.outcome observed_halts
    (charged_draw.initial heap ()) (fun state => Heap.cost heap state.heap "work")
    (fun output => Heap.cost heap output.1 "work") (counter_advance heap)
    (counter_agrees heap) (completes heap) 2
  have converted : charged_draw.costProbability heap () "work" 2 =
      charged_draw.expectedReturn heap ()
        (fun after _ => if (2 : ℝ≥0∞) < (Heap.cost heap after "work" : ℝ≥0∞) then 1 else 0) := by
    simp only [charged_draw.costProbability, charged_draw.law, charged_draw.cost,
      charged_draw.expectedReturn, charged_draw.ValidInput, if_true]
    refine tail.trans ?_
    unfold callProbability
    apply congrArg (callExpected nextChoice charged_draw.outcome (charged_draw.initial heap ()))
    funext result
    by_cases exceeded : (2 : ℝ≥0∞) < (Heap.cost heap result.1 "work" : ℝ≥0∞) <;>
      simp [exceeded]
  rw [converted, expected_reward]
  norm_num [Int.toNat, show Finset.Ico (0 : Int) 4 = {0, 1, 2, 3} from by decide]

/-- Output and cost may occur in the same nonlinear reward; they are perfectly
    correlated in this program and must not be treated as independent. -/
theorem output_work_product (heap : Heap) :
    charged_draw.expectedReturn heap () (fun after value =>
      (value.toNat : ℝ≥0∞) * (Heap.cost heap after "work" : ℝ≥0∞)) = 7 / 2 := by
  rw [expected_reward]
  norm_num [Int.toNat, show Finset.Ico (0 : Int) 4 = {0, 1, 2, 3} from by decide]
  apply (ENNReal.toReal_eq_toReal_iff'
    (by simp [ENNReal.mul_eq_top]) (by simp [ENNReal.div_eq_top])).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.mul_eq_top]

/-- The all-path runtime interface supports second-moment tail bounds without
    assuming that the call succeeds. A separate return law cannot discard
    work on failing or diverging paths when applying this statement. -/
theorem work_tail_bound (heap : Heap) (threshold : ℝ≥0∞)
    (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    charged_draw.costProbability heap () "work" threshold ≤
      expected (charged_draw.law heap ()) ((charged_draw.cost heap "work").pow 2) /
        threshold ^ 2 :=
  probability_exceeds_le_moment (charged_draw.law heap ())
    (charged_draw.cost heap "work") threshold 2 positive finite

/-- The exact second moment gives a numerical runtime-tail bound. -/
theorem work_tail_numerical (heap : Heap) (threshold : ℝ≥0∞)
    (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    charged_draw.costProbability heap () "work" threshold ≤ (7 / 2) / threshold ^ 2 := by
  simpa only [work_second_moment] using work_tail_bound heap threshold positive finite

end ChargedDrawAnalysis
