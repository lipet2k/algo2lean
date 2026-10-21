import Algo.hiring_contract.Analysis
import Algo2LeanProbability.CallObservations

/-!
Whole-execution runtime analysis of randomized hiring. The joint call law
already accounts for the imported shuffle and deterministic scan. Local clock
monotonicity connects its final-heap rewards to costs on complete execution
paths, without conditioning on successful return.
-/

noncomputable section
namespace HiringAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability
open Algo.hiring Algo.hiring.Algo2LeanGenerated
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem clock_step {before after : Configuration} (transition : Step before after)
    (clock : String) : before.heap.clocks clock ≤ after.heap.clocks clock := by
  have resumed (heap : Heap) (result : Result) (stack : Stack) :
      (resumeConfig heap result stack).heap = heap := by
    cases stack <;> rfl
  cases transition with
  | hire_assistant_pc1 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_hire_assistant locals.t5) stack).heap.clocks clock
      rw [resumed]
  | hire_assistant_pc17 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_hire_assistant locals.t9) stack).heap.clocks clock
      rw [resumed]
  | randomized_hire_assistant_pc1 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomized_hire_assistant locals.t2) stack).heap.clocks clock
      rw [resumed]
  | import_0 heap frame inner resume caller after imported =>
      change heap.clocks clock ≤ (ModuleCall.config Frame.import_0 resume caller after).heap.clocks clock
      rw [ModuleCall.heap]
      exact ShuffleAnalysis.clock_step imported clock
  | _ => simp [Config.heap, Heap.tick] <;> split_ifs <;> omega

private theorem outcome_halts (state : Configuration) (output : Heap × Int)
    (observed : randomized_hire_assistant.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | done heap result => rfl
  | active heap frame stack => simp [randomized_hire_assistant.outcome] at observed

private theorem outcome_cost (heap : Heap) (clock : String) (state : Configuration)
    (output : Heap × Int) (observed : randomized_hire_assistant.outcome state = some output) :
    Heap.cost heap state.heap clock = Heap.cost heap output.1 clock := by
  cases state with
  | done final result =>
      cases result <;> simp [randomized_hire_assistant.outcome] at observed
      subst output
      rfl
  | active heap frame stack => simp [randomized_hire_assistant.outcome] at observed

/-- Any nonnegative measurable reward of total charged work can be evaluated
using the reusable final-heap contract. Almost-sure termination comes from that
contract, and all imported operations preserve counter monotonicity. -/
theorem total_cost_reward (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (clock : String)
    (reward : ℝ≥0∞ → ℝ≥0∞) (measurable : Measurable reward) :
    expected (randomized_hire_assistant.law heap (ref, n))
      ((randomized_hire_assistant.cost heap clock).map reward measurable) =
      randomized_hire_assistant.expectedReturn heap (ref, n)
        (fun final _ => reward (Heap.cost heap final clock)) := by
  have finishes := Algo2LeanProbability.HasLaw.termination (randomized_hiring_law heap ref n valid)
  simp only [randomized_hire_assistant.ValidInput, valid, ↓reduceIte] at finishes
  have bridge := expected_total_eq_callExpected nextChoice randomized_hire_assistant.outcome
    outcome_halts (randomized_hire_assistant.initial heap (ref, n))
    (fun state => Heap.cost heap state.heap clock) (fun output => Heap.cost heap output.1 clock)
    (fun before after allowed => Nat.sub_le_sub_right (clock_step (choice_step.mp allowed) clock) _)
    (outcome_cost heap clock) finishes reward measurable
  simpa only [randomized_hire_assistant.law, randomized_hire_assistant.cost,
    randomized_hire_assistant.expectedReturn, randomized_hire_assistant.ValidInput,
    valid, ↓reduceIte] using bridge

/-- The interview, shuffle-draw, and swap counters each grow by n; every other
counter except hires is unchanged. This needs no distinctness assumption. -/
theorem expected_fixed_ticks (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (clock : String) (notHires : clock ≠ "hires") :
    randomized_hire_assistant.expectedReturn heap (ref, n)
      (fun final _ => (Heap.cost heap final clock : ℝ≥0∞)) =
      if clock = "interviews" ∨ clock = "random_draws" ∨ clock = "swaps" then (n : ℝ≥0∞) else 0 := by
  rw [randomized_expected_return heap ref n valid]
  unfold pmfExpected
  calc
    _ = ∑' final, ShuffleAnalysis.shuffleLaw heap ref 0 n final *
        (if clock = "interviews" ∨ clock = "random_draws" ∨ clock = "swaps"
          then (n : ℝ≥0∞) else 0) := by
      apply tsum_congr
      intro final
      by_cases possible : final ∈ (ShuffleAnalysis.shuffleLaw heap ref 0 n).support
      · simp [Heap.cost, account, ShuffleAnalysis.shuffleLaw_clocks n heap ref 0 final possible,
          Heap.tick, notHires]
        split_ifs <;> simp_all
      · have zero := (PMF.apply_eq_zero_iff _ _).2 possible
        simp [zero]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Whole-path costs for interviews, shuffle draws, and swaps each have mean n;
other clocks apart from hires have zero increment. -/
theorem expected_fixed_cost (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (clock : String) (notHires : clock ≠ "hires") :
    randomized_hire_assistant.expectedCost heap (ref, n) clock =
      if clock = "interviews" ∨ clock = "random_draws" ∨ clock = "swaps" then (n : ℝ≥0∞) else 0 := by
  have bridge := total_cost_reward heap ref n valid clock id measurable_id
  change randomized_hire_assistant.expectedCost heap (ref, n) clock = _ at bridge
  rw [bridge]
  exact expected_fixed_ticks heap ref n valid clock notHires

/-- The total interview count is exactly n in expectation, including all paths. -/
theorem expected_interview_cost (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomized_hire_assistant.expectedCost heap (ref, n) "interviews" = n := by
  simpa using expected_fixed_cost heap ref n valid "interviews" (by decide)

/-- For distinct candidate scores, the expected total hire count is H_n. The
expectation includes complete paths and uses the caller's initial counters. -/
theorem expected_hire_cost (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef)
    (distinct : Function.Injective (fun i : Fin n => heap.read ref i.val)) :
    randomized_hire_assistant.expectedCost heap (ref, n) "hires" = HiringRecords.harmonic n := by
  have bridge := total_cost_reward heap ref n valid "hires" id measurable_id
  change randomized_hire_assistant.expectedCost heap (ref, n) "hires" = _ at bridge
  rw [bridge]
  exact expected_hire_ticks heap ref n valid distinct

/-- Markov's inequality gives a whole-path tail bound for total hires. It does
not condition on success or discard costs of exceptional execution paths. -/
theorem hire_cost_tail (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef)
    (distinct : Function.Injective (fun i : Fin n => heap.read ref i.val))
    (threshold : ℝ≥0∞) (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    randomized_hire_assistant.costProbability heap (ref, n) "hires" threshold ≤
      HiringRecords.harmonic n / threshold := by
  have bound := probability_exceeds_le (randomized_hire_assistant.law heap (ref, n))
    (randomized_hire_assistant.cost heap "hires") threshold positive finite
  change randomized_hire_assistant.costProbability heap (ref, n) "hires" threshold ≤
    randomized_hire_assistant.expectedCost heap (ref, n) "hires" / threshold at bound
  simpa only [expected_hire_cost heap ref n valid distinct] using bound

end HiringAnalysis
