import Algo.quicksort_contract.Analysis
import Algo.quicksort_cost_model.Analysis
import Algo.quicksort_cost_bounds.Analysis
import Algo2LeanProbability.CallObservations
import Algo2LeanProbability.CallRewards

/-!
Randomized quicksort reuses randomized partition's joint law for its two recursive
calls. Correctness allows repeated keys; the harmonic expected comparison count
assumes distinct keys. Costs are measured over complete execution paths.
-/

noncomputable section
namespace QuicksortAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis
open Algo.quicksort Algo.quicksort.Algo2LeanGenerated
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Properties of every supported final heap hold with return probability one. -/
theorem returns_of_support (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (post : Heap → Prop)
    (holds : ∀ final ∈ (quicksortLaw (hi - lo).toNat heap ref lo hi).support, post final) :
    randomized_quicksort.returnProbability heap (ref, lo, hi) (fun final _ => post final) = 1 := by
  rw [randomized_quicksort.returnProbability_eq_expectedReturn heap (ref, lo, hi) valid]
  have guarantee := Algo2LeanProbability.HasLaw.probability_one (quicksort_law heap ref lo hi valid)
    (fun output => post output.1) (by
      intro output possible
      obtain ⟨final, supported, rfl⟩ := (PMF.mem_support_map_iff ..).1 possible
      exact holds final supported)
  simpa only [callProbability, randomized_quicksort.expectedReturn,
    randomized_quicksort.ValidInput, valid, ↓reduceIte] using guarantee

-- Main result: Correctness
/-- Quicksort terminates with a sorted permutation of the input interval and
preserves every unrelated object and sequence. Repeated keys are permitted. -/
theorem correctness (heap : Heap) (ref : SeqRef) (lo hi : Int) (valid : ref < heap.nextRef) :
    randomized_quicksort.returnProbability heap (ref, lo, hi)
      (fun final _ => Sorted final ref lo hi ∧ Rearranges heap final ref lo hi ∧
        final.nextRef = heap.nextRef ∧ heap.Footprint final [ref] [] []) = 1 := by
  apply returns_of_support heap ref lo hi valid
  intro final possible
  have ordered := quicksortLaw_correct (hi - lo).toNat heap ref lo hi le_rfl final possible
  exact ⟨ordered.1, ordered.2, quicksortLaw_frame (hi - lo).toNat heap ref lo hi final possible⟩

/-- The recursive law certifies almost-sure termination independently of distinctness. -/
theorem termination (heap : Heap) (ref : SeqRef) (lo hi : Int) (valid : ref < heap.nextRef) :
    randomized_quicksort.terminationProbability heap (ref, lo, hi) = 1 := by
  exact returns_of_support heap ref lo hi valid (fun _ => True) (by intros; trivial)

private theorem clock_step {before after : Configuration} (transition : Step before after)
    (clock : String) : before.heap.clocks clock ≤ after.heap.clocks clock := by
  have resumed (heap : Heap) (result : Result) (stack : Stack) :
      (resumeConfig heap result stack).heap = heap := by cases stack <;> rfl
  cases transition with
  | randomized_quicksort_pc1 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomized_quicksort locals.t4) stack).heap.clocks clock
      rw [resumed]
  | import_0 heap frame inner resume caller after imported =>
      change heap.clocks clock ≤ (ModuleCall.config Frame.import_0 resume caller after).heap.clocks clock
      rw [ModuleCall.heap]
      exact PartitionAnalysis.clock_step imported clock
  | _ => simp [Config.heap, Heap.tick] <;> split_ifs <;> omega

private theorem outcome_halts (state : Configuration) (output : Heap × Unit)
    (observed : randomized_quicksort.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | done heap result => rfl
  | active heap frame stack => simp [randomized_quicksort.outcome] at observed

private theorem outcome_cost (heap : Heap) (clock : String) (state : Configuration)
    (output : Heap × Unit) (observed : randomized_quicksort.outcome state = some output) :
    Heap.cost heap state.heap clock = Heap.cost heap output.1 clock := by
  cases state with
  | done final result =>
      cases result; simp [randomized_quicksort.outcome] at observed
      subst output
      rfl
  | active heap frame stack => simp [randomized_quicksort.outcome] at observed

/-- Nonnegative rewards of total path costs agree with final-heap expectations;
this includes all paths, without conditioning on a successful return. -/
theorem total_cost_reward (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (clock : String)
    (reward : ℝ≥0∞ → ℝ≥0∞) (measurable : Measurable reward) :
    expected (randomized_quicksort.law heap (ref, lo, hi))
      ((randomized_quicksort.cost heap clock).map reward measurable) =
      randomized_quicksort.expectedReturn heap (ref, lo, hi)
        (fun final _ => reward (Heap.cost heap final clock)) := by
  have finishes := Algo2LeanProbability.HasLaw.termination (quicksort_law heap ref lo hi valid)
  simp only [randomized_quicksort.ValidInput, valid, ↓reduceIte] at finishes
  have bridge := expected_total_eq_callExpected nextChoice randomized_quicksort.outcome
    outcome_halts (randomized_quicksort.initial heap (ref, lo, hi))
    (fun state => Heap.cost heap state.heap clock) (fun output => Heap.cost heap output.1 clock)
    (fun before after allowed => Nat.sub_le_sub_right (clock_step (choice_step.mp allowed) clock) _)
    (outcome_cost heap clock) finishes reward measurable
  simpa only [randomized_quicksort.law, randomized_quicksort.cost,
    randomized_quicksort.expectedReturn, randomized_quicksort.ValidInput,
    valid, ↓reduceIte] using bridge

/-- Every clock can be analyzed using the same joint heap law. -/
theorem expected_cost (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (clock : String) :
    randomized_quicksort.expectedCost heap (ref, lo, hi) clock =
      pmfExpected (quicksortLaw (hi - lo).toNat heap ref lo hi)
        (fun final => (Heap.cost heap final clock : ℝ≥0∞)) := by
  have bridge := total_cost_reward heap ref lo hi valid clock id measurable_id
  change randomized_quicksort.expectedCost heap (ref, lo, hi) clock = _ at bridge
  rw [bridge, expected_return (hi - lo).toNat heap ref lo hi valid le_rfl]
  rfl

-- Main result: Running time
/-- On n distinct keys, the expected comparison count is exactly 2(n+1)H_n−4n.
The equality concerns unconditional total path cost, including the imported
partition calls and both recursive sorts. -/
theorem running_time (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_quicksort.expectedCost heap (ref, lo, hi) "comparisons" =
      ENNReal.ofReal (2 * ((hi - lo).toNat + 1 : ℝ) * harmonic (hi - lo).toNat -
        4 * (hi - lo).toNat) := by
  have bridge := total_cost_reward heap ref lo hi valid "comparisons" id measurable_id
  change randomized_quicksort.expectedCost heap (ref, lo, hi) "comparisons" = _ at bridge
  rw [bridge, expected_return (hi - lo).toNat heap ref lo hi valid le_rfl]
  have exactMean := quicksortLaw_comparison_mean (hi - lo).toNat heap ref lo hi le_rfl distinct
    (heap.clocks "comparisons") le_rfl
  simp only [Nat.sub_self, Nat.cast_zero, zero_add] at exactMean
  simpa [Heap.cost, comparisonMean, comparisons] using exactMean

/-- The exact harmonic count implies the customary expected O(n log n) bound. -/
theorem running_time_log_bound (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_quicksort.expectedCost heap (ref, lo, hi) "comparisons" ≤
      ENNReal.ofReal (2 * ((hi - lo).toNat + 1 : ℝ) * (1 + Real.log (hi - lo).toNat)) := by
  rw [running_time heap ref lo hi valid distinct]
  apply ENNReal.ofReal_le_ofReal
  simpa [comparisons] using comparisons_le_log (hi - lo).toNat

/-- Counting comparisons, swaps, random draws, and recursive invocations together
still gives expected O(n log n) work: at most 2C_n + 5n + 1, where
C_n = 2(n+1)H_n−4n. Each source operation has unit weight in this bound. -/
theorem expected_work (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_quicksort.expectedCost heap (ref, lo, hi) "comparisons" +
      randomized_quicksort.expectedCost heap (ref, lo, hi) "swaps" +
      randomized_quicksort.expectedCost heap (ref, lo, hi) "random_draws" +
      randomized_quicksort.expectedCost heap (ref, lo, hi) "quicksort_calls" ≤
      2 * comparisonMean (hi - lo).toNat + 5 * ((hi - lo).toNat : ℝ≥0∞) + 1 := by
  rw [expected_cost heap ref lo hi valid "comparisons", expected_cost heap ref lo hi valid "swaps",
    expected_cost heap ref lo hi valid "random_draws", expected_cost heap ref lo hi valid "quicksort_calls",
    ← pmfExpected_add, ← pmfExpected_add, ← pmfExpected_add]
  let law := quicksortLaw (hi - lo).toNat heap ref lo hi
  calc
    _ ≤ pmfExpected law (fun final => 2 * (Heap.cost heap final "comparisons" : ℝ≥0∞) +
        5 * ((hi - lo).toNat : ℝ≥0∞) + 1) := by
      apply pmfExpected_mono_support
      intro final possible
      have bounds := quicksortLaw_cost_bounds (hi - lo).toNat heap ref lo hi final possible
      have arithmetic : Heap.cost heap final "comparisons" + Heap.cost heap final "swaps" +
          Heap.cost heap final "random_draws" + Heap.cost heap final "quicksort_calls" ≤
          2 * Heap.cost heap final "comparisons" + 5 * (hi - lo).toNat + 1 := by omega
      exact_mod_cast arithmetic
    _ = _ := by
      rw [pmfExpected_add, pmfExpected_add, pmfExpected_const, pmfExpected_const, pmfExpected_mul]
      have mean := quicksortLaw_comparison_mean (hi - lo).toNat heap ref lo hi le_rfl distinct
        (heap.clocks "comparisons") le_rfl
      simpa only [Heap.cost, Nat.sub_self, Nat.cast_zero, zero_add] using
        congrArg (fun value : ℝ≥0∞ => 2 * value + 5 * ((hi - lo).toNat : ℝ≥0∞) + 1) mean

end QuicksortAnalysis
