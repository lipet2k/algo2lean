import Algo.selection_contract.Analysis
import Algo.selection_cost_bounds.Analysis
import Algo2LeanProbability.CallObservations
import Algo2LeanProbability.CallRewards

/-!
Total-path costs of randomized selection. The joint return law already includes
all imported partition calls and recursive selection calls. Monotone clocks
and almost-sure successful return identify a complete path's cost with the
final counter increment, permitting arbitrary measurable runtime rewards.
-/

noncomputable section
namespace SelectionAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability
open Algo.selection Algo.selection.Algo2LeanGenerated
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
  | randomized_select_pc1 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomized_select locals.t6) stack).heap.clocks clock
      rw [resumed]
  | randomized_select_pc7 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomized_select locals.t12) stack).heap.clocks clock
      rw [resumed]
  | randomized_select_pc15 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomized_select locals.t18) stack).heap.clocks clock
      rw [resumed]
  | randomized_select_pc25 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomized_select locals.t24) stack).heap.clocks clock
      rw [resumed]
  | import_0 heap frame inner resume caller after imported =>
      change heap.clocks clock ≤ (ModuleCall.config Frame.import_0 resume caller after).heap.clocks clock
      rw [ModuleCall.heap]
      exact PartitionAnalysis.clock_step imported clock
  | _ => simp [Config.heap, Heap.tick] <;> split_ifs <;> omega

private theorem outcome_halts (state : Configuration) (output : Heap × Int)
    (observed : randomized_select.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | done heap result => rfl
  | active heap frame stack => simp [randomized_select.outcome] at observed

private theorem outcome_cost (heap : Heap) (clock : String) (state : Configuration)
    (output : Heap × Int) (observed : randomized_select.outcome state = some output) :
    Heap.cost heap state.heap clock = Heap.cost heap output.1 clock := by
  cases state with
  | done final result =>
      cases result
      simp only [randomized_select.outcome, Option.some.injEq] at observed
      subst output
      rfl
  | active heap frame stack => simp [randomized_select.outcome] at observed

/-- Every measurable nonnegative function of total cost can be evaluated with
the reusable completed-call contract. This includes moments and tail indicators. -/
theorem total_cost_reward (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo) (clock : String)
    (reward : ℝ≥0∞ → ℝ≥0∞) (measurable : Measurable reward) :
    expected (randomized_select.law heap (ref, lo, hi, requested))
      ((randomized_select.cost heap clock).map reward measurable) =
      randomized_select.expectedReturn heap (ref, lo, hi, requested)
        (fun final _ => reward (Heap.cost heap final clock)) := by
  have finishes := Algo2LeanProbability.HasLaw.termination
    (selection_law heap ref lo hi requested valid nonempty requestedValid)
  simp only [randomized_select.ValidInput, valid, ↓reduceIte] at finishes
  have bridge := expected_total_eq_callExpected nextChoice randomized_select.outcome
    outcome_halts (randomized_select.initial heap (ref, lo, hi, requested))
    (fun state => Heap.cost heap state.heap clock) (fun output => Heap.cost heap output.1 clock)
    (fun before after allowed => Nat.sub_le_sub_right (clock_step (choice_step.mp allowed) clock) _)
    (outcome_cost heap clock) finishes reward measurable
  simpa only [randomized_select.law, randomized_select.cost, randomized_select.expectedReturn,
    randomized_select.ValidInput, valid, ↓reduceIte] using bridge

/-- Distinct-key selection uses at most 4n comparisons in expectation on the
full execution law, including every imported and recursive call. -/
theorem expected_comparison_cost (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_select.expectedCost heap (ref, lo, hi, requested) "comparisons" ≤
      4 * ((hi - lo).toNat : ℝ≥0∞) := by
  have bridge := total_cost_reward heap ref lo hi requested valid nonempty requestedValid
    "comparisons" id measurable_id
  change randomized_select.expectedCost heap (ref, lo, hi, requested) "comparisons" = _ at bridge
  rw [bridge]
  exact expected_comparisons heap ref lo hi requested valid nonempty requestedValid distinct

/-- Markov's inequality bounds the chance that the complete selection uses
more comparisons than a chosen positive finite threshold. -/
theorem comparison_cost_tail (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi))
    (threshold : ℝ≥0∞) (positive : threshold ≠ 0) (finite : threshold ≠ ∞) :
    randomized_select.costProbability heap (ref, lo, hi, requested) "comparisons" threshold ≤
      4 * ((hi - lo).toNat : ℝ≥0∞) / threshold := by
  have bound := probability_exceeds_le (randomized_select.law heap (ref, lo, hi, requested))
    (randomized_select.cost heap "comparisons") threshold positive finite
  change randomized_select.costProbability heap (ref, lo, hi, requested) "comparisons" threshold ≤
    randomized_select.expectedCost heap (ref, lo, hi, requested) "comparisons" / threshold at bound
  refine bound.trans ?_
  exact ENNReal.div_le_div_right
    (expected_comparison_cost heap ref lo hi requested valid nonempty requestedValid distinct) _

/-- Total expected clock growth is the corresponding reward of the reusable
joint selection law. This equation includes all imported and recursive work. -/
theorem expected_cost (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo) (clock : String) :
    randomized_select.expectedCost heap (ref, lo, hi, requested) clock =
      pmfExpected (selectionLaw (hi - lo).toNat heap ref lo hi requested)
        (fun result => (Heap.cost heap result.1 clock : ℝ≥0∞)) := by
  have bridge := total_cost_reward heap ref lo hi requested valid nonempty requestedValid
    clock id measurable_id
  change randomized_select.expectedCost heap (ref, lo, hi, requested) clock = _ at bridge
  rw [bridge, expected_return (hi - lo).toNat heap ref lo hi requested valid nonempty requestedValid le_rfl]
  rfl

/-- All auxiliary operation counts are controlled by interval length and
comparisons, even when the input contains repeated keys. -/
theorem expected_operation_costs (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo) :
    randomized_select.expectedCost heap (ref, lo, hi, requested) "selection_calls" ≤
        ((hi - lo).toNat : ℝ≥0∞) ∧
    randomized_select.expectedCost heap (ref, lo, hi, requested) "random_draws" ≤
        ((hi - lo).toNat : ℝ≥0∞) ∧
    randomized_select.expectedCost heap (ref, lo, hi, requested) "swaps" ≤
      randomized_select.expectedCost heap (ref, lo, hi, requested) "comparisons" +
        2 * randomized_select.expectedCost heap (ref, lo, hi, requested) "random_draws" := by
  rw [expected_cost heap ref lo hi requested valid nonempty requestedValid "selection_calls",
    expected_cost heap ref lo hi requested valid nonempty requestedValid "random_draws",
    expected_cost heap ref lo hi requested valid nonempty requestedValid "swaps",
    expected_cost heap ref lo hi requested valid nonempty requestedValid "comparisons"]
  let law := selectionLaw (hi - lo).toNat heap ref lo hi requested
  constructor
  · calc
      _ ≤ pmfExpected law (fun _ => ((hi - lo).toNat : ℝ≥0∞)) := by
        apply pmfExpected_mono_support
        intro result possible
        exact_mod_cast (selectionLaw_cost_bounds (hi - lo).toNat heap ref lo hi requested
          nonempty requestedValid result possible).1
      _ = _ := pmfExpected_const _ _
  constructor
  · calc
      _ ≤ pmfExpected law (fun _ => ((hi - lo).toNat : ℝ≥0∞)) := by
        apply pmfExpected_mono_support
        intro result possible
        exact_mod_cast (selectionLaw_cost_bounds (hi - lo).toNat heap ref lo hi requested
          nonempty requestedValid result possible).2.1
      _ = _ := pmfExpected_const _ _
  · calc
      _ ≤ pmfExpected law (fun result => (Heap.cost heap result.1 "comparisons" : ℝ≥0∞) +
            2 * (Heap.cost heap result.1 "random_draws" : ℝ≥0∞)) := by
        apply pmfExpected_mono_support
        intro result possible
        exact_mod_cast (selectionLaw_cost_bounds (hi - lo).toNat heap ref lo hi requested
          nonempty requestedValid result possible).2.2
      _ = _ := by rw [pmfExpected_add, pmfExpected_mul]

/-- Assign any nonnegative prices to comparisons, swaps, random draws, and
recursive calls. Their combined expected cost grows linearly with input length. -/
theorem expected_weighted_work (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi))
    (comparisonPrice swapPrice drawPrice callPrice : ℝ≥0∞) :
    comparisonPrice * randomized_select.expectedCost heap (ref, lo, hi, requested) "comparisons" +
      swapPrice * randomized_select.expectedCost heap (ref, lo, hi, requested) "swaps" +
      drawPrice * randomized_select.expectedCost heap (ref, lo, hi, requested) "random_draws" +
      callPrice * randomized_select.expectedCost heap (ref, lo, hi, requested) "selection_calls" ≤
      (4 * comparisonPrice + 6 * swapPrice + drawPrice + callPrice) *
        ((hi - lo).toNat : ℝ≥0∞) := by
  have comparisons := expected_comparison_cost heap ref lo hi requested valid nonempty requestedValid distinct
  obtain ⟨calls, draws, swaps⟩ := expected_operation_costs heap ref lo hi requested valid nonempty requestedValid
  have swapBound : randomized_select.expectedCost heap (ref, lo, hi, requested) "swaps" ≤
      6 * ((hi - lo).toNat : ℝ≥0∞) := by
    calc
      _ ≤ _ := swaps
      _ ≤ 4 * ((hi - lo).toNat : ℝ≥0∞) + 2 * ((hi - lo).toNat : ℝ≥0∞) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ comparisonPrice * (4 * ((hi - lo).toNat : ℝ≥0∞)) +
        swapPrice * (6 * ((hi - lo).toNat : ℝ≥0∞)) +
        drawPrice * ((hi - lo).toNat : ℝ≥0∞) + callPrice * ((hi - lo).toNat : ℝ≥0∞) := by gcongr
    _ = _ := by ring

/-- Charging one unit for every comparison, swap, draw, and selection call gives
at most 12n expected units of work over the entire execution. -/
theorem expected_work (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_select.expectedCost heap (ref, lo, hi, requested) "comparisons" +
      randomized_select.expectedCost heap (ref, lo, hi, requested) "swaps" +
      randomized_select.expectedCost heap (ref, lo, hi, requested) "random_draws" +
      randomized_select.expectedCost heap (ref, lo, hi, requested) "selection_calls" ≤
      12 * ((hi - lo).toNat : ℝ≥0∞) := by
  have bound := expected_weighted_work heap ref lo hi requested valid nonempty requestedValid distinct 1 1 1 1
  norm_num at bound
  exact bound

end SelectionAnalysis
