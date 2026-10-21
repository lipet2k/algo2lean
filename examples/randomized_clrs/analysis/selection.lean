import Algo.selection_contract.Analysis
import Algo.selection_correctness.Analysis
import Algo.selection_costs.Analysis

/-!
RANDOMIZED-SELECT reuses the imported randomized partition contract. For a
nonempty interval of distinct keys and a valid zero-based rank, it returns the
requested order statistic almost surely. The sequence remains a rearrangement
of its original interval, and cells outside that interval retain their values.
The running-time theorem bounds the combined expected comparisons, swaps,
random draws, and selection calls by twelve times the interval length.
-/

noncomputable section
namespace SelectionAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis Algo.selection
open scoped ENNReal

-- Main result: Correctness
/-- Selection returns the requested zero-based order statistic with probability
one and only permutes the selected input interval. -/
theorem correctness (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_select.returnProbability heap (ref, lo, hi, requested)
      (fun final value => IsOrderStatistic heap ref lo hi requested value ∧
        Rearranges heap final ref lo hi) = 1 := by
  rw [randomized_select.returnProbability_eq_expectedReturn heap (ref, lo, hi, requested) valid]
  have guarantee := Algo2LeanProbability.HasLaw.probability_one
    (selection_law heap ref lo hi requested valid nonempty requestedValid)
    (fun result => IsOrderStatistic heap ref lo hi requested result.2 ∧
      Rearranges heap result.1 ref lo hi)
    (fun result possible => selectionLaw_correct (hi - lo).toNat heap ref lo hi requested nonempty
      requestedValid.1 requestedValid.2 le_rfl distinct result possible)
  simpa only [callProbability, randomized_select.expectedReturn,
    randomized_select.ValidInput, valid, ↓reduceIte] using guarantee

-- Main result: Running time
/-- Charging one unit per comparison, swap, random draw, and selection call
costs at most 12n in expectation for distinct input keys. These total path
costs include every imported partition and recursive selection call. -/
theorem running_time (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_select.expectedCost heap (ref, lo, hi, requested) "comparisons" +
      randomized_select.expectedCost heap (ref, lo, hi, requested) "swaps" +
      randomized_select.expectedCost heap (ref, lo, hi, requested) "random_draws" +
      randomized_select.expectedCost heap (ref, lo, hi, requested) "selection_calls" ≤
      12 * ((hi - lo).toNat : ℝ≥0∞) :=
  expected_work heap ref lo hi requested valid nonempty requestedValid distinct

end SelectionAnalysis
