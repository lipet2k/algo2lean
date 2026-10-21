import Algo.quicksort_model.Analysis

/-!
All quicksort operation counters are controlled by input length and comparisons.
These pathwise bounds need no distinct-key assumption: at most one pivot is
removed per recursive split, and partition uses at most two extra swaps beyond
its comparison count. The joint heap law preserves every clock monotonically.
-/

noncomputable section
namespace QuicksortAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis

/-- Every supported quicksort outcome preserves monotonicity of every clock. -/
private theorem quicksortLaw_clock_mono (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (final : Heap) (possible : final ∈ (quicksortLaw fuel heap ref lo hi).support)
    (clock : String) : heap.clocks clock ≤ final.clocks clock := by
  induction fuel generalizing heap lo hi final with
  | zero =>
      have same : final = heap.tick "quicksort_calls" := by simpa [quicksortLaw] using possible
      subst final
      simp [Heap.tick]
      split_ifs <;> omega
  | succ fuel ih =>
      simp only [quicksortLaw] at possible
      split_ifs at possible with large
      · obtain ⟨partitioned, selected, rest⟩ := (PMF.mem_support_bind_iff ..).1 possible
        obtain ⟨left, leftPossible, rightPossible⟩ := (PMF.mem_support_bind_iff ..).1 rest
        have charged : heap.clocks clock ≤ (heap.tick "quicksort_calls").clocks clock := by
          simp [Heap.tick]; split_ifs <;> omega
        exact charged.trans ((randomizedPartitionLaw_clock_mono _ ref lo hi (by omega)
          partitioned selected clock).trans ((ih partitioned.1 lo partitioned.2 left leftPossible).trans
            (ih left (partitioned.2 + 1) hi final rightPossible)))
      · have same : final = heap.tick "quicksort_calls" := by simpa using possible
        subst final
        simp [Heap.tick]
        split_ifs <;> omega

/-- Raw clock bounds telescope across the partition and both recursive calls. -/
theorem quicksortLaw_raw_clock_bounds (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (final : Heap) (possible : final ∈ (quicksortLaw fuel heap ref lo hi).support) :
    final.clocks "quicksort_calls" ≤ heap.clocks "quicksort_calls" + 2 * (hi - lo).toNat + 1 ∧
    final.clocks "random_draws" ≤ heap.clocks "random_draws" + (hi - lo).toNat ∧
    final.clocks "swaps" + heap.clocks "comparisons" + 2 * heap.clocks "random_draws" ≤
      heap.clocks "swaps" + final.clocks "comparisons" + 2 * final.clocks "random_draws" := by
  induction fuel generalizing heap lo hi final with
  | zero =>
      have same : final = heap.tick "quicksort_calls" := by simpa [quicksortLaw] using possible
      subst final
      simp [Heap.tick]
  | succ fuel ih =>
      simp only [quicksortLaw] at possible
      split_ifs at possible with large
      · obtain ⟨partitioned, selected, rest⟩ := (PMF.mem_support_bind_iff ..).1 possible
        obtain ⟨left, leftPossible, rightPossible⟩ := (PMF.mem_support_bind_iff ..).1 rest
        have split := (randomizedPartitionLaw_correct (heap.tick "quicksort_calls") ref lo hi
          (by omega) partitioned selected).1
        have lower := split.1
        have upper := split.2.1
        have partitionCosts := randomizedPartitionLaw_cost (heap.tick "quicksort_calls") ref lo hi
          (by omega) partitioned selected
        have partitionCalls := randomizedPartitionLaw_other_clock (heap.tick "quicksort_calls") ref lo hi
          (by omega) partitioned selected "quicksort_calls" (by decide) (by decide) (by decide)
        have partitionComparisons := randomizedPartitionLaw_clock_mono (heap.tick "quicksort_calls")
          ref lo hi (by omega) partitioned selected "comparisons"
        have partitionDraws := randomizedPartitionLaw_clock_mono (heap.tick "quicksort_calls")
          ref lo hi (by omega) partitioned selected "random_draws"
        have partitionSwaps := randomizedPartitionLaw_clock_mono (heap.tick "quicksort_calls")
          ref lo hi (by omega) partitioned selected "swaps"
        simp only [Heap.cost, Heap.tick, String.reduceEq, ↓reduceIte] at partitionCosts partitionCalls partitionComparisons partitionDraws partitionSwaps
        obtain ⟨leftCalls, leftDraws, leftSwaps⟩ := ih partitioned.1 lo partitioned.2 left leftPossible
        obtain ⟨rightCalls, rightDraws, rightSwaps⟩ := ih left (partitioned.2 + 1) hi final rightPossible
        constructor
        · omega
        constructor
        · omega
        · omega
      · have same : final = heap.tick "quicksort_calls" := by simpa using possible
        subst final
        simp [Heap.tick]

/-- Every completed quicksort law outcome uses at most 2n+1 calls and n random
draws. Its swaps are at most its comparisons plus twice its number of draws. -/
theorem quicksortLaw_cost_bounds (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (final : Heap) (possible : final ∈ (quicksortLaw fuel heap ref lo hi).support) :
    Heap.cost heap final "quicksort_calls" ≤ 2 * (hi - lo).toNat + 1 ∧
    Heap.cost heap final "random_draws" ≤ (hi - lo).toNat ∧
    Heap.cost heap final "swaps" ≤ Heap.cost heap final "comparisons" +
      2 * Heap.cost heap final "random_draws" := by
  have bounds := quicksortLaw_raw_clock_bounds fuel heap ref lo hi final possible
  have comparisons := quicksortLaw_clock_mono fuel heap ref lo hi final possible "comparisons"
  have draws := quicksortLaw_clock_mono fuel heap ref lo hi final possible "random_draws"
  have swaps := quicksortLaw_clock_mono fuel heap ref lo hi final possible "swaps"
  simp only [Heap.cost]
  omega

end QuicksortAnalysis
