import Algo.selection_model.Analysis

/-!
Pathwise bounds for every charged selection operation. A recursive call keeps
one partition piece and discards its pivot, so the numbers of calls and random
draws are linear in interval length. Swaps are controlled by comparisons and
draws. These inequalities require a valid rank but permit repeated input keys.
-/

noncomputable section
namespace SelectionAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis

/-- Every supported selection outcome preserves monotonicity of every clock. -/
theorem selectionLaw_clock_mono (fuel : Nat) (heap : Heap) (ref : SeqRef)
    (lo hi requested : Int) (result : Heap × Int)
    (possible : result ∈ (selectionLaw fuel heap ref lo hi requested).support)
    (clock : String) : heap.clocks clock ≤ result.1.clocks clock := by
  induction fuel generalizing heap lo hi requested result with
  | zero =>
      have same : result = (heap, 0) := by simpa [selectionLaw] using possible
      subst result
      exact le_rfl
  | succ fuel ih =>
      have charged : heap.clocks clock ≤ (heap.tick "selection_calls").clocks clock := by
        simp [Heap.tick]; split_ifs <;> omega
      simp only [selectionLaw] at possible
      split_ifs at possible with singleton nonempty
      · have same : result = (heap.tick "selection_calls", heap.read ref lo) := by simpa using possible
        subst result
        exact charged
      · obtain ⟨partitioned, selected, later⟩ := (PMF.mem_support_bind_iff ..).1 possible
        have part := charged.trans (randomizedPartitionLaw_clock_mono _ ref lo hi nonempty
          partitioned selected clock)
        split_ifs at later with found before
        · have same : result = (partitioned.1, partitioned.1.read ref partitioned.2) := by simpa using later
          subst result
          exact part
        · exact part.trans (ih partitioned.1 lo partitioned.2 requested result later)
        · exact part.trans (ih partitioned.1 (partitioned.2 + 1) hi
            (requested - (partitioned.2 - lo) - 1) result later)
      · have same : result = (heap.tick "selection_calls", 0) := by simpa using possible
        subst result
        exact charged

/-- Raw clock bounds telescope across each imported partition and recursive call. -/
theorem selectionLaw_raw_clock_bounds (fuel : Nat) (heap : Heap) (ref : SeqRef)
    (lo hi requested : Int) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo) (result : Heap × Int)
    (possible : result ∈ (selectionLaw fuel heap ref lo hi requested).support) :
    result.1.clocks "selection_calls" ≤ heap.clocks "selection_calls" + (hi - lo).toNat ∧
    result.1.clocks "random_draws" ≤ heap.clocks "random_draws" + (hi - lo).toNat ∧
    result.1.clocks "swaps" + heap.clocks "comparisons" + 2 * heap.clocks "random_draws" ≤
      heap.clocks "swaps" + result.1.clocks "comparisons" + 2 * result.1.clocks "random_draws" := by
  induction fuel generalizing heap lo hi requested result with
  | zero =>
      have same : result = (heap, 0) := by simpa [selectionLaw] using possible
      subst result
      simp
  | succ fuel ih =>
      simp only [selectionLaw] at possible
      by_cases singleton : hi - lo = 1
      · rw [if_pos singleton] at possible
        have same : result = (heap.tick "selection_calls", heap.read ref lo) := by simpa using possible
        subst result
        simp [Heap.tick, singleton]
      · rw [if_neg singleton, dif_pos nonempty] at possible
        obtain ⟨partitioned, selected, later⟩ := (PMF.mem_support_bind_iff ..).1 possible
        have split := (randomizedPartitionLaw_correct (heap.tick "selection_calls") ref lo hi
          nonempty partitioned selected).1
        have lower := split.1
        have upper := split.2.1
        have partitionCosts := randomizedPartitionLaw_cost (heap.tick "selection_calls") ref lo hi
          nonempty partitioned selected
        have partitionCalls := randomizedPartitionLaw_other_clock (heap.tick "selection_calls") ref lo hi
          nonempty partitioned selected "selection_calls" (by decide) (by decide) (by decide)
        have partitionComparisons := randomizedPartitionLaw_clock_mono (heap.tick "selection_calls")
          ref lo hi nonempty partitioned selected "comparisons"
        have partitionDraws := randomizedPartitionLaw_clock_mono (heap.tick "selection_calls")
          ref lo hi nonempty partitioned selected "random_draws"
        have partitionSwaps := randomizedPartitionLaw_clock_mono (heap.tick "selection_calls")
          ref lo hi nonempty partitioned selected "swaps"
        simp only [Heap.cost, Heap.tick, String.reduceEq, ↓reduceIte] at partitionCosts partitionCalls partitionComparisons partitionDraws partitionSwaps
        split_ifs at later with found before
        · have same : result = (partitioned.1, partitioned.1.read ref partitioned.2) := by simpa using later
          subst result
          simp only
          omega
        · have validLeft : 0 ≤ requested ∧ requested < partitioned.2 - lo := by omega
          have resultBounds := ih partitioned.1 lo partitioned.2 requested (by omega) validLeft result later
          omega
        · have validRight : 0 ≤ requested - (partitioned.2 - lo) - 1 ∧
              requested - (partitioned.2 - lo) - 1 < hi - (partitioned.2 + 1) := by omega
          have resultBounds := ih partitioned.1 (partitioned.2 + 1) hi
            (requested - (partitioned.2 - lo) - 1) (by omega) validRight result later
          omega

/-- Every selection outcome uses at most n calls and n random draws. Swaps are
at most its comparisons plus twice its draws, measured from the input counters. -/
theorem selectionLaw_cost_bounds (fuel : Nat) (heap : Heap) (ref : SeqRef)
    (lo hi requested : Int) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo) (result : Heap × Int)
    (possible : result ∈ (selectionLaw fuel heap ref lo hi requested).support) :
    Heap.cost heap result.1 "selection_calls" ≤ (hi - lo).toNat ∧
    Heap.cost heap result.1 "random_draws" ≤ (hi - lo).toNat ∧
    Heap.cost heap result.1 "swaps" ≤ Heap.cost heap result.1 "comparisons" +
      2 * Heap.cost heap result.1 "random_draws" := by
  have bounds := selectionLaw_raw_clock_bounds fuel heap ref lo hi requested nonempty requestedValid result possible
  have comparisons := selectionLaw_clock_mono fuel heap ref lo hi requested result possible "comparisons"
  have draws := selectionLaw_clock_mono fuel heap ref lo hi requested result possible "random_draws"
  have swaps := selectionLaw_clock_mono fuel heap ref lo hi requested result possible "swaps"
  simp only [Heap.cost]
  omega

end SelectionAnalysis
