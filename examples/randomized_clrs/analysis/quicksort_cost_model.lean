import Algo.quicksort_model.Analysis
import Algo.quicksort_recurrence.Analysis
import Algo2LeanProbability.CallRewards

/-!
The comparison expectation follows by composing the two recursive calls with
partition's joint law. No independence of the mutated heaps is assumed: every
recursive bound holds for the heap actually returned by its preceding call.
-/

noncomputable section
namespace QuicksortAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis
open scoped ENNReal BigOperators

private theorem sum_offsets {α : Type*} [AddCommMonoid α] (lo hi : Int) (nonempty : lo < hi)
    (value : Nat → α) :
    (∑ position ∈ Finset.Ico lo hi, value (position - lo).toNat) =
      ∑ offset ∈ Finset.range (hi - lo).toNat, value offset := by
  apply Finset.sum_bij (fun position _ => (position - lo).toNat)
  · intro position member
    obtain ⟨lower, upper⟩ := Finset.mem_Ico.mp member
    apply Finset.mem_range.mpr
    omega
  · intro first hf second hs same
    obtain ⟨lf, uf⟩ := Finset.mem_Ico.mp hf
    obtain ⟨ls, us⟩ := Finset.mem_Ico.mp hs
    omega
  · intro offset member
    have bound := Finset.mem_range.mp member
    refine ⟨lo + offset, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intros; rfl

/-- The two subproblem sizes average to the harmonic comparison recurrence. -/
theorem uniform_comparison_recurrence (lo hi : Int) (nonempty : lo < hi) :
    ((hi - lo - 1).toNat : ℝ≥0∞) + pmfExpected (uniformInt lo hi nonempty)
      (fun pivot => comparisonMean (pivot - lo).toNat + comparisonMean (hi - (pivot + 1)).toNat) =
        comparisonMean (hi - lo).toNat := by
  rw [pmfExpected_uniformInt, ← Finset.sum_mul]
  have shifted : (∑ pivot ∈ Finset.Ico lo hi,
      (comparisonMean (pivot - lo).toNat + comparisonMean (hi - (pivot + 1)).toNat)) =
      ∑ pivot ∈ Finset.range (hi - lo).toNat,
        (comparisonMean pivot + comparisonMean ((hi - lo).toNat - 1 - pivot)) := by
    calc
      _ = ∑ pivot ∈ Finset.Ico lo hi,
          (comparisonMean (pivot - lo).toNat + comparisonMean ((hi - lo).toNat - 1 - (pivot - lo).toNat)) := by
        apply Finset.sum_congr rfl
        intro pivot member
        obtain ⟨lower, upper⟩ := Finset.mem_Ico.mp member
        have length : (hi - (pivot + 1)).toNat = (hi - lo).toNat - 1 - (pivot - lo).toNat := by omega
        rw [length]
      _ = _ := sum_offsets lo hi nonempty
        (fun pivot => comparisonMean pivot + comparisonMean ((hi - lo).toNat - 1 - pivot))
  rw [shifted]
  have base : (hi - lo - 1).toNat = (hi - lo).toNat - 1 := by omega
  rw [base]
  exact (comparisonMean_recurrence (hi - lo).toNat (by omega)).symm

/-- Every supported recursive result has clocks at least as large as its input. -/
theorem quicksortLaw_clock_mono (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (final : Heap) (possible : final ∈ (quicksortLaw fuel heap ref lo hi).support) (clock : String) :
    heap.clocks clock ≤ final.clocks clock := by
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
      have before : heap.clocks clock ≤ (heap.tick "quicksort_calls").clocks clock := by
        simp [Heap.tick]; split_ifs <;> omega
      exact before.trans ((randomizedPartitionLaw_clock_mono _ ref lo hi (by omega)
        partitioned selected clock).trans ((ih partitioned.1 lo partitioned.2 left leftPossible).trans
          (ih left (partitioned.2 + 1) hi final rightPossible)))
    · have same : final = heap.tick "quicksort_calls" := by simpa using possible
      subst final
      simp [Heap.tick]
      split_ifs <;> omega

/-- Exact comparisons compose from any earlier clock baseline, so correlated
heap effects from the two recursive calls remain available to later proofs. -/
theorem quicksortLaw_comparison_mean (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (enough : (hi - lo).toNat ≤ fuel)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi))
    (baseline : Nat) (baselineLe : baseline ≤ heap.clocks "comparisons") :
    pmfExpected (quicksortLaw fuel heap ref lo hi)
      (fun final => ((final.clocks "comparisons" - baseline : Nat) : ℝ≥0∞)) =
      ((heap.clocks "comparisons" - baseline : Nat) : ℝ≥0∞) + comparisonMean (hi - lo).toNat := by
  induction fuel generalizing heap lo hi with
  | zero =>
    have empty : (hi - lo).toNat = 0 := by omega
    simp [quicksortLaw, pmfExpected_pure, Heap.tick, empty]
  | succ fuel ih =>
    by_cases large : 1 < hi - lo
    · rw [quicksortLaw, dif_pos large, pmfExpected_bind]
      let charged := heap.tick "quicksort_calls"
      have nonempty : lo < hi := by omega
      let fixed : ℝ≥0∞ := ((heap.clocks "comparisons" - baseline : Nat) : ℝ≥0∞) +
        ((hi - lo - 1).toNat : ℝ≥0∞)
      have branch : ∀ result ∈ (randomizedPartitionLaw charged ref lo hi nonempty).support,
          pmfExpected ((quicksortLaw fuel result.1 ref lo result.2).bind
              (fun left => quicksortLaw fuel left ref (result.2 + 1) hi))
            (fun final => ((final.clocks "comparisons" - baseline : Nat) : ℝ≥0∞)) =
          fixed + (comparisonMean (result.2 - lo).toNat + comparisonMean (hi - (result.2 + 1)).toNat) := by
        intro result possible
        have facts := randomizedPartitionLaw_correct charged ref lo hi nonempty result possible
        have pivotLow := facts.1.1
        have pivotHigh := facts.1.2.1
        have partitionDistinct := rearranges_distinct facts.2.1 distinct
        have leftEnough : (result.2 - lo).toNat ≤ fuel := by omega
        have rightEnough : (hi - (result.2 + 1)).toNat ≤ fuel := by omega
        have leftDistinct : Set.InjOn (result.1.read ref) (Set.Ico lo result.2) :=
          partitionDistinct.mono (by intro x hx; exact ⟨hx.1, lt_trans hx.2 pivotHigh⟩)
        have raw := randomizedPartitionLaw_comparison_clock charged ref lo hi nonempty result possible
        have raw' : result.1.clocks "comparisons" = heap.clocks "comparisons" +
            (hi - lo - 1).toNat := by simpa [charged, Heap.tick] using raw
        have basePartition : baseline ≤ result.1.clocks "comparisons" := by omega
        have fixedClock : ((result.1.clocks "comparisons" - baseline : Nat) : ℝ≥0∞) = fixed := by
          have arithmetic : result.1.clocks "comparisons" - baseline =
              (heap.clocks "comparisons" - baseline) + (hi - lo - 1).toNat := by omega
          simp only [arithmetic, Nat.cast_add]
          rfl
        rw [pmfExpected_bind]
        calc
          _ = pmfExpected (quicksortLaw fuel result.1 ref lo result.2)
              (fun left => ((left.clocks "comparisons" - baseline : Nat) : ℝ≥0∞) +
                comparisonMean (hi - (result.2 + 1)).toNat) := by
            apply pmfExpected_congr_support
            intro left leftPossible
            have leftPermutation := (quicksortLaw_correct fuel result.1 ref lo result.2 leftEnough
              left leftPossible).2
            have wholePermutation := rearranges_expand leftPermutation le_rfl pivotHigh.le
            have leftAllDistinct := rearranges_distinct wholePermutation partitionDistinct
            have rightDistinct : Set.InjOn (left.read ref) (Set.Ico (result.2 + 1) hi) :=
              leftAllDistinct.mono (by intro x hx; exact ⟨by have := hx.1; omega, hx.2⟩)
            exact ih left (result.2 + 1) hi rightEnough rightDistinct
              (basePartition.trans (quicksortLaw_clock_mono fuel result.1 ref lo result.2 left leftPossible "comparisons"))
          _ = _ := by
            rw [pmfExpected_add, pmfExpected_const, ih result.1 lo result.2 leftEnough leftDistinct basePartition,
              fixedClock, add_assoc]
      calc
        _ = pmfExpected (randomizedPartitionLaw charged ref lo hi nonempty)
            (fun result => fixed + (comparisonMean (result.2 - lo).toNat +
              comparisonMean (hi - (result.2 + 1)).toNat)) := pmfExpected_congr_support _ _ _ branch
        _ = fixed + pmfExpected (uniformInt lo hi nonempty)
            (fun pivot => comparisonMean (pivot - lo).toNat + comparisonMean (hi - (pivot + 1)).toNat) := by
          rw [pmfExpected_add, pmfExpected_const]
          rw [← pmfExpected_map (randomizedPartitionLaw charged ref lo hi nonempty) Prod.snd
            (fun pivot => comparisonMean (pivot - lo).toNat + comparisonMean (hi - (pivot + 1)).toNat),
            randomized_boundary_law charged ref lo hi nonempty distinct]
        _ = _ := by
          dsimp only [fixed]
          rw [add_assoc, uniform_comparison_recurrence]
    · have length : (hi - lo).toNat = 0 ∨ (hi - lo).toNat = 1 := by omega
      rcases length with empty | singleton
      · simp only [quicksortLaw, dif_neg large, pmfExpected_pure, empty, comparisonMean_zero, add_zero]
        rfl
      · simp only [quicksortLaw, dif_neg large, pmfExpected_pure, singleton, comparisonMean_one, add_zero]
        rfl

end QuicksortAnalysis
