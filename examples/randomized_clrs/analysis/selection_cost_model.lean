import Algo.selection_model.Analysis
import Algo.selection_recurrence.Analysis

/-!
Expected comparisons for the recursive selection law. Partition's exact raw
clock increment is composed with the one surviving recursive call. Uniformity
of the returned boundary, rather than any independence assumption about the
mutated heap, gives the averaging estimate.
-/

noncomputable section
namespace SelectionAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis
open scoped ENNReal BigOperators

private theorem expected_const_add {α : Type*} (law : PMF α) (constant : ℝ≥0∞)
    (payoff : α → ℝ≥0∞) :
    pmfExpected law (fun x => constant + payoff x) = constant + pmfExpected law payoff := by
  unfold pmfExpected
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Integer intervals and their zero-based offsets have identical finite sums. -/
theorem sum_offsets {α : Type*} [AddCommMonoid α] (lo hi : Int) (nonempty : lo < hi)
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

/-- Uniform pivot selection leaves at most three quarters of the current
interval in expectation, expressed in the nonnegative expectation arithmetic. -/
theorem uniform_remaining_bound (lo hi requested : Int) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo) :
    pmfExpected (uniformInt lo hi nonempty)
      (fun pivot => 4 * (nextSize (hi - lo).toNat requested.toNat (pivot - lo).toNat : ℝ≥0∞)) ≤
      3 * ((hi - lo).toNat : ℝ≥0∞) := by
  let size := (hi - lo).toNat
  have positive : 0 < size := by dsimp [size]; omega
  have rankValid : requested.toNat < size := by dsimp [size]; omega
  have bound := sum_nextSize_bound size requested.toNat rankValid
  have bound' : (4 : ℝ≥0∞) * (∑ pivot ∈ Finset.range size,
      (nextSize size requested.toNat pivot : ℝ≥0∞)) ≤ 3 * size * size := by
    exact_mod_cast bound
  rw [pmfExpected_uniformInt, ← Finset.sum_mul, sum_offsets lo hi nonempty
      (fun offset => 4 * (nextSize (hi - lo).toNat requested.toNat offset : ℝ≥0∞)),
    ← Finset.mul_sum]
  change (4 * ∑ pivot ∈ Finset.range size,
    (nextSize size requested.toNat pivot : ℝ≥0∞)) * (size : ℝ≥0∞)⁻¹ ≤ 3 * size
  calc
    _ ≤ (3 * size * size) * (size : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast positive.ne') (by simp), mul_one]

/-- Expected payoffs respect inequalities on outcomes that have positive mass. -/
private theorem expected_le_on_support {α : Type*} (law : PMF α) (first second : α → ℝ≥0∞)
    (bound : ∀ x ∈ law.support, first x ≤ second x) :
    pmfExpected law first ≤ pmfExpected law second := by
  unfold pmfExpected
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases possible : law value = 0
  · simp [possible]
  · have inequality := bound value possible
    gcongr

/-- With any earlier comparison-clock baseline, selection uses at most four
comparisons per input element in expectation. The bound applies uniformly to
every heap produced by a partition, preserving correlations through recursion. -/
theorem selectionLaw_comparisons_le (fuel : Nat) (heap : Heap) (ref : SeqRef)
    (lo hi requested : Int) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi))
    (baseline : Nat) (baselineLe : baseline ≤ heap.clocks "comparisons") :
    pmfExpected (selectionLaw fuel heap ref lo hi requested)
      (fun result => ((result.1.clocks "comparisons" - baseline : Nat) : ℝ≥0∞)) ≤
      ((heap.clocks "comparisons" - baseline : Nat) : ℝ≥0∞) +
        4 * ((hi - lo).toNat : ℝ≥0∞) := by
  induction fuel generalizing heap lo hi requested with
  | zero =>
    simp only [selectionLaw, pmfExpected_pure]
    exact le_add_right le_rfl
  | succ fuel ih =>
    by_cases singleton : hi - lo = 1
    · simp only [selectionLaw, if_pos singleton, pmfExpected_pure]
      simp only [Heap.tick]
      exact le_add_right le_rfl
    · rw [selectionLaw, if_neg singleton, dif_pos nonempty, pmfExpected_bind]
      let charged := heap.tick "selection_calls"
      let size := (hi - lo).toNat
      let oldCost : ℝ≥0∞ := ((heap.clocks "comparisons" - baseline : Nat) : ℝ≥0∞)
      let fixedCost : ℝ≥0∞ := oldCost + ((hi - lo - 1).toNat : ℝ≥0∞)
      have chargedDistinct : Set.InjOn (charged.read ref) (Set.Ico lo hi) := distinct
      have branchBound : ∀ result ∈ (randomizedPartitionLaw charged ref lo hi nonempty).support,
          pmfExpected (if requested = result.2 - lo then
              PMF.pure (result.1, result.1.read ref result.2)
            else if requested < result.2 - lo then
              selectionLaw fuel result.1 ref lo result.2 requested
            else selectionLaw fuel result.1 ref (result.2 + 1) hi
              (requested - (result.2 - lo) - 1))
            (fun final => ((final.1.clocks "comparisons" - baseline : Nat) : ℝ≥0∞)) ≤
          fixedCost + 4 * (nextSize size requested.toNat (result.2 - lo).toNat : ℝ≥0∞) := by
        intro result possible
        have facts := randomizedPartitionLaw_correct charged ref lo hi nonempty result possible
        have pivotLow := facts.1.1
        have pivotHigh := facts.1.2.1
        have afterDistinct := rearranges_distinct facts.2.1 chargedDistinct
        have raw := randomizedPartitionLaw_comparison_clock charged ref lo hi nonempty result possible
        have raw' : result.1.clocks "comparisons" = heap.clocks "comparisons" +
            (hi - lo - 1).toNat := by simpa [charged, Heap.tick] using raw
        have baseAfter : baseline ≤ result.1.clocks "comparisons" := by omega
        have fixed : ((result.1.clocks "comparisons" - baseline : Nat) : ℝ≥0∞) = fixedCost := by
          have arithmetic : result.1.clocks "comparisons" - baseline =
              (heap.clocks "comparisons" - baseline) + (hi - lo - 1).toNat := by omega
          simp only [arithmetic, Nat.cast_add]
          rfl
        split_ifs with found before
        · rw [pmfExpected_pure, fixed]
          exact le_add_right le_rfl
        · have leftValid : 0 ≤ requested ∧ requested < result.2 - lo := ⟨requestedValid.1, before⟩
          have bound := ih result.1 lo result.2 requested (by omega) leftValid
            (afterDistinct.mono (by intro x hx; obtain ⟨lower, upper⟩ := hx; exact ⟨lower, by omega⟩)) baseAfter
          have remaining : nextSize size requested.toNat (result.2 - lo).toNat =
              (result.2 - lo).toNat := by unfold nextSize; dsimp [size]; split_ifs <;> omega
          simpa only [fixed, remaining] using bound
        · have rightValid : 0 ≤ requested - (result.2 - lo) - 1 ∧
              requested - (result.2 - lo) - 1 < hi - (result.2 + 1) := by omega
          have bound := ih result.1 (result.2 + 1) hi (requested - (result.2 - lo) - 1)
            (by omega) rightValid
            (afterDistinct.mono (by intro x hx; obtain ⟨lower, upper⟩ := hx; exact ⟨by omega, upper⟩)) baseAfter
          have remaining : nextSize size requested.toNat (result.2 - lo).toNat =
              (hi - (result.2 + 1)).toNat := by unfold nextSize; dsimp [size]; split_ifs <;> omega
          simpa only [fixed, remaining] using bound
      calc
        _ ≤ pmfExpected (randomizedPartitionLaw charged ref lo hi nonempty)
            (fun result => fixedCost + 4 *
              (nextSize size requested.toNat (result.2 - lo).toNat : ℝ≥0∞)) :=
          expected_le_on_support _ _ _ branchBound
        _ = fixedCost + pmfExpected (uniformInt lo hi nonempty)
            (fun pivot => 4 * (nextSize size requested.toNat (pivot - lo).toNat : ℝ≥0∞)) := by
          rw [expected_const_add]
          rw [← pmfExpected_map (randomizedPartitionLaw charged ref lo hi nonempty) Prod.snd
            (fun pivot => 4 * (nextSize size requested.toNat (pivot - lo).toNat : ℝ≥0∞)),
            randomized_boundary_law charged ref lo hi nonempty chargedDistinct]
        _ ≤ fixedCost + 3 * (size : ℝ≥0∞) := by
          gcongr
          exact uniform_remaining_bound lo hi requested nonempty requestedValid
        _ ≤ oldCost + 4 * (size : ℝ≥0∞) := by
          have length : (hi - lo - 1).toNat + 3 * size ≤ 4 * size := by dsimp [size]; omega
          have cast : ((hi - lo - 1).toNat : ℝ≥0∞) + 3 * (size : ℝ≥0∞) ≤
              4 * (size : ℝ≥0∞) := by exact_mod_cast length
          dsimp only [fixedCost]
          rw [add_assoc]
          gcongr

end SelectionAnalysis
