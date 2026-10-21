import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
The comparison recurrence for a uniformly chosen pivot. The exact answer is
expressed with harmonic numbers; its logarithmic upper bound gives the familiar
expected O(n log n) guarantee.
-/

namespace QuicksortAnalysis
open scoped BigOperators

/-- Exact expected comparisons for n distinct keys. -/
def comparisons (n : Nat) : ℚ := 2 * (n + 1) * harmonic n - 4 * n

@[simp] theorem comparisons_zero : comparisons 0 = 0 := by simp [comparisons]
@[simp] theorem comparisons_one : comparisons 1 = 0 := by norm_num [comparisons, harmonic]

/-- The closed form satisfies the first-order difference of the quicksort recurrence. -/
theorem comparisons_step (n : Nat) :
    (n + 1 : ℚ) * comparisons (n + 1) = (n + 2) * comparisons n + 2 * n := by
  unfold comparisons
  rw [harmonic_succ]
  push_cast
  have nonzero : (n + 1 : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- The sum of all shorter subproblems recovers the divide-and-conquer recurrence. -/
theorem comparisons_sum (n : Nat) :
    (n : ℚ) * comparisons n = (n : ℚ) * (n - 1) +
      2 * ∑ k ∈ Finset.range n, comparisons k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    rw [comparisons_step]
    nlinarith

/-- Averaging both recursive sides over the uniformly distributed pivot rank. -/
theorem comparisons_recurrence (n : Nat) (positive : 0 < n) :
    comparisons n = (n : ℚ) - 1 +
      (∑ k ∈ Finset.range n, (comparisons k + comparisons (n - 1 - k))) / n := by
  have reverse : (∑ k ∈ Finset.range n, comparisons (n - 1 - k)) =
      ∑ k ∈ Finset.range n, comparisons k := by
    exact Finset.sum_range_reflect comparisons n
  rw [Finset.sum_add_distrib, reverse]
  have nz : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have recurrence := comparisons_sum n
  field_simp
  nlinarith

/-- Expected comparisons are nonnegative, including empty and singleton inputs. -/
theorem comparisons_nonnegative (n : Nat) : 0 ≤ comparisons n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n = 0
    · simp [zero]
    rw [comparisons_recurrence n (by omega)]
    apply add_nonneg
    · have positive : (1 : ℚ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    · apply div_nonneg
      · apply Finset.sum_nonneg
        intro k member
        have below := Finset.mem_range.mp member
        exact add_nonneg (ih k below) (ih (n - 1 - k) (by omega))
      · positivity

/-- A simple logarithmic bound avoids negative terms in the public runtime estimate. -/
theorem comparisons_le_log (n : Nat) :
    (comparisons n : ℝ) ≤ 2 * (n + 1) * (1 + Real.log n) := by
  have harmonicBound := harmonic_le_one_add_log n
  unfold comparisons
  push_cast
  have factor : (0 : ℝ) ≤ 2 * (n + 1) := by positivity
  have product := mul_le_mul_of_nonneg_left harmonicBound factor
  nlinarith

noncomputable section
open scoped ENNReal

/-- The exact comparison expectation as a nonnegative extended real. -/
def comparisonMean (n : Nat) : ℝ≥0∞ := ENNReal.ofReal (comparisons n)

@[simp] theorem comparisonMean_zero : comparisonMean 0 = 0 := by simp [comparisonMean]
@[simp] theorem comparisonMean_one : comparisonMean 1 = 0 := by simp [comparisonMean]

/-- The same recurrence in the arithmetic used by probability expectations. -/
theorem comparisonMean_recurrence (n : Nat) (positive : 0 < n) :
    comparisonMean n = ((n - 1 : Nat) : ℝ≥0∞) +
      (∑ k ∈ Finset.range n, (comparisonMean k + comparisonMean (n - 1 - k))) *
        (n : ℝ≥0∞)⁻¹ := by
  have nonnegative (k : Nat) : (0 : ℝ) ≤ comparisons k := by
    exact_mod_cast comparisons_nonnegative k
  have recurrence := congrArg (fun value : ℚ => (value : ℝ)) (comparisons_recurrence n positive)
  push_cast at recurrence
  have base : (n : ℝ) - 1 = ((n - 1 : Nat) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [base] at recurrence
  have identity := congrArg ENNReal.ofReal recurrence
  have sumNonnegative : (0 : ℝ) ≤ ∑ k ∈ Finset.range n,
      ((comparisons k : ℝ) + (comparisons (n - 1 - k) : ℝ)) :=
    Finset.sum_nonneg (by intros; exact add_nonneg (nonnegative _) (nonnegative _))
  rw [ENNReal.ofReal_add (by positivity) (div_nonneg sumNonnegative (by positivity)), ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_sum_of_nonneg (by intros; exact add_nonneg (nonnegative _) (nonnegative _))] at identity
  simp only [ENNReal.ofReal_natCast, div_eq_mul_inv] at identity
  simpa only [comparisonMean, ENNReal.ofReal_add (nonnegative _) (nonnegative _)] using identity

end
end QuicksortAnalysis
