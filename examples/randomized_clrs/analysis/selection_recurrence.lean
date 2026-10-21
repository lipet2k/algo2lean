import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
The expected-size calculation behind RANDOMIZED-SELECT. A uniform pivot rank
leaves only the side containing the requested rank. These mathematical lemmas
isolate averaging from heap mutation and recursive call mechanics.
-/

namespace SelectionAnalysis
open scoped BigOperators

/-- Size of the only recursive subproblem after choosing a pivot rank. -/
def nextSize (size rank pivot : Nat) : Nat :=
  if pivot < rank then size - pivot - 1 else if rank < pivot then pivot else 0

/-- The next recursive interval is strictly shorter than the current interval. -/
theorem nextSize_lt (size rank pivot : Nat) (pivotValid : pivot < size) :
    nextSize size rank pivot < size := by
  unfold nextSize
  split_ifs <;> omega

private theorem sum_ranks (size : Nat) :
    (∑ pivot ∈ Finset.range size, (pivot : ℚ)) = (size : ℚ) * (size - 1) / 2 := by
  induction size with
  | zero => simp
  | succ size ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Exact sum of remaining subproblem sizes over every pivot rank. -/
theorem sum_nextSize (size rank : Nat) (valid : rank < size) :
    (∑ pivot ∈ Finset.range size, (nextSize size rank pivot : ℚ)) =
      (size : ℚ) * (size - 1) / 2 + rank * (size - 1 - rank) := by
  have left : (∑ pivot ∈ Finset.range rank, (nextSize size rank pivot : ℚ)) =
      (rank : ℚ) * (size - 1) - (rank : ℚ) * (rank - 1) / 2 := by
    calc
      _ = ∑ pivot ∈ Finset.range rank, ((size : ℚ) - 1 - pivot) := by
        apply Finset.sum_congr rfl
        intro pivot member
        have below := Finset.mem_range.mp member
        simp only [nextSize, below, ↓reduceIte]
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, sum_ranks]; simp [mul_sub]
  have right : (∑ pivot ∈ Finset.Ico (rank + 1) size, (nextSize size rank pivot : ℚ)) =
      (size : ℚ) * (size - 1) / 2 - ((rank : ℚ) + 1) * rank / 2 := by
    calc
      _ = ∑ pivot ∈ Finset.Ico (rank + 1) size, (pivot : ℚ) := by
        apply Finset.sum_congr rfl
        intro pivot member
        have above := (Finset.mem_Ico.mp member).1
        simp [nextSize, show ¬ pivot < rank by omega, show rank < pivot by omega]
      _ = _ := by
        rw [Finset.sum_Ico_eq_sub _ (by omega), sum_ranks, sum_ranks]
        push_cast
        ring
  rw [← Finset.sum_range_add_sum_Ico (fun pivot => (nextSize size rank pivot : ℚ))
    (show rank + 1 ≤ size by omega), Finset.sum_range_succ, left, right]
  simp only [nextSize, lt_self_iff_false, ↓reduceIte, Nat.cast_zero, add_zero]
  ring

/-- The expected recursive size is at most three quarters of the original size. -/
theorem average_nextSize_le (size rank : Nat) (valid : rank < size) :
    (∑ pivot ∈ Finset.range size, (nextSize size rank pivot : ℚ)) / size ≤
      3 * (size : ℚ) / 4 := by
  rw [sum_nextSize size rank valid]
  have positive : (0 : ℚ) < size := by exact_mod_cast (by omega : 0 < size)
  apply (div_le_iff₀ positive).2
  have square := sq_nonneg ((size : ℚ) - 1 - 2 * rank)
  have nonnegative : (0 : ℚ) ≤ size := positive.le
  nlinarith

/-- Rank requested within the surviving interval. -/
def nextRank (rank pivot : Nat) : Nat :=
  if pivot < rank then rank - pivot - 1 else rank

theorem nextRank_valid (size rank pivot : Nat) (rankValid : rank < size)
    (pivotValid : pivot < size) (different : pivot ≠ rank) :
    nextRank rank pivot < nextSize size rank pivot := by
  unfold nextRank nextSize
  split_ifs <;> omega

/-- Any comparison-cost recurrence obtained by uniformly choosing a pivot and
recursing only on the requested side has a linear upper bound. -/
theorem comparisons_le_linear (cost : Nat → Nat → ℚ)
    (recurrence : ∀ size rank, rank < size → cost size rank ≤
      (size : ℚ) - 1 +
        (∑ pivot ∈ Finset.range size, if pivot = rank then 0 else
          cost (nextSize size rank pivot) (nextRank rank pivot)) / size)
    (size rank : Nat) (valid : rank < size) :
    cost size rank ≤ 4 * size := by
  induction size using Nat.strong_induction_on generalizing rank with
  | h size ih =>
    have positive : (0 : ℚ) < size := by exact_mod_cast (by omega : 0 < size)
    have children :
        (∑ pivot ∈ Finset.range size, if pivot = rank then 0 else
          cost (nextSize size rank pivot) (nextRank rank pivot)) ≤
        ∑ pivot ∈ Finset.range size, 4 * (nextSize size rank pivot : ℚ) := by
      apply Finset.sum_le_sum
      intro pivot member
      have pivotValid := Finset.mem_range.mp member
      by_cases same : pivot = rank
      · simp [same, nextSize]
      · simpa only [same, ↓reduceIte] using
          ih (nextSize size rank pivot) (nextSize_lt size rank pivot pivotValid)
            (nextRank rank pivot) (nextRank_valid size rank pivot valid pivotValid same)
    rw [← Finset.mul_sum] at children
    have average := div_le_div_of_nonneg_right children positive.le
    have shrink := average_nextSize_le size rank valid
    have step := recurrence size rank valid
    rw [mul_div_assoc] at average
    nlinarith

/-- Integer form of the averaging estimate, convenient for nonnegative costs. -/
theorem sum_nextSize_bound (size rank : Nat) (valid : rank < size) :
    4 * (∑ pivot ∈ Finset.range size, nextSize size rank pivot) ≤ 3 * size * size := by
  have positive : (0 : ℚ) < size := by exact_mod_cast (by omega : 0 < size)
  have average := (div_le_iff₀ positive).mp (average_nextSize_le size rank valid)
  have bound : (4 : ℚ) * (∑ pivot ∈ Finset.range size, (nextSize size rank pivot : ℚ)) ≤
      3 * size * size := by nlinarith
  exact_mod_cast bound

end SelectionAnalysis
