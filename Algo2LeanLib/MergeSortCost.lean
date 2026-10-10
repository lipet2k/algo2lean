import Std

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Cost mathematics for balanced merge sort.

The recurrence charges one unit for every sorting call and `n` units for merging
an interval of length `n`. It applies to arbitrary natural lengths, including
empty and singleton intervals. A compiled algorithm must separately prove that
its clock increments satisfy this recurrence.
-/

namespace Algo2Lean.MergeSortCost

/-- One unit per sorting call, plus one unit per merged element. -/
def work (n : Nat) : Nat :=
  if small : n ≤ 1 then 1
  else 1 + work (n / 2) + work (n - n / 2) + n
termination_by n
decreasing_by all_goals omega

/-- Empty and singleton intervals perform only the initial sorting call. -/
theorem work_base (n : Nat) (small : n ≤ 1) : work n = 1 := by
  rw [work]
  simp [small]

@[simp] theorem work_zero : work 0 = 1 := work_base 0 (by decide)

@[simp] theorem work_one : work 1 = 1 := work_base 1 (by decide)

/-- A nontrivial interval splits into floor and ceiling halves, then merges. -/
theorem work_step (n : Nat) (large : 1 < n) :
    work n = 1 + work (n / 2) + work (n - n / 2) + n := by
  rw [work]
  simp [show ¬ n ≤ 1 by omega]

/-- At depth at most `k`, the merge work is at most `n * k`, and the binary
    recursion tree contributes at most `2 * n - 1` sorting calls. -/
theorem work_le_of_le_pow (n k : Nat) (positive : 0 < n) (size : n ≤ 2 ^ k) :
    work n + 1 ≤ n * (k + 2) := by
  induction k generalizing n with
  | zero =>
      have singleton : n = 1 := by simp only [Nat.pow_zero] at size; omega
      subst n
      simp
  | succ k ih =>
      by_cases small : n ≤ 1
      · have singleton : n = 1 := by omega
        subst n
        simp
      · have large : 1 < n := by omega
        have leftPositive : 0 < n / 2 := by omega
        have rightPositive : 0 < n - n / 2 := by omega
        have powerBound : n ≤ 2 ^ k * 2 := by simpa [Nat.pow_succ] using size
        have leftBound : n / 2 ≤ 2 ^ k := by omega
        have rightBound : n - n / 2 ≤ 2 ^ k := by omega
        have left := ih (n / 2) leftPositive leftBound
        have right := ih (n - n / 2) rightPositive rightBound
        calc
          work n + 1 = (work (n / 2) + 1) + (work (n - n / 2) + 1) + n := by
            rw [work_step n large]
            omega
          _ ≤ n / 2 * (k + 2) + (n - n / 2) * (k + 2) + n :=
            Nat.add_le_add_right (Nat.add_le_add left right) n
          _ = n * (k + 1 + 2) := by
            rw [← Nat.add_mul]
            have halves : n / 2 + (n - n / 2) = n := by omega
            rw [halves]
            simp only [Nat.mul_add, Nat.mul_one]
            omega

/-- A concrete bound valid at every input length, including the empty interval. -/
theorem work_le_logarithmic (n : Nat) :
    work n ≤ 2 * n * (Nat.log2 n + 1) + 1 := by
  by_cases small : n ≤ 1
  · rw [work_base n small]
    omega
  · have positive : 0 < n := by omega
    have depth := work_le_of_le_pow n (Nat.log2 n + 1) positive
      (Nat.le_of_lt Nat.lt_log2_self)
    have logPositive : 1 ≤ Nat.log2 n :=
      (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simp; omega)
    have coefficient : Nat.log2 n + 1 + 2 ≤ 2 * (Nat.log2 n + 1) := by omega
    have scaled := Nat.mul_le_mul_left n coefficient
    have bound : work n + 1 ≤ 2 * n * (Nat.log2 n + 1) := by
      apply Nat.le_trans depth
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using scaled
    omega

end Algo2Lean.MergeSortCost
