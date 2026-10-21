import Algo2LeanLib.ParallelBounds
set_option maxRecDepth 4096

/-! Integer recurrence bounds for CLRS parallel merge. The generated execution
contracts separately establish these recurrence inequalities. -/
namespace Algo2Lean.ParallelMerge
theorem log_mono {n m : Nat} (h : n ≤ m) : Nat.log2 n ≤ Nat.log2 m := by
  by_cases hn : n = 0
  · subst n; simp
  · exact (Nat.le_log2 (by omega : m ≠ 0)).2 (Nat.le_trans (Nat.log2_self_le hn) h)
theorem log_double_bound (a b : Nat) (hb : 0 < b) (h : a ≤ 2*b) :
     Nat.log2 a ≤ Nat.log2 b + 1 := by
  have hh := log_mono h
  rw [Nat.log2_two_mul (by omega)] at hh
  exact hh
theorem merge_log_budget (m n j : Nat) (large : 0 < m) (order : n ≤ m) (split : j ≤ n) :
    Nat.log2 (m+n+1) + Nat.log2 (n+1) ≤
      Nat.log2 (m/2+j+1) + Nat.log2 (m-m/2-1+(n-j)+1) + 4 := by
  have parent := log_double_bound (m+n+1) (m+1) (by omega) (by omega)
  have left := log_double_bound (m+1) (m/2+j+1) (by omega) (by omega)
  have right := log_double_bound (n+1) (2*(m-m/2-1+(n-j)+1)) (by omega) (by omega)
  rw [Nat.log2_two_mul (by omega)] at right
  omega
theorem merge_work_combine (m n j left right search : Nat)
    (large : 0 < m) (order : n ≤ m) (split : j ≤ n)
    (hl : left + 64 * Nat.log2 (m/2+j+1) + 512 ≤ 1024 * (m/2+j+1))
    (hr : right + 64 * Nat.log2 (m-m/2-1+(n-j)+1) + 512 ≤ 1024 * (m-m/2-1+(n-j)+1))
    (hs : search ≤ 64 * (Nat.log2 (n+1)+1)) :
    left + right + search + 128 + 64 * Nat.log2 (m+n+1) + 512 ≤ 1024*(m+n+1) := by
  have logs := merge_log_budget m n j large order split
  have sizes : (m/2+j+1) + (m-m/2-1+(n-j)+1) = m+n+1 := by omega
  omega
def mergeHeight (n : Nat) : Nat := if n=0 then 1 else mergeHeight (3*n/4)+1
termination_by n
decreasing_by omega
theorem mergeHeight_pos (n : Nat) : 0 < mergeHeight n := by
  rw [mergeHeight]
  split <;> omega
theorem mergeHeight_step (n : Nat) (h : 0 < n) : mergeHeight n = mergeHeight (3*n/4)+1 := by
  rw [mergeHeight]; simp [show n≠0 by omega]
theorem mergeHeight_step_le (n : Nat) : mergeHeight n ≤ mergeHeight (3*n/4)+1 := by
  by_cases h : n=0
  · subst n; simp only [Nat.mul_zero, Nat.zero_div]; omega
  · rw [mergeHeight_step n (by omega)]
    exact Nat.le_refl _
theorem mergeHeight_mono {n m : Nat} (h : n≤m) : mergeHeight n ≤ mergeHeight m := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    by_cases hn : n=0
    · subst n
      have positive := mergeHeight_pos m
      have zero : mergeHeight 0 = 1 := by rw [mergeHeight]; decide
      rw [zero]
      omega
    · have hm : 0<m := by omega
      rw [mergeHeight_step n (by omega), mergeHeight_step m hm]
      exact Nat.add_le_add_right (ih (3*m/4) (by omega) (by omega : 3*n/4≤3*m/4)) 1
theorem mergeHeight_pow (n k : Nat) (h : n ≤ 2^k) : mergeHeight n ≤ 3*k+2 := by
  induction k generalizing n with
  | zero =>
    have : n≤1 := by simpa using h
    have : n=0 ∨ n=1 := by omega
    rcases this with rfl | rfl <;> simp [mergeHeight]
  | succ k ih =>
    have size : n ≤ 2*(2^k) := by simpa [Nat.pow_succ, Nat.mul_comm] using h
    have a := mergeHeight_step_le n
    have b := mergeHeight_step_le (3*n/4)
    have c := mergeHeight_step_le (3*(3*n/4)/4)
    have small : 3*(3*(3*n/4)/4)/4 ≤ 2^k := by omega
    have bound := ih _ small
    omega
theorem mergeHeight_log (n : Nat) : mergeHeight n ≤ 3*Nat.log2 (n+1)+5 := by
  have := mergeHeight_pow n (Nat.log2 (n+1)+1) (Nat.le_trans (by omega : n≤n+1) (Nat.le_of_lt Nat.lt_log2_self))
  omega

/-- Amortized linear-work budget. The logarithmic credit pays for each search. -/
def mergeWork (n : Nat) : Nat := 1024*(n+1) - 64*Nat.log2 (n+1) - 512

theorem mergeWork_budget (n : Nat) :
    mergeWork n + 64*Nat.log2 (n+1) + 512 = 1024*(n+1) := by
  have bound := Nat.log2_le_self (n+1)
  unfold mergeWork
  omega

theorem mergeWork_base : 12 ≤ mergeWork 0 := by decide

theorem mergeWork_step (m n j : Nat) (large : 0 < m) (order : n ≤ m) (split : j ≤ n) :
    mergeWork (m/2+j) + mergeWork (m-m/2-1+(n-j)) +
      32*(Nat.log2 (n+1)+1) + 40 ≤ mergeWork (m+n) := by
  have left := mergeWork_budget (m/2+j)
  have right := mergeWork_budget (m-m/2-1+(n-j))
  have total := mergeWork_budget (m+n)
  have combined := merge_work_combine m n j (mergeWork (m/2+j))
    (mergeWork (m-m/2-1+(n-j))) (32*(Nat.log2 (n+1)+1)) large order split
    (Nat.le_of_eq left) (Nat.le_of_eq right) (by omega)
  omega

theorem mergeWork_linear (n : Nat) : mergeWork n ≤ 1024*(n+1) := by
  have := mergeWork_budget n
  omega

/-- One logarithmic search budget per level of the merge recursion. -/
def mergeSpan (n : Nat) : Nat := 256*mergeHeight n*(Nat.log2 (n+1)+1)

theorem mergeSpan_base : 12 ≤ mergeSpan 0 := by simp [mergeSpan, mergeHeight, Nat.log2_def]

theorem mergeSpan_step (m n j : Nat) (large : 0 < m) (order : n ≤ m) (split : j ≤ n) :
    max (mergeSpan (m/2+j)) (mergeSpan (m-m/2-1+(n-j))) +
      32*(Nat.log2 (n+1)+1) + 40 ≤ mergeSpan (m+n) := by
  have leftSize : m/2+j ≤ 3*(m+n)/4 := by omega
  have rightSize : m-m/2-1+(n-j) ≤ 3*(m+n)/4 := by omega
  have lh := mergeHeight_mono leftSize
  have rh := mergeHeight_mono rightSize
  have ll := log_mono (show m/2+j+1 ≤ m+n+1 by omega)
  have rl := log_mono (show m-m/2-1+(n-j)+1 ≤ m+n+1 by omega)
  have search := log_mono (show n+1 ≤ m+n+1 by omega)
  have leftBound : mergeSpan (m/2+j) ≤ 256*mergeHeight (3*(m+n)/4)*(Nat.log2 (m+n+1)+1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 256 lh) (Nat.add_le_add_right ll 1)
  have rightBound : mergeSpan (m-m/2-1+(n-j)) ≤ 256*mergeHeight (3*(m+n)/4)*(Nat.log2 (m+n+1)+1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 256 rh) (Nat.add_le_add_right rl 1)
  have both := Nat.max_le.mpr ⟨leftBound, rightBound⟩
  have toll : 32*(Nat.log2 (n+1)+1)+40 ≤ 256*(Nat.log2 (m+n+1)+1) := by omega
  calc
    _ ≤ 256*mergeHeight (3*(m+n)/4)*(Nat.log2 (m+n+1)+1) + 256*(Nat.log2 (m+n+1)+1) := by omega
    _ = mergeSpan (m+n) := by
      unfold mergeSpan
      rw [mergeHeight_step (m+n) (by omega)]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega

theorem mergeSpan_quadratic (n : Nat) : mergeSpan n ≤ 4096*(Nat.log2 (n+1)+1)^2 := by
  have height := mergeHeight_log n
  have height' : mergeHeight n ≤ 16*(Nat.log2 (n+1)+1) := by omega
  have bound := Nat.mul_le_mul_right (Nat.log2 (n+1)+1) (Nat.mul_le_mul_left 256 height')
  unfold mergeSpan
  calc
    256*mergeHeight n*(Nat.log2 (n+1)+1) ≤ 256*(16*(Nat.log2 (n+1)+1))*(Nat.log2 (n+1)+1) := bound
    _ = (256*16)*((Nat.log2 (n+1)+1)*(Nat.log2 (n+1)+1)) := by ac_rfl
    _ = 4096*(Nat.log2 (n+1)+1)^2 := by rw [Nat.pow_two]

end Algo2Lean.ParallelMerge
