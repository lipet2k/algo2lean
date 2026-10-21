import Algo2LeanLib.ParallelMergeCost

set_option maxRecDepth 4096

/-! Work/span recurrence bounds for the preallocated CLRS parallel merge sort.
The actual source-call proof establishes these recurrences separately. -/
namespace Algo2Lean.ParallelMerge

/-- Both recursively sorted halves contribute work, followed by linear merge. -/
def sortWork (n : Nat) : Nat :=
  if n ≤ 1 then 8 else
    sortWork (n/2) + sortWork (n-n/2) + 1024*(n+1) + 32
termination_by n
decreasing_by all_goals omega

/-- The two sorts overlap; parallel merge adds quadratic-logarithmic span. -/
def sortSpan (n : Nat) : Nat :=
  if n ≤ 1 then 8 else
    max (sortSpan (n/2)) (sortSpan (n-n/2)) + 4096*(Nat.log2 (n+1)+1)^2 + 32
termination_by n
decreasing_by all_goals omega

theorem sortWork_base (n : Nat) (small : n ≤ 1) : sortWork n = 8 := by
  rw [sortWork]; simp [small]

theorem sortSpan_base (n : Nat) (small : n ≤ 1) : sortSpan n = 8 := by
  rw [sortSpan]; simp [small]

theorem sortWork_step (n : Nat) (large : 1 < n) :
    sortWork n = sortWork (n/2) + sortWork (n-n/2) + 1024*(n+1) + 32 := by
  rw [sortWork]; simp [show ¬ n≤1 by omega]

theorem sortSpan_step (n : Nat) (large : 1 < n) :
    sortSpan n = max (sortSpan (n/2)) (sortSpan (n-n/2)) + 4096*(Nat.log2 (n+1)+1)^2 + 32 := by
  rw [sortSpan]; simp [show ¬ n≤1 by omega]

/-- Work bound for any positive length fitting within a power of two. -/
theorem sortWork_pow (n k : Nat) (positive : 0 < n) (size : n ≤ 2^k) :
    sortWork n ≤ 2112*n*(k+1) := by
  induction k generalizing n with
  | zero =>
    have small : n≤1 := by simpa using size
    have : n=1 := by omega
    subst n
    rw [sortWork_base 1 (by omega)]
    decide
  | succ k ih =>
    by_cases small : n≤1
    · have : n=1 := by omega
      subst n
      rw [sortWork_base 1 (by omega)]
      simp only [Nat.mul_one, Nat.mul_add, Nat.mul_one]
      omega
    · have large : 1<n := by omega
      have sizes : n ≤ 2*(2^k) := by simpa [Nat.pow_succ, Nat.mul_comm] using size
      have left := ih (n/2) (by omega) (by omega)
      have right := ih (n-n/2) (by omega) (by omega)
      have total : n/2+(n-n/2)=n := by omega
      have children : sortWork (n/2)+sortWork (n-n/2) ≤ 2112*n*(k+1) := by
        calc
          _ ≤ 2112*(n/2)*(k+1)+2112*(n-n/2)*(k+1) := Nat.add_le_add left right
          _ = 2112*(n/2+(n-n/2))*(k+1) := by simp only [Nat.mul_add, Nat.add_mul] <;> omega
          _ = 2112*n*(k+1) := by rw [total]
      have toll : 1024*(n+1)+32 ≤ 2112*n := by omega
      rw [sortWork_step n large]
      calc
        _ ≤ 2112*n*(k+1)+2112*n := by omega
        _ = 2112*n*(k+1+1) := by simp only [Nat.mul_add, Nat.mul_one] <;> omega

private theorem square_step_le_cube_step (k : Nat) :
    k^3+(k+1)^2 ≤ (k+1)^3 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

/-- Span bound for all lengths fitting within a power of two. -/
theorem sortSpan_pow (n k : Nat) (size : n ≤ 2^k) :
    sortSpan n ≤ 16424*(k+1)^3 := by
  induction k generalizing n with
  | zero =>
    have small : n≤1 := by simpa using size
    rw [sortSpan_base n small]
    decide
  | succ k ih =>
    by_cases small : n≤1
    · rw [sortSpan_base n small]
      have one : 1 ≤ (k+1+1)^3 := Nat.one_le_pow _ _ (by omega)
      omega
    · have large : 1<n := by omega
      have sizes : n ≤ 2*(2^k) := by simpa [Nat.pow_succ, Nat.mul_comm] using size
      have left := ih (n/2) (by omega)
      have right := ih (n-n/2) (by omega)
      have children := Nat.max_le.mpr ⟨left,right⟩
      have logs : Nat.log2 (n+1)+1 ≤ 2*(k+1+1) := by
        have bound := log_mono (show n+1 ≤ 2*(2^(k+1)) by
          have power : 0 < 2^(k+1) := Nat.pow_pos (by decide)
          omega)
        rw [Nat.log2_two_mul (by have := Nat.pow_pos (n := k+1) (by decide : 0<2); omega),
          Nat.log2_two_pow] at bound
        omega
      have square := Nat.pow_le_pow_left logs 2
      have square' : (Nat.log2 (n+1)+1)^2 ≤ 4*(k+1+1)^2 := by
        simpa only [Nat.mul_pow, Nat.reducePow] using square
      have one : 1 ≤ (k+1+1)^2 := Nat.one_le_pow _ _ (by omega)
      have toll : 4096*(Nat.log2 (n+1)+1)^2+32 ≤ 16424*(k+1+1)^2 := by omega
      have difference := Nat.mul_le_mul_left 16424 (square_step_le_cube_step (k+1))
      rw [sortSpan_step n large]
      have combined := Nat.add_le_add children toll
      simp only [Nat.mul_add] at difference
      omega

/-- Explicit uniform work bound, including an empty input. -/
theorem sortWork_nlog (n : Nat) :
    sortWork n ≤ 4224*(n+1)*(Nat.log2 (n+1)+1) := by
  by_cases zero : n=0
  · subst n
    rw [sortWork_base 0 (by omega)]
    decide
  · have power : n ≤ 2^(Nat.log2 (n+1)+1) :=
      Nat.le_trans (by omega : n≤n+1) (Nat.le_of_lt Nat.lt_log2_self)
    have bound := sortWork_pow n (Nat.log2 (n+1)+1) (by omega) power
    have first : 2112*n ≤ 2112*(n+1) := by omega
    have second : Nat.log2 (n+1)+1+1 ≤ 2*(Nat.log2 (n+1)+1) := by omega
    have product := Nat.mul_le_mul first second
    calc
      sortWork n ≤ 2112*n*(Nat.log2 (n+1)+1+1) := bound
      _ ≤ 2112*(n+1)*(2*(Nat.log2 (n+1)+1)) := product
      _ = 4224*(n+1)*(Nat.log2 (n+1)+1) := by
        calc
          _ = (2112*2)*(n+1)*(Nat.log2 (n+1)+1) := by ac_rfl
          _ = _ := rfl

/-- Explicit uniform cubic-logarithmic span bound, including empty input. -/
theorem sortSpan_logcubed (n : Nat) :
    sortSpan n ≤ 131392*(Nat.log2 (n+1)+1)^3 := by
  have power : n ≤ 2^(Nat.log2 (n+1)+1) :=
    Nat.le_trans (by omega : n≤n+1) (Nat.le_of_lt Nat.lt_log2_self)
  have bound := sortSpan_pow n (Nat.log2 (n+1)+1) power
  have larger : Nat.log2 (n+1)+1+1 ≤ 2*(Nat.log2 (n+1)+1) := by omega
  have cube := Nat.pow_le_pow_left larger 3
  have cube' : (Nat.log2 (n+1)+1+1)^3 ≤ 8*(Nat.log2 (n+1)+1)^3 := by
    simpa only [Nat.mul_pow, Nat.reducePow] using cube
  have multiply := Nat.mul_le_mul_left 16424 cube'
  calc
    sortSpan n ≤ 16424*(Nat.log2 (n+1)+1+1)^3 := bound
    _ ≤ 16424*(8*(Nat.log2 (n+1)+1)^3) := multiply
    _ = 131392*(Nat.log2 (n+1)+1)^3 := by rw [← Nat.mul_assoc]

end Algo2Lean.ParallelMerge
