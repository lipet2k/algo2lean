import Algo2LeanLib.Ackermann

/-!
Arithmetic bounds for the two Kruskal running-time statements. The sorting
term and vertex initialization absorb the inverse-Ackermann contribution,
even when the graph has many isolated vertices. These lemmas depend only on
the existing Ackermann definition; they do not inspect an algorithm or heap.
-/

namespace KruskalBounds

open Algo2Lean.Ackermann

private theorem iterate_successor (count value : Nat) :
    iterate (fun n => n + 1) count value = value + count := by
  induction count with
  | zero => simp
  | succ count ih => simp [iterate_succ, ih, Nat.add_assoc]

private theorem ack_one (value : Nat) : ack 1 value = 2 * value + 1 := by
  change iterate (fun n => n + 1) (value + 1) value = 2 * value + 1
  rw [iterate_successor]
  omega

/-- Hierarchy growth dominates powers of two in the hierarchy index. -/
theorem exponential_le_ack (level : Nat) : 2 ^ level ≤ ack level 1 := by
  induction level with
  | zero => simp
  | succ level ih =>
    by_cases zero : level = 0
    · subst level
      decide
    · have double := ack_mono_left (by omega : 1 ≤ level) (ack level 1)
      rw [ack_one] at double
      have step : ack (level + 1) 1 = ack level (ack level 1) := by
        simp [ack_succ, iterate]
      rw [step, Nat.pow_succ]
      omega

/-- The inverse-Ackermann factor is bounded by a binary logarithm. -/
theorem alpha_le_log (vertices : Nat) :
    alpha vertices ≤ (vertices + 1).log2 + 1 := by
  apply alpha_le (by omega)
  have threshold := exponential_le_ack ((vertices + 1).log2 + 1)
  have powerBound : vertices + 1 < 2 ^ ((vertices + 1).log2 + 1) := Nat.lt_log2_self
  omega

/-- A logarithmic vertex factor can be paid by vertex initialization and the
    edge-sorting scale. This does not require a relationship between V and E. -/
theorem logarithm_absorption (vertices edges : Nat) :
    edges * (vertices + 1).log2 ≤
      2 * (vertices + 1) + edges * (edges + 1).log2 := by
  by_cases ordered : (vertices + 1).log2 ≤ (edges + 1).log2
  · have multiplied := Nat.mul_le_mul_left edges ordered
    omega
  · have gap : (vertices + 1).log2 =
        (edges + 1).log2 + ((vertices + 1).log2 - (edges + 1).log2) := by omega
    have edgePower : edges ≤ 2 ^ ((edges + 1).log2 + 1) := by
      have : edges + 1 < 2 ^ ((edges + 1).log2 + 1) := Nat.lt_log2_self
      omega
    have differencePower : (vertices + 1).log2 - (edges + 1).log2 ≤
        2 ^ ((vertices + 1).log2 - (edges + 1).log2) :=
      Nat.le_of_lt Nat.lt_two_pow_self
    have multiplied := Nat.mul_le_mul edgePower differencePower
    have powers : 2 ^ ((edges + 1).log2 + 1) *
        2 ^ ((vertices + 1).log2 - (edges + 1).log2) =
        2 * 2 ^ (vertices + 1).log2 := by
      rw [← Nat.pow_add]
      have exponent : (edges + 1).log2 + 1 +
          ((vertices + 1).log2 - (edges + 1).log2) = (vertices + 1).log2 + 1 := by omega
      rw [exponent, Nat.pow_succ, Nat.mul_comm]
    rw [powers] at multiplied
    have vertexPower := Nat.mul_le_mul_left 2 (Nat.log2_self_le (by omega : vertices + 1 ≠ 0))
    have sum : edges * (vertices + 1).log2 = edges * (edges + 1).log2 +
        edges * ((vertices + 1).log2 - (edges + 1).log2) := by
      calc
        edges * (vertices + 1).log2 = edges * ((edges + 1).log2 +
            ((vertices + 1).log2 - (edges + 1).log2)) := congrArg (edges * ·) gap
        _ = _ := Nat.mul_add _ _ _
    omega

/-- Union-find's inverse-Ackermann work fits within the total sorting scale. -/
theorem alpha_absorption (vertices edges : Nat) :
    edges * alpha vertices ≤
      2 * (vertices + 1) + 2 * (edges * (edges + 1).log2) := by
  by_cases zero : edges = 0
  · simp [zero]
  · have logarithmPositive : 1 ≤ (edges + 1).log2 :=
      (Nat.le_log2 (by omega)).mpr (by simp; omega)
    have edgeBound := Nat.mul_le_mul_left edges logarithmPositive
    have alphaBound := Nat.mul_le_mul_left edges (alpha_le_log vertices)
    have logarithmBound := logarithm_absorption vertices edges
    simp only [Nat.mul_add, Nat.mul_one] at alphaBound edgeBound
    omega

/-- The explicit eight-clock budget has a uniform O(V + E log(E+1) + 1)
    upper bound, including empty and disconnected graphs. -/
theorem total_budget_le (vertices edges : Nat) :
    2 * edges * (3 * (edges + 1).log2 + 2) + vertices + 2 +
      edges * (10 * alpha vertices + 14) ≤
        44 * (vertices + 1 + edges * (edges + 1).log2) := by
  by_cases zero : edges = 0
  · simp only [zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_add, Nat.mul_one]
    omega
  · have logarithmPositive : 1 ≤ (edges + 1).log2 :=
      (Nat.le_log2 (by omega)).mpr (by simp; omega)
    have edgeBound := Nat.mul_le_mul_left edges logarithmPositive
    have amortizedBound := Nat.mul_le_mul_left 10 (alpha_absorption vertices edges)
    simp only [Nat.mul_one] at edgeBound
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at amortizedBound ⊢
    have e3 : edges * (3 * (edges + 1).log2) = 3 * (edges * (edges + 1).log2) := by
      simp only [Nat.mul_left_comm]
    have e10 : edges * (10 * alpha vertices) = 10 * (edges * alpha vertices) := by
      simp only [Nat.mul_left_comm]
    omega

end KruskalBounds
