import FactorialGenerated

/-!
Analysis outline:
- `natural_summary`: Reusable factorial contract.
- `output`: Factorial output exists.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace FactorialAnalysis

/-- The usual mathematical factorial, represented as an unbounded integer. -/
def factorialValue : Nat → Int
  | 0 => 1
  | n + 1 => (n + 1 : Nat) * factorialValue n

/-- Nonpositive inputs take the base case, in every calling context. -/
theorem nonpositive_summary (heap : Heap) (n : Int) (nonpositive : n ≤ 0) :
    factorial.Call heap n heap 1 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.factorial_pc9 ..))
  apply Reaches.trans (Reaches.single (Step.factorial_pc8_true _ _ _
    (by simpa only [decide_eq_true_eq] using nonpositive)))
  apply Reaches.trans (Reaches.single (Step.factorial_pc2 ..))
  exact Reaches.single (Step.factorial_pc1 ..)

/-- For every natural input, factorial terminates with the mathematical factorial.
    The summary preserves an arbitrary heap and can be reused inside other calls. -/
theorem natural_summary (heap : Heap) (n : Nat) :
    factorial.Call heap (n : Int) heap (factorialValue n) := by
  induction n with
  | zero => exact nonpositive_summary heap 0 (by omega)
  | succ n inductionHypothesis =>
    refine ⟨True.intro, ?_⟩
    intro stack
    apply Reaches.trans (Reaches.single (Step.factorial_pc9 ..))
    apply Reaches.trans (Reaches.single (Step.factorial_pc8_false _ _ _
      (by simp)))
    apply Reaches.trans (Reaches.single (Step.factorial_pc7 ..))
    apply Reaches.trans (Reaches.single (Step.factorial_pc6 ..))
    apply Reaches.trans (Reaches.single (Step.factorial_pc5 ..))
    have callee := inductionHypothesis.2
    have previous : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
    simp only [previous]
    apply Reaches.trans (callee _)
    apply Reaches.trans (Reaches.single (Step.factorial_pc4 ..))
    exact Reaches.single (Step.factorial_pc3 ..)

-- Main result: Correctness
/-- All integer inputs have an output. Negative inputs are clamped to zero in the
    mathematical specification, matching the source's n ≤ 0 base case.
    This is an existence theorem; it does not assert output uniqueness. -/
theorem output (n : Int) : factorial.Returns n (factorialValue n.toNat) := by
  have specification : factorial.Call ({} : Heap) n {} (factorialValue n.toNat) := by
    by_cases nonpositive : n ≤ 0
    · simpa [Int.toNat_eq_zero.mpr nonpositive, factorialValue] using
        nonpositive_summary {} n nonpositive
    · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ n)] using natural_summary {} n.toNat
  exact ⟨{}, specification.1, specification.2.root⟩

end FactorialAnalysis
