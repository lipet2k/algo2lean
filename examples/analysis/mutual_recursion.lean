import MutualRecursionGenerated

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `natural_summaries`: Reusable parity contracts.
- `outputs`: Even and odd outputs exist.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace MutualRecursionAnalysis

/-- The evenness of a natural number, alternating at each successor. -/
def evenValue : Nat → Bool
  | 0 => true
  | n + 1 => !(evenValue n)

/-- Both nonpositive cases terminate immediately, preserving the caller's heap. -/
theorem nonpositive_summaries (heap : Heap) (n : Int) (nonpositive : n ≤ 0) :
    is_even.Call heap n heap true ∧ is_odd.Call heap n heap false := by
  constructor
  · refine ⟨True.intro, ?_⟩
    intro stack
    apply Reaches.trans (Reaches.single (Step.is_even_pc7 ..))
    apply Reaches.trans (Reaches.single (Step.is_even_pc6_true _ _ _
      (by simpa only [decide_eq_true_eq] using nonpositive)))
    apply Reaches.trans (Reaches.single (Step.is_even_pc5 ..))
    exact Reaches.single (Step.is_even_pc4 ..)
  · refine ⟨True.intro, ?_⟩
    intro stack
    apply Reaches.trans (Reaches.single (Step.is_odd_pc7 ..))
    apply Reaches.trans (Reaches.single (Step.is_odd_pc6_true _ _ _
      (by simpa only [decide_eq_true_eq] using nonpositive)))
    apply Reaches.trans (Reaches.single (Step.is_odd_pc5 ..))
    exact Reaches.single (Step.is_odd_pc4 ..)

/-- One simultaneous induction verifies both directions of the mutual recursion.
    These are contextual termination-and-value summaries, not bounded executions. -/
theorem natural_summaries (heap : Heap) (n : Nat) :
    is_even.Call heap (n : Int) heap (evenValue n) ∧
    is_odd.Call heap (n : Int) heap (!(evenValue n)) := by
  induction n with
  | zero => exact nonpositive_summaries heap 0 (by omega)
  | succ n inductionHypothesis =>
    have previous : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
    constructor
    · refine ⟨True.intro, ?_⟩
      intro stack
      apply Reaches.trans (Reaches.single (Step.is_even_pc7 ..))
      apply Reaches.trans (Reaches.single (Step.is_even_pc6_false _ _ _ (by simp)))
      apply Reaches.trans (Reaches.single (Step.is_even_pc3 ..))
      apply Reaches.trans (Reaches.single (Step.is_even_pc2 ..))
      simp only [previous]
      apply Reaches.trans (inductionHypothesis.2.2 _)
      exact Reaches.single (Step.is_even_pc1 ..)
    · refine ⟨True.intro, ?_⟩
      intro stack
      apply Reaches.trans (Reaches.single (Step.is_odd_pc7 ..))
      apply Reaches.trans (Reaches.single (Step.is_odd_pc6_false _ _ _ (by simp)))
      apply Reaches.trans (Reaches.single (Step.is_odd_pc3 ..))
      apply Reaches.trans (Reaches.single (Step.is_odd_pc2 ..))
      simp only [previous]
      apply Reaches.trans (inductionHypothesis.1.2 _)
      simp only [evenValue, Bool.not_not]
      exact Reaches.single (Step.is_odd_pc1 ..)

/-- Both signed-input contracts preserve the caller's entire heap and clocks. -/
theorem summaries (heap : Heap) (n : Int) :
    is_even.Call heap n heap (evenValue n.toNat) ∧
    is_odd.Call heap n heap (!(evenValue n.toNat)) := by
  by_cases nonpositive : n ≤ 0
  · simpa [Int.toNat_eq_zero.mpr nonpositive, evenValue] using
      nonpositive_summaries heap n nonpositive
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ n)] using natural_summaries heap n.toNat

-- Main result: Correctness
/-- Both functions have complementary outputs on every integer input; nonpositive
    integers use the source's zero case. This asserts existence, not uniqueness. -/
theorem outputs (n : Int) :
    is_even.Returns n (evenValue n.toNat) ∧
    is_odd.Returns n (!(evenValue n.toNat)) := by
  exact ⟨⟨{}, (summaries {} n).1.run⟩, ⟨{}, (summaries {} n).2.run⟩⟩

end MutualRecursionAnalysis
