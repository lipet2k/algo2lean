import SumLoopGeneratedPoints

/-!
Analysis outline:
- `natural_summary`: Reusable summation contract.
- `output`: Summation output exists.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace SumLoopAnalysis

/-- A sum of `count` successive integers, starting at `first`. -/
def consecutiveSum (first : Int) : Nat → Int
  | 0 => 0
  | count + 1 => first + consecutiveSum (first + 1) count

/-- Starting at the named loop test with `count` remaining values, finish with
    their sum added to `total`. This local fact needs no execution history and
    is reusable under any caller stack. -/
theorem remaining_summary (count : Nat) (state : Configuration) (first total : Int)
    (location : sum_to.At.loop state)
    (readFirst : sum_to.Local.i state = some first)
    (readTotal : sum_to.Local.total state = some total)
    (readBound : sum_to.Local.n state = some (first + (count : Int) - 1)) :
    sum_to.CallFrom state state.heap (total + consecutiveSum first count) := by
  induction count generalizing state first total with
  | zero =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_sum_to pc s =>
        have counter : pc = 4 := by
          unfold sum_to.At.loop at location
          split at location <;> simp_all
        subst pc
        simp [sum_to.Local.i, sum_to.Local.total, sum_to.Local.n] at readFirst readTotal readBound
        intro stack
        apply Reaches.trans (Reaches.single (Step.sum_to_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.sum_to_pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega)))
        apply Reaches.trans (Reaches.single (Step.sum_to_pc2 ..))
        simpa [consecutiveSum, readTotal, Config.heap] using Reaches.single (Step.sum_to_pc1 heap _ stack)
  | succ count inductionHypothesis =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_sum_to pc s =>
        have counter : pc = 4 := by
          unfold sum_to.At.loop at location
          split at location <;> simp_all
        subst pc
        simp [sum_to.Local.i, sum_to.Local.total, sum_to.Local.n] at readFirst readTotal readBound
        have next := inductionHypothesis
          (.active heap (.fn_sum_to 4
            { s with t4 := decide (s.v2 ≤ s.v0), v1 := s.v1 + s.v2, v2 := s.v2 + 1 }) originalStack)
          (first + 1) (total + first)
          True.intro
          (by simp [sum_to.Local.i, readFirst])
          (by simp [sum_to.Local.total, readTotal, readFirst])
          (by simp [sum_to.Local.n]; omega)
        intro stack
        apply Reaches.trans (Reaches.single (Step.sum_to_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.sum_to_pc3_true _ _ _
          (by simp only [decide_eq_true_eq]; omega)))
        apply Reaches.trans (Reaches.single (Step.sum_to_pc6 ..))
        apply Reaches.trans (Reaches.single (Step.sum_to_pc5 ..))
        simpa [consecutiveSum, Int.add_assoc] using next stack

/-- The loop terminates on every natural input and returns 1 + ... + n.
    The call contract is obtained by summing the remaining loop interval. -/
theorem natural_summary (heap : Heap) (n : Nat) :
    sum_to.Call heap (n : Int) heap (consecutiveSum 1 n) := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.sum_to_pc8 ..))
  apply Reaches.trans (Reaches.single (Step.sum_to_pc7 ..))
  have loop := remaining_summary n
    (.active heap (.fn_sum_to 4 { v0 := n, v1 := 0, v2 := 1 }) stack) 1 0
    True.intro rfl rfl (by simp [sum_to.Local.n]; omega)
  simpa using loop stack

/-- For n ≤ 0 the guard is initially false and the result is zero. -/
theorem nonpositive_summary (heap : Heap) (n : Int) (nonpositive : n ≤ 0) :
    sum_to.Call heap n heap 0 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.sum_to_pc8 ..))
  apply Reaches.trans (Reaches.single (Step.sum_to_pc7 ..))
  apply Reaches.trans (Reaches.single (Step.sum_to_pc4 ..))
  apply Reaches.trans (Reaches.single (Step.sum_to_pc3_false _ _ _
    (by simp only [decide_eq_false_iff_not]; omega)))
  apply Reaches.trans (Reaches.single (Step.sum_to_pc2 ..))
  exact Reaches.single (Step.sum_to_pc1 ..)

-- Main result: Correctness
/-- Every integer input has the expected sum as an output. This proves existence
    of a completed run; uniqueness is not claimed here. -/
theorem output (n : Int) : sum_to.Returns n (consecutiveSum 1 n.toNat) := by
  have specification : sum_to.Call ({} : Heap) n {} (consecutiveSum 1 n.toNat) := by
    by_cases nonpositive : n ≤ 0
    · simpa [Int.toNat_eq_zero.mpr nonpositive, consecutiveSum] using
        nonpositive_summary {} n nonpositive
    · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ n)] using natural_summary {} n.toNat
  exact ⟨{}, specification.1, specification.2.root⟩

end SumLoopAnalysis
