import GcdGeneratedPoints

/-!
Euclid's algorithm on all signed integers. The proof outline is sign
normalization, one Euclidean reduction, well-founded induction on the second
argument, and an ordinary output theorem. Transition details are confined to
small local-execution lemmas; their statements use the named source locations.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace GcdAnalysis

/-- Normalizing a sign produces the nonnegative mathematical absolute value. -/
theorem absolute_value (a : Int) :
    (a.natAbs : Int) = if a < 0 then -a else a := by
  by_cases negative : a < 0
  · rw [if_pos negative]
    simpa using Int.natAbs_of_nonneg (a := -a) (by omega)
  · rw [if_neg negative]
    exact Int.natAbs_of_nonneg (by omega)

/-- Euclidean reduction preserves the mathematical greatest common divisor. -/
theorem gcd_reduction (a b : Int) : Int.gcd b (a % b) = Int.gcd a b := by
  calc
    Int.gcd b (a % b) = Int.gcd b (a % b + b * (a / b)) :=
      (Int.gcd_add_mul_left_right b (a % b) (a / b)).symm
    _ = Int.gcd b a := by rw [Int.emod_add_mul_ediv]
    _ = Int.gcd a b := Int.gcd_comm _ _

/-- At a loop test with zero second argument, return the first argument. -/
theorem loop_zero (state : Configuration) (a : Int)
    (location : gcd.At.loop state)
    (readA : gcd.Local.a state = some a)
    (readB : gcd.Local.b state = some 0) :
    gcd.CallFrom state state.heap a := by
  cases state with
  | done => cases location
  | active heap frame oldStack =>
    cases frame with
    | invalid => cases location
    | fn_gcd pc s =>
      have counter : pc = 4 := by
        unfold gcd.At.loop at location
        split at location <;> simp_all
      subst pc
      simp [gcd.Local.a, gcd.Local.b] at readA readB
      intro stack
      apply Reaches.trans (Reaches.single (Step.gcd_pc4 ..))
      apply Reaches.trans (Reaches.single (Step.gcd_pc3_false _ _ _ (by simpa)))
      apply Reaches.trans (Reaches.single (Step.gcd_pc2 ..))
      simpa [readA, Config.heap] using Reaches.single (Step.gcd_pc1 heap _ stack)

/-- One loop iteration replaces (a,b) by (b,a%b). A summary proved for that
    smaller pair can therefore be reused at the current named loop test. -/
theorem loop_reduce (a b output : Int) (positive : 0 < b)
    (continuation : ∀ next, gcd.At.loop next →
      gcd.Local.a next = some b → gcd.Local.b next = some (a % b) →
      gcd.CallFrom next next.heap output)
    (state : Configuration) (location : gcd.At.loop state)
    (readA : gcd.Local.a state = some a)
    (readB : gcd.Local.b state = some b) :
    gcd.CallFrom state state.heap output := by
  cases state with
  | done => cases location
  | active heap frame oldStack =>
    cases frame with
    | invalid => cases location
    | fn_gcd pc s =>
      have counter : pc = 4 := by
        unfold gcd.At.loop at location
        split at location <;> simp_all
      subst pc
      simp [gcd.Local.a, gcd.Local.b] at readA readB
      have next := continuation
        (.active heap (.fn_gcd 4
          { s with
            t4 := decide (s.v1 ≠ 0)
            v2 := Int.fmod s.v0 s.v1
            v0 := s.v1
            v1 := Int.fmod s.v0 s.v1 }) oldStack)
        True.intro (by simp [gcd.Local.a, readB])
        (by simp [gcd.Local.b, readA, readB, Int.fmod_eq_emod_of_nonneg a (by omega : 0 ≤ b)])
      intro stack
      apply Reaches.trans (Reaches.single (Step.gcd_pc4 ..))
      apply Reaches.trans (Reaches.single (Step.gcd_pc3_true _ _ _ (by simp; omega)))
      apply Reaches.trans (Reaches.single (Step.gcd_pc7 _ _ _ (by dsimp; omega)))
      apply Reaches.trans (Reaches.single (Step.gcd_pc6 ..))
      apply Reaches.trans (Reaches.single (Step.gcd_pc5 ..))
      exact next stack

/-- Normalize the second argument before entering the Euclidean loop. -/
theorem normalize_second (a b output : Int)
    (continuation : ∀ next, gcd.At.loop next →
      gcd.Local.a next = some a → gcd.Local.b next = some (b.natAbs : Int) →
      gcd.CallFrom next next.heap output)
    (state : Configuration) (location : gcd.At.normalize_b state)
    (readA : gcd.Local.a state = some a)
    (readB : gcd.Local.b state = some b) :
    gcd.CallFrom state state.heap output := by
  cases state with
  | done => cases location
  | active heap frame oldStack =>
    cases frame with
    | invalid => cases location
    | fn_gcd pc s =>
      have counter : pc = 10 := by
        unfold gcd.At.normalize_b at location
        split at location <;> simp_all
      subst pc
      simp [gcd.Local.a, gcd.Local.b] at readA readB
      intro stack
      apply Reaches.trans (Reaches.single (Step.gcd_pc10 ..))
      by_cases negative : b < 0
      · apply Reaches.trans (Reaches.single (Step.gcd_pc9_true _ _ _ (by simp; omega)))
        apply Reaches.trans (Reaches.single (Step.gcd_pc8 ..))
        exact continuation
          (.active heap (.fn_gcd 4 { s with t5 := decide (s.v1 < 0), v1 := -s.v1 }) [])
          True.intro (by simp [gcd.Local.a, readA])
          (by simp [gcd.Local.b, readB, absolute_value, negative]) stack
      · apply Reaches.trans (Reaches.single (Step.gcd_pc9_false _ _ _ (by simp; omega)))
        exact continuation
          (.active heap (.fn_gcd 4 { s with t5 := decide (s.v1 < 0) }) [])
          True.intro (by simp [gcd.Local.a, readA])
          (by simp [gcd.Local.b, readB, absolute_value, negative]) stack

/-- Normalize both signs. The continuation only needs to handle nonnegative
    source arguments at the named loop test. -/
theorem normalize_signs (heap : Heap) (a b output : Int)
    (continuation : ∀ state, gcd.At.loop state →
      gcd.Local.a state = some (a.natAbs : Int) →
      gcd.Local.b state = some (b.natAbs : Int) →
      gcd.CallFrom state state.heap output) :
    gcd.Call heap (a, b) heap output := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.gcd_pc13 ..))
  by_cases negative : a < 0
  · apply Reaches.trans (Reaches.single (Step.gcd_pc12_true _ _ _ (by simpa)))
    apply Reaches.trans (Reaches.single (Step.gcd_pc11 ..))
    exact normalize_second (a.natAbs : Int) b output continuation
      (.active heap (.fn_gcd 10 { v0 := -a, v1 := b, t6 := decide (a < 0) }) [])
      True.intro (by simp [gcd.Local.a, absolute_value, negative])
      (by simp [gcd.Local.b]) stack
  · apply Reaches.trans (Reaches.single (Step.gcd_pc12_false _ _ _ (by simp; omega)))
    exact normalize_second (a.natAbs : Int) b output continuation
      (.active heap (.fn_gcd 10 { v0 := a, v1 := b, t6 := decide (a < 0) }) [])
      True.intro (by simp [gcd.Local.a, absolute_value, negative])
      (by simp [gcd.Local.b]) stack

/-- Well-founded Euclidean induction: the nonnegative second argument strictly
    decreases at every nonterminal loop test. No transition details occur here. -/
theorem loop_summary (a b : Int) (nonnegativeA : 0 ≤ a) (nonnegativeB : 0 ≤ b)
    (state : Configuration) (location : gcd.At.loop state)
    (readA : gcd.Local.a state = some a) (readB : gcd.Local.b state = some b) :
    gcd.CallFrom state state.heap (Int.gcd a b : Int) := by
  generalize measure : b.toNat = count
  induction count using Nat.strongRecOn generalizing a b state with
  | ind count inductionHypothesis =>
    by_cases finished : b = 0
    · subst b
      simpa [Int.natAbs_of_nonneg nonnegativeA] using loop_zero state a location readA readB
    · have positive : 0 < b := by omega
      have remainderNonnegative := Int.emod_nonneg a finished
      have remainderSmaller := Int.emod_lt_of_pos a positive
      have decreases : (a % b).toNat < count := by omega
      apply loop_reduce a b (Int.gcd a b : Int) positive
      · intro next nextLocation nextA nextB
        have reduced := inductionHypothesis (a % b).toNat decreases
          b (a % b) (by omega) remainderNonnegative next nextLocation nextA nextB rfl
        simpa [gcd_reduction] using reduced
      · exact location
      · exact readA
      · exact readB

/-- Every signed pair terminates with the nonnegative mathematical GCD, preserving
    the heap and valid under every caller stack. -/
theorem summary (heap : Heap) (a b : Int) :
    gcd.Call heap (a, b) heap (Int.gcd a b : Int) := by
  apply normalize_signs heap a b (Int.gcd a b : Int)
  intro state location readA readB
  have normalized := loop_summary (a.natAbs : Int) (b.natAbs : Int)
    (by omega) (by omega) state location readA readB
  simpa [Int.gcd] using normalized

/-- In particular, every signed input has the correct ordinary-value output. -/
theorem output (a b : Int) : gcd.Returns (a, b) (Int.gcd a b : Int) := by
  have specification := summary {} a b
  exact ⟨{}, specification.1, specification.2.root⟩

/-- Each configuration permits at most one next configuration. This local
    transition fact is independent of termination or any particular input. -/
theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

/-- Any completed execution has the mathematical result and preserves the heap. -/
theorem execution_correct (heap finalHeap : Heap) (a b result : Int)
    (execution : gcd.Run heap (a, b) finalHeap result) :
    finalHeap = heap ∧ result = (Int.gcd a b : Int) := by
  have correctRun := (summary heap a b).2.root
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic execution.2 correctRun
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

-- Main result: Correctness
/-- Exact total correctness for every signed input, including gcd(0,0)=0. -/
theorem output_iff (a b result : Int) :
    gcd.Returns (a, b) result ↔ result = (Int.gcd a b : Int) := by
  constructor
  · rintro ⟨heap, execution⟩
    exact (execution_correct {} heap a b result execution).2
  · intro correct
    subst result
    exact output a b

/-- The two zero-argument base cases follow from the general result. -/
theorem right_zero (a : Int) : gcd.Returns (a, 0) (a.natAbs : Int) := by
  simpa using output a 0

theorem left_zero (b : Int) : gcd.Returns (0, b) (b.natAbs : Int) := by
  simpa using output 0 b

end GcdAnalysis
