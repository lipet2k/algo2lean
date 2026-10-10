import WeightedTicksGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `triangular_formula`: Closed form of weighted work.
- `weighted_tick`: Local weighted tick effect.
- `summary`: Reusable call contract.
- `output_with_cost_iff`: Output and exact weighted costs.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace WeightedTicksAnalysis

/-- The work of iterations 0, ..., n-1. -/
def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + n

/-- A closed form for the weighted work count, without truncated division. -/
theorem triangular_formula (n : Nat) :
    2 * triangular n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [triangular, Nat.mul_add, Nat.mul_succ, Nat.succ_mul,
        Nat.add_sub_cancel] at ih ⊢
      omega

/-- Cost specifications name only the counters this algorithm changes. -/
def remainingCosts (first count : Nat) : Clocks :=
  Clocks.add (Clocks.single "work" (first * count + triangular count))
    (Clocks.single "iterations" count)

def costs (n : Int) : Clocks := remainingCosts 0 n.toNat

@[simp] theorem remainingCosts_zero (first : Nat) :
    remainingCosts first 0 = fun _ => 0 := by
  funext name
  simp [remainingCosts, Clocks.add, Clocks.single, triangular]

/-- The mathematical recurrence is independent of heaps and transition rules. -/
theorem remainingCosts_step (first count : Nat) :
    Clocks.add (Clocks.single "work" first)
      (Clocks.add (Clocks.single "iterations" 1) (remainingCosts (first + 1) count)) =
      remainingCosts first (count + 1) := by
  funext name
  by_cases work : name = "work" <;> by_cases iterations : name = "iterations" <;>
    simp_all [remainingCosts, Clocks.add, Clocks.single, triangular,
      Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- A single charge reads a local variable and increases only the selected
    clock. Its statement does not mention a transcript or an initial state. -/
theorem weighted_tick {before after : Configuration} (value : Int)
    (transition : Step before after) (location : triangular_work.At.charge before)
    (readValue : triangular_work.Local.i before = some value) :
    0 ≤ value ∧ clock after "work" = clock before "work" + value.toNat ∧
      clock after "iterations" = clock before "iterations" := by
  cases transition <;>
    simp_all [triangular_work.At.charge, triangular_work.Local.i, clock, Config.heap]

/-- Starting at iteration `first`, the remaining `count` iterations charge
    `first * count + triangular count` work and exactly `count` iterations.
    This local helper applies with any heap and any suspended caller stack. -/
theorem remaining_summary (count first : Nat) (state : Configuration)
    (location : triangular_work.At.loop state)
    (readFirst : triangular_work.Local.i state = some (first : Int))
    (readBound : triangular_work.Local.n state = some ((first + count : Nat) : Int)) :
    triangular_work.CallFrom state
      (state.heap.charge (remainingCosts first count))
      ((first + count : Nat) : Int) := by
  induction count generalizing state first with
  | zero =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_triangular_work pc s =>
        have counter : pc = 4 := by
          unfold triangular_work.At.loop at location
          split at location <;> simp_all
        subst pc
        simp [triangular_work.Local.i, triangular_work.Local.n] at readFirst readBound
        intro stack
        apply Reaches.prepend (Step.triangular_work_pc4 _ _ _)
        apply Reaches.prepend (Step.triangular_work_pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega))
        apply Reaches.prepend (Step.triangular_work_pc2 _ _ _)
        simpa [readFirst, Config.heap] using
          Reaches.single (Step.triangular_work_pc1 heap _ stack)
  | succ count inductionHypothesis =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_triangular_work pc s =>
        have counter : pc = 4 := by
          unfold triangular_work.At.loop at location
          split at location <;> simp_all
        subst pc
        simp [triangular_work.Local.i, triangular_work.Local.n] at readFirst readBound
        have nonnegative : 0 ≤ s.v1 := by omega
        have next := inductionHypothesis (first + 1)
          (.active ((heap.tick "work" s.v1.toNat).tick "iterations")
            (.fn_triangular_work 4 { s with t3 := decide (s.v1 < s.v0), v1 := s.v1 + 1 })
            originalStack) True.intro
          (by simp [triangular_work.Local.i, readFirst])
          (by simp [triangular_work.Local.n]; omega)
        intro stack
        apply Reaches.prepend (Step.triangular_work_pc4 _ _ _)
        apply Reaches.prepend (Step.triangular_work_pc3_true _ _ _
          (by simp only [decide_eq_true_eq]; omega))
        apply Reaches.prepend (Step.triangular_work_pc7 _ _ _ (by exact nonnegative))
        apply Reaches.prepend (Step.triangular_work_pc6 _ _ _)
        apply Reaches.prepend (Step.triangular_work_pc5 _ _ _)
        simpa only [Config.heap, Heap.tick_charge, readFirst, Int.toNat_natCast,
          remainingCosts_step, Nat.add_assoc, Nat.add_comm 1 count] using next stack

/-- The whole algorithm terminates for every natural bound. -/
theorem natural_summary (heap : Heap) (n : Nat) :
    triangular_work.Call heap (n : Int)
      (heap.charge (remainingCosts 0 n)) (n : Int) := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.triangular_work_pc8 _ _ _)
  have loop := remaining_summary n 0
    (.active heap (.fn_triangular_work 4 { v0 := n }) stack)
    True.intro rfl (by simp [triangular_work.Local.n])
  simpa [Config.heap] using loop stack

/-- Nonpositive bounds skip the body and do not charge either clock. -/
theorem nonpositive_summary (heap : Heap) (n : Int) (nonpositive : n ≤ 0) :
    triangular_work.Call heap n heap 0 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.triangular_work_pc8 _ _ _)
  apply Reaches.prepend (Step.triangular_work_pc4 _ _ _)
  apply Reaches.prepend (Step.triangular_work_pc3_false _ _ _
    (by simp only [decide_eq_false_iff_not]; omega))
  apply Reaches.prepend (Step.triangular_work_pc2 _ _ _)
  exact Reaches.single (Step.triangular_work_pc1 _ _ _)

/-- A reusable summary includes nonzero initial clocks and arbitrary callers. -/
theorem summary (heap : Heap) (n : Int) :
    triangular_work.Call heap n
      (heap.charge (costs n)) (n.toNat : Int) := by
  by_cases nonpositive : n ≤ 0
  · simpa [costs, Int.toNat_eq_zero.mpr nonpositive] using
      nonpositive_summary heap n nonpositive
  · simpa [costs, Int.toNat_of_nonneg (by omega : 0 ≤ n)] using natural_summary heap n.toNat

/-- The output and exact weighted costs belong to the same terminating run. -/
theorem output_with_cost (n : Int) :
    triangular_work.ReturnsWithCost n (n.toNat : Int) (costs n) := by
  have call := summary {} n
  exact ⟨_, triangular_work.Call.run call, Heap.cost_charge {} (costs n)⟩

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

/-- Every completed execution has the heap effect described by the summary. -/
theorem execution_correct (heap finalHeap : Heap) (n result : Int)
    (execution : triangular_work.Run heap n finalHeap result) :
    finalHeap = heap.charge (costs n) ∧
      result = (n.toNat : Int) := by
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
    execution.2 (summary heap n).2.root
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

-- Main result: Correctness and running time
/-- Complete characterization, rather than merely constructing one output. -/
theorem output_with_cost_iff (n result : Int) (charged : Clocks) :
    triangular_work.ReturnsWithCost n result charged ↔
      result = (n.toNat : Int) ∧ charged = costs n := by
  constructor
  · rintro ⟨heap, execution, cost⟩
    obtain ⟨heapEffect, resultEffect⟩ := execution_correct {} heap n result execution
    refine ⟨resultEffect, ?_⟩
    simpa [heapEffect, triangular_work.load] using cost.symm
  · rintro ⟨rfl, rfl⟩
    exact output_with_cost n

end WeightedTicksAnalysis
