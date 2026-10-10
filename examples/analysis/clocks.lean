import ClocksGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `counted_summary`: Reusable call contract.
- `output_with_cost`: Termination with exact clock costs.
- `output_with_cost_iff`: Output and running time characterization.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace ClocksAnalysis

-- Clock observations are local to the supplied configurations. No transcript
-- or function-entry hypothesis is needed to describe one tick's effect.
theorem work_tick {before after : Configuration}
    (transition : Step before after) (location : advance.At.charge before) :
    clock after "work" = clock before "work" + 1 := by
  cases transition <;> simp_all [advance.At.charge, clock, Config.heap]

-- The method of counting is explicit: one work tick per call. The theorem
-- works with any existing counters and under any suspended caller stack.
theorem advance_summary (heap : Heap) (value : Int) :
    advance.Call heap value (heap.tick "work") (value + 1) := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.advance_pc3 _ _ _)
  apply Reaches.prepend (Step.advance_pc2 _ _ _)
  exact Reaches.single (Step.advance_pc1 _ _ _)

-- This local loop theorem observes only a supplied configuration. It does not
-- require that entry reached the loop or that a whole transcript was built.
theorem remaining_summary (count : Nat) (state : Configuration) (value : Int)
    (location : counted_loop.At.loop state)
    (readValue : counted_loop.Local.value state = some value)
    (readBound : counted_loop.Local.n state = some (value + (count : Int))) :
    counted_loop.CallFrom state (state.heap.tick "work" count)
      (value + (count : Int)) := by
  induction count generalizing state value with
  | zero =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_advance => cases location
      | fn_counted_loop pc s =>
        have counter : pc = 4 := by
          unfold counted_loop.At.loop at location
          split at location <;> simp_all
        subst pc
        simp [counted_loop.Local.value, counted_loop.Local.n] at readValue readBound
        intro stack
        apply Reaches.prepend (Step.counted_loop_pc4 _ _ _)
        apply Reaches.prepend (Step.counted_loop_pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega))
        apply Reaches.prepend (Step.counted_loop_pc2 _ _ _)
        simpa [readValue, Config.heap] using Reaches.single (Step.counted_loop_pc1 heap _ stack)
  | succ count inductionHypothesis =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_advance => cases location
      | fn_counted_loop pc s =>
        have counter : pc = 4 := by
          unfold counted_loop.At.loop at location
          split at location <;> simp_all
        subst pc
        simp [counted_loop.Local.value, counted_loop.Local.n] at readValue readBound
        have next := inductionHypothesis
          (.active (heap.tick "work") (.fn_counted_loop 4
            { s with t3 := decide (s.v1 < s.v0), t5 := s.v1, t4 := s.v1 + 1, v1 := s.v1 + 1 }) originalStack)
          (value + 1) True.intro
          (by simp [counted_loop.Local.value, readValue])
          (by simp [counted_loop.Local.n]; omega)
        intro stack
        apply Reaches.prepend (Step.counted_loop_pc4 _ _ _)
        apply Reaches.prepend (Step.counted_loop_pc3_true _ _ _
          (by simp only [decide_eq_true_eq]; omega))
        apply Reaches.prepend (Step.counted_loop_pc7 _ _ _)
        apply Reaches.prepend (Step.counted_loop_pc6 _ _ _)
        apply Reaches.trans ((advance_summary heap s.v1).2 _)
        apply Reaches.prepend (Step.counted_loop_pc5 _ _ _)
        simpa [Config.heap, Heap.tick_add, Nat.add_comm, Int.add_assoc,
          Int.add_left_comm, Int.add_comm] using next stack

theorem natural_summary (heap : Heap) (n : Nat) :
    counted_loop.Call heap (n : Int)
      ((heap.tick "calls").tick "work" n) (n : Int) := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.counted_loop_pc9 _ _ _)
  apply Reaches.prepend (Step.counted_loop_pc8 _ _ _)
  have loop := remaining_summary n
    (.active (heap.tick "calls") (.fn_counted_loop 4 { v0 := n }) stack) 0
    True.intro rfl (by simp [counted_loop.Local.n])
  simpa [Config.heap] using loop stack

theorem nonpositive_summary (heap : Heap) (n : Int) (nonpositive : n ≤ 0) :
    counted_loop.Call heap n (heap.tick "calls") 0 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.counted_loop_pc9 _ _ _)
  apply Reaches.prepend (Step.counted_loop_pc8 _ _ _)
  apply Reaches.prepend (Step.counted_loop_pc4 _ _ _)
  apply Reaches.prepend (Step.counted_loop_pc3_false _ _ _
    (by simp only [decide_eq_false_iff_not]; omega))
  apply Reaches.prepend (Step.counted_loop_pc2 _ _ _)
  exact Reaches.single (Step.counted_loop_pc1 _ _ _)

theorem counted_summary (heap : Heap) (n : Int) :
    counted_loop.Call heap n
      ((heap.tick "calls").tick "work" n.toNat) (n.toNat : Int) := by
  by_cases nonpositive : n ≤ 0
  · simpa [Int.toNat_eq_zero.mpr nonpositive] using nonpositive_summary heap n nonpositive
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ n)] using natural_summary heap n.toNat

-- All named counters are described, including those untouched by this source.
def countedCosts (n : Int) : Clocks :=
  fun name => if name = "calls" then 1 else if name = "work" then n.toNat else 0

theorem counted_costs (heap : Heap) (n : Int) :
    Heap.cost heap ((heap.tick "calls").tick "work" n.toNat) = countedCosts n := by
  funext name
  by_cases calls : name = "calls"
  · subst name
    simp [Heap.cost, Heap.tick, countedCosts]
  · by_cases work : name = "work"
    · subst name
      simp [Heap.cost, Heap.tick, countedCosts]
    · simp [Heap.cost, Heap.tick, countedCosts, calls, work]

-- The output and the two exact costs belong to the same completed execution.
theorem output_with_cost (n : Int) :
    counted_loop.ReturnsWithCost n (n.toNat : Int) (countedCosts n) := by
  have summary := counted_summary ({} : Heap) n
  exact ⟨_, ⟨summary.1, summary.2.root⟩, counted_costs {} n⟩

theorem output (n : Int) : counted_loop.Returns n (n.toNat : Int) :=
  (output_with_cost n).returns

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

-- Determinism identifies the result and clock increments of every completed execution,
-- including those starting from nonzero counters in an arbitrary caller heap.
theorem execution_correct (heap finalHeap : Heap) (n result : Int)
    (execution : counted_loop.Run heap n finalHeap result) :
    finalHeap = (heap.tick "calls").tick "work" n.toNat ∧ result = (n.toNat : Int) := by
  have correctRun := (counted_summary heap n).2.root
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
    execution.2 correctRun
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

-- Main result: Correctness and running time
theorem output_with_cost_iff (n result : Int) (costs : Clocks) :
    counted_loop.ReturnsWithCost n result costs ↔
      result = (n.toNat : Int) ∧ costs = countedCosts n := by
  constructor
  · rintro ⟨heap, execution, cost⟩
    obtain ⟨heapEffect, resultEffect⟩ := execution_correct {} heap n result execution
    refine ⟨resultEffect, ?_⟩
    rw [heapEffect] at cost
    exact cost.symm.trans (counted_costs {} n)
  · rintro ⟨rfl, rfl⟩
    exact output_with_cost n

end ClocksAnalysis
