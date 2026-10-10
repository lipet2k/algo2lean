import HeapHeightGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable ancestor-count contract.
- `output_with_cost_iff`: Exact result and logarithmic cost.
- `runtime_bounded`: Running time bounded by heap size.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace HeapHeightAnalysis

/-- Depth of an array position in a complete, zero-based binary tree. -/
def depth (index : Nat) : Nat := Nat.log2 (index + 1)

@[simp] theorem depth_root : depth 0 = 0 := rfl

/-- Taking a parent removes exactly one level. -/
theorem depth_parent (index : Nat) :
    depth (index + 1) = depth (index / 2) + 1 := by
  unfold depth
  rw [Nat.log2_def (index + 1 + 1), if_pos (by omega)]
  congr 2
  omega

/-- The source uses Python floor division; the divisor here is positive, so
    the parent of position index+1 is the natural quotient index/2. -/
theorem parent_index (index : Nat) :
    Int.fdiv (((index + 1 : Nat) : Int) - 1) 2 = ((index / 2 : Nat) : Int) := by
  simp [Int.fdiv_eq_ediv, Int.natCast_ediv]

/-- Clock costs are a mathematical specification, separate from heap layout. -/
def depthCosts (index : Nat) : Clocks := Clocks.single "levels" (depth index)

@[simp] theorem depthCosts_root : depthCosts 0 = fun _ => 0 := by
  funext name
  simp [depthCosts, Clocks.single]

theorem depthCosts_parent (index : Nat) :
    Clocks.add (Clocks.single "levels" 1) (depthCosts (index / 2)) =
      depthCosts (index + 1) := by
  funext name
  by_cases same : name = "levels" <;>
    simp [Clocks.add, Clocks.single, depthCosts, depth_parent, Nat.add_comm, same]

/-- A local loop state finishes after exactly depth(index) additional parent
    links. Existing levels, heap data, counters, and caller stack are arbitrary. -/
theorem remaining_summary (index : Nat) (levels : Int) (state : Configuration)
    (location : heap_ancestors.At.loop state)
    (readIndex : heap_ancestors.Local.index state = some (index : Int))
    (readLevels : heap_ancestors.Local.levels state = some levels) :
    heap_ancestors.CallFrom state (state.heap.charge (depthCosts index))
      (levels + (depth index : Int)) := by
  induction index using Nat.strongRecOn generalizing state levels with
  | ind index inductionHypothesis =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_heap_ancestors pc s =>
        have counter : pc = 4 := by
          unfold heap_ancestors.At.loop at location
          split at location <;> simp_all
        subst pc
        simp [heap_ancestors.Local.index, heap_ancestors.Local.levels] at readIndex readLevels
        cases index with
        | zero =>
          intro stack
          apply Reaches.prepend (Step.heap_ancestors_pc4 _ _ _)
          apply Reaches.prepend (Step.heap_ancestors_pc3_false _ _ _
            (by simp only [decide_eq_false_iff_not]; omega))
          apply Reaches.prepend (Step.heap_ancestors_pc2 _ _ _)
          simpa [readLevels, Config.heap] using Reaches.single (Step.heap_ancestors_pc1 heap _ stack)
        | succ index =>
          have next := inductionHypothesis (index / 2) (by omega) (levels + 1)
            (.active (heap.tick "levels") (.fn_heap_ancestors 4
              { s with t3 := decide (s.v0 > 0), v0 := Int.fdiv (s.v0 - 1) 2, v1 := s.v1 + 1 }) originalStack)
            True.intro
            (by change some (Int.fdiv (s.v0 - 1) 2) = some ((index / 2 : Nat) : Int)
                rw [readIndex, parent_index])
            (by simp [heap_ancestors.Local.levels, readLevels])
          intro stack
          apply Reaches.prepend (Step.heap_ancestors_pc4 _ _ _)
          apply Reaches.prepend (Step.heap_ancestors_pc3_true _ _ _
            (by simp only [decide_eq_true_eq]; omega))
          apply Reaches.prepend (Step.heap_ancestors_pc7 _ _ _)
          apply Reaches.prepend (Step.heap_ancestors_pc6 _ _ _ (by decide))
          apply Reaches.prepend (Step.heap_ancestors_pc5 _ _ _)
          simpa [Config.heap, Heap.tick_charge, depthCosts_parent, depth_parent,
            Int.add_assoc, Int.add_comm, Int.add_left_comm] using next stack

/-- A reusable summary for every valid binary-tree index. -/
theorem natural_summary (heap : Heap) (index : Nat) :
    heap_ancestors.Call heap (index : Int) (heap.charge (depthCosts index))
      (depth index : Int) := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.heap_ancestors_pc8 _ _ _)
  have loop := remaining_summary index 0
    (.active heap (.fn_heap_ancestors 4 { v0 := index }) stack) True.intro rfl rfl
  simpa [Config.heap] using loop stack

/-- Nonpositive input skips traversal and incurs no cost. -/
theorem nonpositive_summary (heap : Heap) (index : Int) (nonpositive : index ≤ 0) :
    heap_ancestors.Call heap index heap 0 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.heap_ancestors_pc8 _ _ _)
  apply Reaches.prepend (Step.heap_ancestors_pc4 _ _ _)
  apply Reaches.prepend (Step.heap_ancestors_pc3_false _ _ _
    (by simp only [decide_eq_false_iff_not]; omega))
  apply Reaches.prepend (Step.heap_ancestors_pc2 _ _ _)
  exact Reaches.single (Step.heap_ancestors_pc1 _ _ _)

theorem summary (heap : Heap) (index : Int) :
    heap_ancestors.Call heap index (heap.charge (depthCosts index.toNat))
      (depth index.toNat : Int) := by
  by_cases nonpositive : index ≤ 0
  · simpa [Int.toNat_eq_zero.mpr nonpositive] using nonpositive_summary heap index nonpositive
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ index)] using natural_summary heap index.toNat

/-- Termination and exact logarithmic runtime belong to the same execution. -/
theorem output_with_cost (index : Int) :
    heap_ancestors.ReturnsWithCost index (Nat.log2 (index.toNat + 1) : Int)
      (Clocks.single "levels" (Nat.log2 (index.toNat + 1))) := by
  have run := summary {} index
  exact ⟨_, ⟨run.1, run.2.root⟩, Heap.cost_charge {} (depthCosts index.toNat)⟩

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

theorem execution_correct (heap finalHeap : Heap) (index result : Int)
    (execution : heap_ancestors.Run heap index finalHeap result) :
    finalHeap = heap.charge (depthCosts index.toNat) ∧ result = (depth index.toNat : Int) := by
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
    execution.2 (summary heap index).2.root
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

-- Main result: Correctness and running time
/-- Complete characterization of both the result and every named counter. -/
theorem output_with_cost_iff (index result : Int) (charged : Clocks) :
    heap_ancestors.ReturnsWithCost index result charged ↔
      result = (Nat.log2 (index.toNat + 1) : Int) ∧
      charged = Clocks.single "levels" (Nat.log2 (index.toNat + 1)) := by
  constructor
  · rintro ⟨heap, execution, cost⟩
    obtain ⟨heapEffect, resultEffect⟩ := execution_correct {} heap index result execution
    refine ⟨resultEffect, ?_⟩
    simpa [heapEffect, heap_ancestors.load] using! cost.symm
  · rintro ⟨rfl, rfl⟩
    exact output_with_cost index

/-- The conventional depth interval. This is a theorem about parent traversal,
    not yet a correctness or runtime theorem for an entire priority queue. -/
theorem depth_interval (index : Nat) :
    2 ^ depth index ≤ index + 1 ∧ index + 1 < 2 ^ (depth index + 1) :=
  (Nat.log2_eq_iff (by omega : index + 1 ≠ 0)).mp rfl

/-- Every position in an array of size `size` has at most log2(size) parents. -/
theorem depth_bounded (index size : Nat) (within : index < size) :
    depth index ≤ Nat.log2 size := by
  apply (Nat.le_log2 (by omega : size ≠ 0)).mpr
  exact Nat.le_trans (depth_interval index).1 (by omega)

theorem runtime_bounded (index size : Nat) (within : index < size)
    (result : Int) (charged : Clocks)
    (execution : heap_ancestors.ReturnsWithCost (index : Int) result charged) :
    charged "levels" ≤ Nat.log2 size := by
  obtain ⟨_, correctCost⟩ := (output_with_cost_iff (index : Int) result charged).mp execution
  simpa [correctCost, Clocks.single, depth] using depth_bounded index size within

end HeapHeightAnalysis
