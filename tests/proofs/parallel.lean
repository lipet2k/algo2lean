import ParallelSemanticsGenerated

open Algo2LeanGenerated Algo2LeanParallel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

-- These examples build actual generated executions. Work and span are inferred
-- from the execution constructors before their concrete values are checked.
syntax "fork_steps" : tactic
macro_rules
  | `(tactic| fork_steps) => `(tactic| first
    | exact Eval.ret (by rfl)
    | (apply Eval.step (by rfl); fork_steps)
    | (apply Eval.call (by rfl) <;> fork_steps)
    | (apply Eval.fork (by rfl) <;> fork_steps)
    | exact Access.empty_compatible _ rfl
    | (constructor <;> simp_all [Access.union, Access.empty, Access.readSeq, Access.writeSeq,
        Access.read, Access.write, Heap.read]))

theorem paired_cost : ∃ cost access, paired.ParallelCall {} 4 {} (5, true) cost access ∧
    cost.work = 12 ∧ cost.span = 10 := by
  exact ⟨_, _, ⟨True.intro, by fork_steps⟩, rfl, rfl⟩

theorem shared_read : ∃ cost access,
    pair_read.ParallelCall { nextRef := 1 } (0, -2, -2)
      { nextRef := 1 } (0, 0) cost access := by
  unfold pair_read.ParallelCall pair_read.ValidInput
  exact ⟨_, _, by decide, by fork_steps⟩

theorem disjoint_write : ∃ cost access,
    pair_write.ParallelCall { nextRef := 1 } (0, -2, 4)
      (({ nextRef := 1 } : Heap).write 0 (-2) 1 |>.write 0 4 2) (1, 2) cost access := by
  unfold pair_write.ParallelCall pair_write.ValidInput
  exact ⟨_, _, by decide, by fork_steps⟩

-- The right child index is read before the left child writes a[0].
-- That parent read is not a conflicting sibling read; the child reads a[1].
theorem arguments_before_children : ∃ cost access,
    captured_arguments.ParallelCall
      { nextRef := 1, store := fun _ i => i + 1 } 0
      (({ nextRef := 1, store := fun _ i => i + 1 } : Heap).write 0 0 9)
      (9, 2) cost access := by
  unfold captured_arguments.ParallelCall captured_arguments.ValidInput
  exact ⟨_, _, by decide, by fork_steps⟩

-- A valid parallel execution also supplies the established source Call API.
example (before : Heap) (input : Int) (after : Heap) (output : Int × Bool)
    (cost : Cost) (access : Access)
    (run : paired.ParallelCall before input after output cost access) :
    paired.Call before input after output := run.call

-- The access rules rule out true aliases and allocation even when cells have
-- different source-level variable names or a write preserves the old value.
example (alias : Nat) (index : Int) :
    ¬ Access.Compatible (Access.writeSeq alias index) (Access.readSeq alias index) :=
  Access.not_write_read alias index

example (alias : Nat) (index : Int) :
    ¬ Access.Compatible (Access.writeSeq alias index) (Access.writeSeq alias index) :=
  Access.not_write_write alias index

example (other : Access) : ¬ Access.Compatible Access.allocation other :=
  Access.not_allocation other

#print axioms paired_cost
#print axioms shared_read
#print axioms disjoint_write
#print axioms paired.ParallelCall.call
#print axioms Access.not_write_read
#print axioms Access.not_write_write
#print axioms Access.not_allocation

#print axioms arguments_before_children
