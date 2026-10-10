-- Bound-method lookup captures the old receiver before the argument switches it.
-- The method itself sees the argument's mutation from 3 to 50, then adds 7.
example : bound_receiver.Returns () 5704 := by
  unfold bound_receiver.Returns
  algo_steps

-- Ordinary assignment resolves its target after the RHS changes holder.current.
example : ordinary_assignment.Returns () 5007 := by
  unfold ordinary_assignment.Returns
  algo_steps

-- Augmented assignment retains both the original receiver and its old value 3.
example : augmented_assignment.Returns () 1004 := by
  unfold augmented_assignment.Returns
  algo_steps

-- Constructor arguments finish before the outer object's allocation. Therefore
-- the argument's Box has reference 0 and the returned Box has reference 1.
example : constructor_order.Returns ()
    (create_Box (create_Box ({} : Heap) 99).1 5) := by
  unfold constructor_order.Returns
  algo_steps

-- Allocation/copying in the sequence arena cannot erase the object arena.
example : sequence_field.Returns () 851 := by
  unfold sequence_field.Returns
  algo_steps
