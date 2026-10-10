-- Concrete outputs follow from valid transcripts of heap-threaded steps.
example : aliases.Returns () 91 := by
  unfold aliases.Returns
  algo_steps

example : rebound.Returns () 2 := by
  unfold rebound.Returns
  algo_steps

example : independent_copy.Returns () 7 := by
  unfold independent_copy.Returns
  algo_steps

example : fresh_constants.Returns () 7 := by
  unfold fresh_constants.Returns
  algo_steps

example : copy_current_contents.Returns () 8 := by
  unfold copy_current_contents.Returns
  algo_steps

example : mutating_call.Returns () 42 := by
  unfold mutating_call.Returns
  algo_steps

-- The first read sees the old contents; the read after the call sees mutation.
example : read_call_read.Returns () 5 := by
  algo_steps

example : updating_returns_same_object.Returns () 19 := by
  unfold updating_returns_same_object.Returns
  algo_steps

-- Bounds mutate the same object from left to right, once each. The body then
-- observes the final bound effect and makes three additional mutations.
example : range_args.Returns () 93162 := by
  unfold range_args.Returns
  algo_steps

example : descending_range.Returns () 8 := by
  unfold descending_range.Returns
  algo_steps

example : empty_range.Returns () 9 := by
  unfold empty_range.Returns
  algo_steps

example : range_stop.Returns 4 6 := by
  unfold range_stop.Returns
  algo_steps

example : range_stop.Returns (-3) 0 := by
  unfold range_stop.Returns
  algo_steps

example : range_start_stop.Returns (-3, 0) (-6) := by
  unfold range_start_stop.Returns
  algo_steps

example : range_signed.Returns (0, 3, -1) 0 := by
  unfold range_signed.Returns
  algo_steps

example : range_signed.Returns (3, 0, 1) 0 := by
  unfold range_signed.Returns
  algo_steps

example : range_signed.Returns (5, 5, -1) 0 := by
  unfold range_signed.Returns
  algo_steps

example : range_signed.Returns
    (1000000000000000000000000000000, 1000000000000000000000000000002, 1)
    2000000000000000000000000000001 := by
  unfold range_signed.Returns
  algo_steps

example : range_body_rebinds.Returns () 3 := by
  unfold range_body_rebinds.Returns
  algo_steps

example : range_uses_old_binding.Returns () 94 := by
  unfold range_uses_old_binding.Returns
  algo_steps

-- Ordinary assignment evaluates its RHS before the index.
example : assignment_order.Returns () 2 := by
  unfold assignment_order.Returns
  algo_steps

def sharedHeap : Heap := ({} : Heap).allocate (fun _ => 3)

-- Both parameters are explicitly the same object in the stateful interface.
example : aliased_params.Run sharedHeap (0, 0)
    (sharedHeap.write 0 0 11) 11 := by
  unfold aliased_params.Run
  algo_steps

-- The value-view adapter deliberately loads separate input objects.
example : aliased_params.Returns ((fun _ => 3), (fun _ => 3)) 3 := by
  unfold aliased_params.Returns
  algo_steps

-- Assignment reads the right-hand side before evaluating the mutating index call.
-- The stored right-hand side retains value 1; the index call's write of 2 at
-- index 0 also remains visible.
example : assignment_index_mutates.Returns () 21 := by
  unfold assignment_index_mutates.Returns
  algo_steps
