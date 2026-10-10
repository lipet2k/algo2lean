-- Even a finite prefix cannot execute the side-effecting argument: Python
-- resolves the method on its receiver before it evaluates the arguments.
private def nullCallRegion (initialHeap : Heap) (state : Configuration) : Prop :=
  state.heap = initialHeap ∧ match state with
    | .active _ (.fn_null_call pc s) _ =>
      (pc = 8 ∨ pc = 7 ∨ pc = 6) ∧ s.v1 = none ∧ s.t4 = none
    | _ => False

private theorem nullCallRegion_preserved (heap : Heap) (before after : Configuration)
    (transition : Step before after) (inside : nullCallRegion heap before) :
    nullCallRegion heap after := by
  cases transition <;> simp_all [nullCallRegion, Algo2LeanCore.Config.heap]

theorem null_call_never_mutates (heap : Heap) (cell : Ref_Cell) (trace : Transcript)
    (execution : null_call.ValidHeapTranscript heap cell trace) :
    ∀ state ∈ trace, state.heap = heap := by
  obtain ⟨_, final, run⟩ := execution
  have inside := run.all_states (nullCallRegion heap)
    (by simp [nullCallRegion, null_call.initial, Algo2LeanCore.start, Algo2LeanCore.Config.heap])
    (nullCallRegion_preserved heap)
  intro state member
  exact (inside state member).1

theorem null_call_has_no_output (heap : Heap) (cell : Ref_Cell) :
    ¬ null_call.Returns (heap, cell) () := by
  rintro ⟨_, _, run⟩
  have inside := run.invariant (nullCallRegion heap)
    (by simp [nullCallRegion, null_call.initial, null_call.load,
      Algo2LeanCore.start, Algo2LeanCore.Config.heap])
    (nullCallRegion_preserved heap)
  exact inside.2

-- A shallowly valid object may contain missing fields. Reads require the field
-- to exist; the compiler cannot manufacture a default integer result.
theorem missing_field_has_no_output (heap : Heap) (cell : Ref_Cell) (output : Int)
    (missing : field_Cell_value heap cell = none) :
    ¬ uninitialized_read.Returns (heap, cell) output := by
  have terminal : Algo2LeanCore.Terminal Step (uninitialized_read.initial heap cell) := by
    intro next transition
    unfold uninitialized_read.initial Algo2LeanCore.start at transition
    cases transition <;> simp_all
  rintro ⟨finalHeap, _, trace, run⟩
  cases run with
  | cons transition _ => exact terminal _ transition

example (output : Int) :
    ¬ uninitialized_read.Returns ((({} : Heap).allocateObject "Cell"), 0) output := by
  exact missing_field_has_no_output _ _ _ (by decide)
