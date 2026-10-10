open Algo2LeanCore

-- A local statement theorem: no initial state or transcript is assumed.
theorem assignment_local {before after : Configuration}
    (transition : Step before after) (location : assignment.At.set before) :
    assignment.At.after after ∧ assignment.Local.a after = some 1 := by
  cases transition <;> simp_all [assignment.At.set, assignment.At.after, assignment.Local.a]

def AssignmentFact (before after : Configuration) : Prop :=
  assignment.At.set before → assignment.Local.a after = some 1

-- Every transition from the named assignment location sets a to 1;
-- the property holds at each adjacent pair of a valid transcript.
theorem assignment_fact_on_any_transcript {initial final : Configuration} {trace : Transcript}
    (valid : Valid Step initial trace final) : Valid AssignmentFact initial trace final := by
  exact valid.lift (fun _ _ transition location => (assignment_local transition location).2)

theorem pass_preserves_assignment {before after : Configuration}
    (transition : Step before after) (location : assignment.At.after before)
    (value : assignment.Local.a before = some 1) :
    assignment.At.ready after ∧ assignment.Local.a after = some 1 := by
  cases transition <;>
    simp_all [assignment.At.after, assignment.At.ready, assignment.Local.a]

-- Local facts compose without assuming either state is reachable from entry.
theorem local_composition {before middle after : Configuration}
    (assign : Step before middle) (pass : Step middle after)
    (location : assignment.At.set before) :
    Reaches Step before after ∧ assignment.At.ready after ∧ assignment.Local.a after = some 1 := by
  have assigned := assignment_local assign location
  exact ⟨(Reaches.single assign).trans (Reaches.single pass),
    pass_preserves_assignment pass assigned.1 assigned.2⟩

-- Getters exclude uninitialized locals, internal instruction points and other functions.
example (heap : Heap) (n : Int) : assignment.Local.a (assignment.initial heap n) = none := rfl
example (heap : Heap) (state : State_assignment) (stack : Stack) :
    assignment.Local.a (.active heap (.fn_assignment 1 state) stack) = none := rfl
example (heap : Heap) (n : Int) : assignment.Local.a (caller.initial heap n) = none := rfl

def readyState (n : Int) : State_assignment := { v0 := n, v1 := 1 }
def readyConfig (heap : Heap) (n : Int) (stack : Stack) : Configuration :=
  .active heap (.fn_assignment 2 (readyState n)) stack

theorem assignment_ready_prefix (heap : Heap) (n : Int) (stack : Stack) :
    Reaches Step (.active heap (.fn_assignment 5 { v0 := n }) stack)
      (readyConfig heap n stack) := by
  algo_steps

theorem ready_has_value (heap : Heap) (n : Int) (stack : Stack) :
    assignment.At.ready (readyConfig heap n stack) ∧
    assignment.Local.a (readyConfig heap n stack) = some 1 := by
  exact (local_composition (Step.assignment_pc4 heap { v0 := n } stack)
    (Step.assignment_pc3 heap { v0 := n, v1 := 1 } stack) True.intro).2

-- From the named return location, a = 1 suffices to return 1 with the
-- supplied heap and caller stack; no other local-variable facts are required.
theorem return_from_ready (heap : Heap) (state : State_assignment) (stack : Stack)
    (value : assignment.Local.a (.active heap (.fn_assignment 2 state) stack) = some 1) :
    Reaches Step (.active heap (.fn_assignment 2 state) stack)
      (resumeConfig heap (.fn_assignment 1) stack) := by
  have field : state.v1 = 1 := by simpa [assignment.Local.a] using value
  refine (Reaches.single (Step.assignment_pc2 heap state stack)).trans ?_
  simpa [field] using
    Reaches.single (Step.assignment_pc1 heap { state with t2 := state.v1 } stack)

-- The assignment function returns 1 without changing the heap, under any
-- caller stack; compose its entry prefix with the local return theorem.
theorem assignment_summary_from_intermediate (heap : Heap) (n : Int) :
    assignment.Call heap n heap 1 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  exact (assignment_ready_prefix heap n stack).trans
    (return_from_ready heap (readyState n) stack (ready_has_value heap n stack).2)

theorem assignment_output_from_intermediate (n : Int) : assignment.Returns n 1 := by
  exact ⟨{}, True.intro, (assignment_summary_from_intermediate {} n).2.root⟩

-- The caller reuses the summary, rather than expanding the callee transcript.
theorem caller_reuses_summary (heap : Heap) (n : Int) :
    caller.Run heap n heap 2 := by
  let callerState : State_caller := { v0 := n, t4 := n }
  let resume : Result → Frame := fun value => match value with
    | .fn_assignment result => .fn_caller 3 { callerState with t3 := result }
    | _ => .invalid
  have enter : Reaches Step (caller.initial heap n)
      (.active heap (.fn_assignment 5 { v0 := n }) [resume]) := by
    exact (Reaches.single (Step.caller_pc5 heap { v0 := n } [])).trans
      (Reaches.single (Step.caller_pc4 heap callerState []))
  have callee := (assignment_summary_from_intermediate heap n).2 [resume]
  have finish : Reaches Step (resumeConfig heap (.fn_assignment 1) [resume])
      (.done heap (.fn_caller 2)) := by
    algo_steps
  exact ⟨True.intro, (enter.trans callee).trans finish⟩

-- Explicit historical states retain old contents even when their object IDs agree.
def historicalHeap (value : Int) : Heap := ({} : Heap).allocate (fun _ => value)
def beforeWrite (value : Int) : Configuration :=
  .active (historicalHeap value) (.fn_mutate 4 {}) []
def afterWrite (value : Int) : Configuration :=
  .active ((historicalHeap value).write 0 0 9) (.fn_mutate 3 {}) []

theorem historical_write_segment (value : Int) :
    Reaches Step (beforeWrite value) (afterWrite value) := by
  exact Reaches.single (Step.mutate_pc4 _ _ _ (by change (0 : Nat) < 1; decide))

theorem historical_contents (value : Int) :
    mutate.Local.a (beforeWrite value) = some 0 ∧
    mutate.Local.b (beforeWrite value) = some 0 ∧
    mutate.Local.a (afterWrite value) = some 0 ∧
    (beforeWrite value).heap.read 0 0 = value ∧
    (afterWrite value).heap.read 0 0 = 9 := by
  simp [beforeWrite, afterWrite, mutate.Local.a, mutate.Local.b,
    Config.heap, historicalHeap, Heap.read, Heap.allocate, Heap.write]

theorem historical_other_indices (value index : Int) (other : index ≠ 0) :
    (afterWrite value).heap.read 0 index = (beforeWrite value).heap.read 0 index := by
  simp [afterWrite, beforeWrite, Config.heap, Heap.read, Heap.write, other]

-- Element getters observe the contents in the supplied configuration: both aliases
-- see the write at index 0, while the negative-index value remains unchanged.
theorem named_sequence_elements (value : Int) :
    mutate.Element.a (beforeWrite value) 0 = some value ∧
    mutate.Element.a (afterWrite value) 0 = some 9 ∧
    mutate.Element.b (afterWrite value) 0 = some 9 ∧
    mutate.Element.b (afterWrite value) (-17) = some value := by
  simp [mutate.Element.a, mutate.Element.b, mutate.Local.a, mutate.Local.b,
    beforeWrite, afterWrite, Config.heap, historicalHeap, Heap.read, Heap.allocate, Heap.write]

example (heap : Heap) : mutate.Element.b (mutate.initial heap 0) 0 = none := rfl
example (heap : Heap) (n : Int) : mutate.Element.a (assignment.initial heap n) 0 = none := rfl
example (heap : Heap) (state : State_mutate) (stack : Stack) :
    mutate.Element.a (.active heap (.fn_mutate 1 state) stack) 0 = none := rfl
