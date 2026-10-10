namespace TranscriptDivergence

open Algo2LeanCore

-- These continuations are ordinary data in the explicit transcript. No call
-- identifiers or visit counters are needed to distinguish nested invocations.
def suspendedCaller (n : Int) : Result → Frame
  | .fn_spin result => .fn_start_spin 3 { v0 := n, t3 := result, t4 := n }
  | _ => .invalid

def suspendedSpin (n : Int) : Result → Frame
  | .fn_spin result => .fn_spin 1 { v0 := n, t1 := result, t2 := n + 1 }
  | _ => .invalid

def secondEntry (heap : Heap) (n : Int) : Configuration :=
  .active heap (.fn_spin 4 { v0 := n + 1 }) [suspendedSpin n, suspendedCaller n]

-- Six states record five steps, stopping at the recursive callee's entry.
-- The heap and input are arbitrary; this is not a test at one concrete input.
def recursivePrefix (heap : Heap) (n : Int) : Transcript :=
  [ start_spin.initial heap n,
    .active heap (.fn_start_spin 4 { v0 := n, t4 := n }) [],
    .active heap (.fn_spin 4 { v0 := n }) [suspendedCaller n],
    .active heap (.fn_spin 3 { v0 := n }) [suspendedCaller n],
    .active heap (.fn_spin 2 { v0 := n, t2 := n + 1 }) [suspendedCaller n],
    secondEntry heap n ]

theorem recursive_prefix_valid (heap : Heap) (n : Int) :
    Valid Step (start_spin.initial heap n) (recursivePrefix heap n) (secondEntry heap n) := by
  algo_steps

theorem recursive_prefix_is_transcript (heap : Heap) (n : Int) :
    start_spin.ValidHeapTranscript heap n (recursivePrefix heap n) :=
  ⟨True.intro, secondEntry heap n, recursive_prefix_valid heap n⟩

theorem recursive_entry_named (heap : Heap) (n : Int) :
    spin.At.entered (secondEntry heap n) ∧ spin.Local.n (secondEntry heap n) = some (n + 1) :=
  ⟨True.intro, rfl⟩

theorem caller_value_uninitialized (heap : Heap) (n : Int) :
    start_spin.At.waiting (start_spin.initial heap n) ∧
    start_spin.Local.value (start_spin.initial heap n) = none :=
  ⟨True.intro, rfl⟩

-- This local invariant handles every possible finite prefix. It excludes the
-- return instructions in both functions, rather than enumerating longer runs.
def recursiveRegion : Configuration → Prop
  | .active _ (.fn_start_spin pc _) _ => pc = 5 ∨ pc = 4
  | .active _ (.fn_spin pc _) _ => pc = 4 ∨ pc = 3 ∨ pc = 2
  | _ => False

theorem recursive_region_preserved {before after : Configuration}
    (transition : Step before after) (inside : recursiveRegion before) :
    recursiveRegion after := by
  cases transition <;> simp_all [recursiveRegion]

theorem recursive_region_has_no_caller_return {state : Configuration}
    (inside : recursiveRegion state) :
    ¬ start_spin.At.unreachable state ∧ start_spin.Local.value state = none := by
  cases state with
  | done => exact inside.elim
  | active heap frame stack =>
    cases frame <;> simp only [recursiveRegion] at inside
    case fn_spin => simp [start_spin.At.unreachable, start_spin.Local.value]
    case fn_start_spin pc locals =>
      rcases inside with rfl | rfl <;>
        simp [start_spin.At.unreachable, start_spin.Local.value]

theorem caller_return_never_in_transcript (heap : Heap) (n : Int) (trace : Transcript)
    (valid : start_spin.ValidHeapTranscript heap n trace) :
    ∀ state ∈ trace, ¬ start_spin.At.unreachable state ∧ start_spin.Local.value state = none := by
  obtain ⟨_, final, valid⟩ := valid
  have stays := valid.all_states recursiveRegion
    (by simp [start_spin.initial, start, recursiveRegion])
    (fun _ _ transition inside => recursive_region_preserved transition inside)
  intro state member
  exact recursive_region_has_no_caller_return (stays state member)

theorem diverging_caller_has_no_execution (heap finalHeap : Heap) (n output : Int) :
    ¬ start_spin.Run heap n finalHeap output := by
  rintro ⟨_, trace, valid⟩
  have impossible := valid.invariant recursiveRegion
    (by simp [start_spin.initial, start, recursiveRegion])
    (fun _ _ transition inside => recursive_region_preserved transition inside)
  exact impossible

theorem diverging_caller_has_no_output (n output : Int) : ¬ start_spin.Returns n output := by
  rintro ⟨finalHeap, execution⟩
  exact diverging_caller_has_no_execution {} finalHeap n output execution

end TranscriptDivergence
