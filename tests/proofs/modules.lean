import Algo2LeanLib.Modules

/-!
Module execution uses the original source relation and its existing proofs.
These fixtures cover nested source calls, transitive module reuse, distinct
result types, arbitrary suspended callers, divergence, and shared heap effects.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace Source
inductive Frame where
  | twice (value : Nat)
  | tick (value : Nat)
  | ret (value : Nat)
  | spin
  | allocate
  | mutate (original alias : SeqRef)
abbrev State := Config Heap Frame Nat
abbrev Stack := Algo2LeanCore.Stack Frame Nat
inductive Step : State → State → Prop where
  | twice (h : Heap) (value : Nat) (stack : Stack) :
      Step (.active h (.twice value) stack)
        (.active h (.tick value) ((fun result => .tick result) :: stack))
  | tick (h : Heap) (value : Nat) (stack : Stack) :
      Step (.active h (.tick value) stack) (.active (h.tick "library") (.ret value) stack)
  | ret (h : Heap) (value : Nat) (stack : Stack) :
      Step (.active h (.ret value) stack) (resumeConfig h value stack)
  | spin (h : Heap) (stack : Stack) :
      Step (.active h .spin stack) (.active (h.tick "spin") .spin stack)
  | allocate (h : Heap) (stack : Stack) :
      Step (.active h .allocate stack)
        (.active (h.allocate (fun _ => 11)) (.mutate h.nextRef h.nextRef) stack)
  | mutate (h : Heap) (original alias : SeqRef) (stack : Stack) :
      Step (.active h (.mutate original alias) stack)
        (.active ((h.write alias (-3) 7).tick "mutation") (.ret original) stack)
theorem deterministic : Deterministic Step := by
  intro a b c first second
  cases first <;> cases second <;> rfl
theorem twice_summary (h : Heap) (value : Nat) :
    Summary Step h (.twice value) ((h.tick "library").tick "library") value := by
  intro stack
  apply Reaches.prepend (Step.twice h value stack)
  apply Reaches.prepend (Step.tick h value _)
  apply Reaches.prepend (Step.ret (h.tick "library") value _)
  apply Reaches.prepend (Step.tick (h.tick "library") value _)
  exact Reaches.single (Step.ret ((h.tick "library").tick "library") value stack)

def allocatedHeap (h : Heap) : Heap :=
  ((h.allocate (fun _ => 11)).write h.nextRef (-3) 7).tick "mutation"

theorem allocation_summary (h : Heap) :
    Summary Step h .allocate (allocatedHeap h) h.nextRef := by
  intro stack
  apply Reaches.prepend (Step.allocate h stack)
  apply Reaches.prepend (Step.mutate _ _ _ stack)
  exact Reaches.single (Step.ret _ _ stack)

theorem allocation_effects (h : Heap) :
    (allocatedHeap h).nextRef = h.nextRef + 1 ∧
    (allocatedHeap h).read h.nextRef (-3) = 7 ∧
    (allocatedHeap h).read h.nextRef 0 = 11 ∧
    (allocatedHeap h).clocks "mutation" = h.clocks "mutation" + 1 := by
  simp [allocatedHeap]

theorem allocation_preserves_old_refs (h : Heap) (ref : SeqRef) (index : Int)
    (existing : ref < h.nextRef) :
    (allocatedHeap h).read ref index = h.read ref index := by
  simp [allocatedHeap, existing, Nat.ne_of_lt existing]
end Source

namespace Caller
inductive Frame where
  | imported (frame : Source.Frame) (inner : Source.Stack) (resume : Nat → Frame)
  | complete (value : Nat)
abbrev State := Config Heap Frame Bool
abbrev Stack := Algo2LeanCore.Stack Frame Bool
inductive Step : State → State → Prop where
  | imported (h : Heap) (frame : Source.Frame) (inner : Source.Stack)
      (resume : Nat → Frame) (caller : Stack) (after : Source.State)
      (transition : Source.Step (.active h frame inner) after) :
      Step (.active h (.imported frame inner resume) caller)
        (ModuleCall.config Frame.imported resume caller after)
  | complete (h : Heap) (value : Nat) (caller : Stack) :
      Step (.active h (.complete value) caller) (resumeConfig h (value == 0) caller)
theorem simulates : ModuleCall.Simulates Frame.imported Source.Step Step := by
  apply ModuleCall.Delegates.simulates
  · exact Step.imported
  · intro heap result next transition
    cases transition
theorem deterministic : Deterministic Step := by
  intro a b c first second
  cases first with
  | imported h frame inner resume caller after execution =>
    cases second with
    | imported _ _ _ _ _ other otherExecution =>
      exact congrArg (ModuleCall.config Frame.imported resume caller)
        (Source.deterministic execution otherExecution)
  | complete h value caller => cases second; rfl
theorem terminal (h : Heap) (result : Bool) : Terminal Step (.done h result) := by
  intro next transition
  cases transition
theorem imported_summary (h : Heap) (value : Nat) :
    Summary Step h (.imported (.twice value) [] Frame.complete)
      ((h.tick "library").tick "library") (value == 0) := by
  intro caller
  exact (ModuleCall.summary simulates Frame.complete caller (Source.twice_summary h value)).trans
    (Reaches.single (Step.complete _ _ caller))

/-- A completed run's heap and result follow from the imported proof and
    determinism. No reverse translation of caller frames is needed. -/
theorem every_completed_import (h : Heap) (value : Nat) (after : Heap) (output : Bool)
    (execution : Reaches Step (start h (.imported (.twice value) [] Frame.complete))
      (.done after output)) :
    after = (h.tick "library").tick "library" ∧ output = (value == 0) := by
  have equal := Reaches.eq_of_terminal (step := Step) deterministic (imported_summary h value).root execution
    (terminal _ _) (terminal _ _)
  have parts := Config.done.inj equal
  exact ⟨parts.1.symm, parts.2.symm⟩

/-- Allocation and a write through an alias retain the same shared identities
    when the source summary is used under any caller stack. -/
theorem imported_allocation (h : Heap) :
    Summary Step h (.imported .allocate [] Frame.complete)
      (Source.allocatedHeap h) (h.nextRef == 0) := by
  intro caller
  exact (ModuleCall.summary simulates Frame.complete caller (Source.allocation_summary h)).trans
    (Reaches.single (Step.complete _ _ caller))

theorem divergence_prefix (h : Heap) (caller : Stack) :
    Valid Step (.active h (.imported .spin [] Frame.complete) caller)
      [ .active h (.imported .spin [] Frame.complete) caller,
        .active (h.tick "spin") (.imported .spin [] Frame.complete) caller,
        .active ((h.tick "spin").tick "spin") (.imported .spin [] Frame.complete) caller ]
      (.active ((h.tick "spin").tick "spin") (.imported .spin [] Frame.complete) caller) := by
  exact ModuleCall.valid simulates Frame.complete caller
    (.cons (Source.Step.spin h []) (.cons (Source.Step.spin _ []) (.single _)))
end Caller

namespace Outer
inductive Frame where
  | imported (frame : Caller.Frame) (inner : Caller.Stack) (resume : Bool → Frame)
  | complete
abbrev State := Config Heap Frame Unit
abbrev Stack := Algo2LeanCore.Stack Frame Unit
inductive Step : State → State → Prop where
  | imported (h : Heap) (frame : Caller.Frame) (inner : Caller.Stack)
      (resume : Bool → Frame) (caller : Stack) (after : Caller.State)
      (transition : Caller.Step (.active h frame inner) after) :
      Step (.active h (.imported frame inner resume) caller)
        (ModuleCall.config Frame.imported resume caller after)
  | complete (h : Heap) (caller : Stack) :
      Step (.active h .complete caller) (resumeConfig h () caller)
theorem simulates : ModuleCall.Simulates Frame.imported Caller.Step Step := by
  apply ModuleCall.Delegates.simulates
  · exact Step.imported
  · intro heap result next transition
    cases transition
theorem composed_summary (h : Heap) (value : Nat) :
    Summary Step h
      (.imported (.imported (.twice value) [] Caller.Frame.complete) [] (fun _ => .complete))
      ((h.tick "library").tick "library") () := by
  intro caller
  exact (ModuleCall.summary simulates (fun _ => Frame.complete) caller
    (Caller.imported_summary h value)).trans (Reaches.single (Step.complete _ caller))
end Outer
