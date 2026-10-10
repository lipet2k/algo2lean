import Algo2LeanLib.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable abstract-callable contract.
- `correct`: Callable-client correctness.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace CallableClient

/-- This example's fixed function signature has no receiver or object identity.
    Executable code and its typed entry are separate from behavioral laws. -/
structure Code extends InterfaceCode Heap Int where
  entry : Int → Frame

def call.Call (code : Code) (before : Heap) (value : Int) (after : Heap) (result : Int) : Prop :=
  Summary code.Step before (code.entry value) after result

/-- An executable two-call client, parameterized once by the callable's code. -/
inductive Frame (code : Code) where
  | start (value : Int)
  | afterFirst (value : Int)
  | returned (value : Int)
  | imported (frame : code.Frame) (inner : Stack code.Frame Int)
      (resume : Int → Frame code)

abbrev Configuration (code : Code) := Config Heap (Frame code) Int

inductive Step (code : Code) : Configuration code → Configuration code → Prop where
  | first (heap : Heap) (value : Int) (caller : Stack (Frame code) Int) :
      Step code (.active heap (.start value) caller)
        (.active heap (.imported (code.entry value) [] Frame.afterFirst) caller)
  | second (heap : Heap) (value : Int) (caller : Stack (Frame code) Int) :
      Step code (.active heap (.afterFirst value) caller)
        (.active heap (.imported (code.entry value) [] Frame.returned) caller)
  | returned (heap : Heap) (value : Int) (caller : Stack (Frame code) Int) :
      Step code (.active heap (.returned value) caller) (resumeConfig heap value caller)
  | imported (heap : Heap) (frame : code.Frame) (inner : Stack code.Frame Int)
      (resume : Int → Frame code) (caller : Stack (Frame code) Int)
      (after : Config Heap code.Frame Int)
      (transition : code.Step (.active heap frame inner) after) :
      Step code (.active heap (.imported frame inner resume) caller)
        (ModuleCall.config Frame.imported resume caller after)

theorem terminal (code : Code) (heap : Heap) (result : Int) :
    Terminal (Step code) (.done heap result) := by
  intro next transition
  cases transition

theorem simulates (code : Code) :
    ModuleCall.Simulates (Frame.imported (code := code)) code.Step (Step code) :=
  ModuleCall.Delegates.simulates (Step.imported (code := code)) code.terminal

/-- This applies to any finite source prefix, even when the callable diverges.
    There is no completed-call or behavioral-law premise. -/
theorem lift_prefix (code : Code) (resume : Int → Frame code) (caller : Stack (Frame code) Int)
    {before after : Config Heap code.Frame Int} (run : Reaches code.Step before after) :
    Reaches (Step code) (ModuleCall.config Frame.imported resume caller before)
      (ModuleCall.config Frame.imported resume caller after) :=
  ModuleCall.reaches (simulates code) resume caller run

def twice.Call (code : Code) (before : Heap) (value : Int) (after : Heap) (result : Int) : Prop :=
  Summary (Step code) before (.start value) after result

def twice.Run (code : Code) (before : Heap) (value : Int) (after : Heap) (result : Int) : Prop :=
  Reaches (Step code) (start before (.start value)) (.done after result)

/-- One client proof works for every executable callable with this local law.
    Both calls retain their actual transitions and exact shared heap effects. -/
theorem summary (code : Code) (charge : Nat)
    (successor : ∀ heap value, call.Call code heap value
      (heap.tick "callable_work" charge) (value + 1))
    (heap : Heap) (value : Int) :
    twice.Call code heap value (heap.tick "callable_work" (charge + charge)) (value + 2) := by
  suffices calls : twice.Call code heap value
      ((heap.tick "callable_work" charge).tick "callable_work" charge) ((value + 1) + 1) by
    simpa [Heap.tick_add, Int.add_assoc] using calls
  intro caller
  apply Reaches.prepend (Step.first (code := code) heap value caller)
  apply (ModuleCall.summary (simulates code) _ caller (successor heap value)).trans
  apply Reaches.prepend (Step.second (code := code) _ _ caller)
  apply (ModuleCall.summary (simulates code) _ caller (successor _ _)).trans
  exact Reaches.single (Step.returned (code := code) _ _ caller)

/-- Optional determinism is derived from the callable's certificate alone. -/
def next {code : Code} (facts : InterfaceFacts code.toInterfaceCode) :
    Configuration code → Configuration code
  | .done heap result => .done heap result
  | .active heap (.start value) caller =>
      .active heap (.imported (code.entry value) [] Frame.afterFirst) caller
  | .active heap (.afterFirst value) caller =>
      .active heap (.imported (code.entry value) [] Frame.returned) caller
  | .active heap (.returned value) caller => resumeConfig heap value caller
  | .active heap (.imported frame inner resume) caller =>
      ModuleCall.config Frame.imported resume caller (facts.next (.active heap frame inner))

theorem step_next {code : Code} (facts : InterfaceFacts code.toInterfaceCode)
    {before after : Configuration code} (transition : Step code before after) :
    next facts before = after := by
  cases transition with
  | first | second | returned => rfl
  | imported heap frame inner resume caller after transition =>
      exact congrArg (ModuleCall.config Frame.imported resume caller) (facts.step_next transition)

theorem deterministic {code : Code} (facts : InterfaceFacts code.toInterfaceCode) :
    Deterministic (Step code) := by
  intro before left right first second
  exact (step_next facts first).symm.trans (step_next facts second)

-- Main result: Correctness and running time
/-- Every completed client execution has the independently proved result and
    exact full heap, including clocks and untouched sequence/object storage. -/
theorem correct (code : Code) (facts : InterfaceFacts code.toInterfaceCode) (charge : Nat)
    (successor : ∀ heap value, call.Call code heap value
      (heap.tick "callable_work" charge) (value + 1))
    {before after : Heap} {value result : Int}
    (execution : twice.Run code before value after result) :
    after = before.tick "callable_work" (charge + charge) ∧ result = value + 2 := by
  have same := Reaches.eq_of_terminal (step := Step code) (deterministic facts)
    execution (summary code charge successor before value).root
    (terminal code after result) (terminal code _ _)
  exact Config.done.inj same

end CallableClient
