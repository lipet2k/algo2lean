import Algo2LeanLib.Interface

open Algo2LeanCore Algo2LeanGenerated

namespace InterfaceCoreTest

namespace Source
inductive Frame where
  | entry
  | result
  | spin
inductive Result where
  | value (number : Int)
  | other
abbrev Configuration := Config Heap Frame Result
inductive Step : Configuration → Configuration → Prop where
  | entry (heap : Heap) (stack : Stack Frame Result) :
      Step (.active heap .entry stack) (.active (heap.tick "method" 3) .result stack)
  | result (heap : Heap) (stack : Stack Frame Result) :
      Step (.active heap .result stack) (resumeConfig heap (.value 7) stack)
  | spin (heap : Heap) (stack : Stack Frame Result) :
      Step (.active heap .spin stack) (.active (heap.tick "spin") .spin stack)
theorem terminal (heap : Heap) (result : Result) : Terminal Step (.done heap result) := by
  intro next transition
  cases transition
theorem contract (heap : Heap) : Summary Step heap .entry (heap.tick "method" 3) (.value 7) := by
  intro caller
  apply Reaches.prepend (Step.entry heap caller)
  exact Reaches.single (Step.result _ caller)
def next : Configuration → Configuration
  | .active heap .entry stack => .active (heap.tick "method" 3) .result stack
  | .active heap .result stack => resumeConfig heap (.value 7) stack
  | .active heap .spin stack => .active (heap.tick "spin") .spin stack
  | .done heap result => .done heap result
theorem step_next {before after : Configuration} (transition : Step before after) :
    next before = after := by cases transition <;> rfl
end Source

inductive Result where
  | operation (number : Int)

def decode : Source.Result → Option Result
  | .value number => some (.operation number)
  | .other => none

def implementation : InterfaceCode Heap Result := InterfaceAdapter.code Source.Step

/-- The concrete proof is reused with unchanged heap and named-clock effects. -/
theorem imported_contract (heap : Heap) :
    Summary implementation.Step heap (InterfaceAdapter.entry Source.Frame.entry decode)
      (heap.tick "method" 3) (.operation 7) :=
  InterfaceAdapter.summary Source.terminal (Source.contract heap) decode rfl

def implementation_facts : InterfaceFacts implementation :=
  InterfaceAdapter.facts Source.next Source.step_next

example : Deterministic implementation.Step := implementation_facts.deterministic

/-- The decoder never invents a result for an unrelated concrete operation. -/
example : InterfaceAdapter.decodeFrame (SourceFrame := Source.Frame) decode .other = .invalid := rfl

example (heap : Heap) :
    Terminal implementation.Step (.active heap .invalid []) := by
  intro next transition
  cases transition

/-- A finite transcript remains visible while the concrete method diverges. -/
example (heap : Heap) :
    Reaches implementation.Step
      (.active heap (InterfaceAdapter.entry Source.Frame.spin decode) [])
      (.active ((heap.tick "spin").tick "spin")
        (InterfaceAdapter.entry Source.Frame.spin decode) []) := by
  exact ModuleCall.reaches (InterfaceAdapter.simulates Source.terminal)
    (InterfaceAdapter.decodeFrame decode) []
    ((Reaches.single (Source.Step.spin heap [])).trans
      (Reaches.single (Source.Step.spin (heap.tick "spin") [])))

end InterfaceCoreTest
