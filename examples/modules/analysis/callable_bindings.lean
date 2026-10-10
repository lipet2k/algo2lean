import Algo.callable_client.Analysis
import Algo.callable_direct.Analysis
import Algo.callable_staged.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `direct_summary`: Reusable direct-callable contract.
- `staged_summary`: Reusable staged-callable contract.
- `direct_correct`: Direct-callable correctness.
- `staged_correct`: Staged-callable correctness.
- `direct_first_tick`: Bound callable retains local tick behavior.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace CallableBindings

namespace Direct

open Algo.callable_direct Algo.callable_direct.Algo2LeanGenerated

def decode : Result → Option Int
  | .fn_successor value => some value

/-- The adapter contains the original compiled function's control; no receiver
    is added and the heap is neither allocated nor repacked. -/
def code : CallableClient.Code where
  toInterfaceCode := InterfaceAdapter.code Step
  entry value := InterfaceAdapter.entry (entry_successor value) decode

def facts : InterfaceFacts code.toInterfaceCode :=
  InterfaceAdapter.facts next step_next

theorem summary (heap : Heap) (value : Int) :
    CallableClient.call.Call code heap value (heap.tick "callable_work") (value + 1) :=
  InterfaceAdapter.summary terminal (CallableDirectAnalysis.summary heap value).2 decode rfl

end Direct

namespace Staged

open Algo.callable_staged Algo.callable_staged.Algo2LeanGenerated

def decode : Result → Option Int
  | .fn_successor value => some value

def code : CallableClient.Code where
  toInterfaceCode := InterfaceAdapter.code Step
  entry value := InterfaceAdapter.entry (entry_successor value) decode

def facts : InterfaceFacts code.toInterfaceCode :=
  InterfaceAdapter.facts next step_next

theorem summary (heap : Heap) (value : Int) :
    CallableClient.call.Call code heap value (heap.tick "callable_work" 2) (value + 1) :=
  InterfaceAdapter.summary terminal (CallableStagedAnalysis.summary heap value).2 decode rfl

end Staged

/-- Both instances reuse the identical client body and client proof. -/
theorem direct_summary (heap : Heap) (value : Int) :
    CallableClient.twice.Call Direct.code heap value
      (heap.tick "callable_work" 2) (value + 2) :=
  CallableClient.summary Direct.code 1 Direct.summary heap value

theorem staged_summary (heap : Heap) (value : Int) :
    CallableClient.twice.Call Staged.code heap value
      (heap.tick "callable_work" 4) (value + 2) :=
  CallableClient.summary Staged.code 2 Staged.summary heap value

-- Main result: Correctness and running time
theorem direct_correct {before after : Heap} {value result : Int}
    (execution : CallableClient.twice.Run Direct.code before value after result) :
    after = before.tick "callable_work" 2 ∧ result = value + 2 :=
  CallableClient.correct Direct.code Direct.facts 1 Direct.summary execution

-- Main result: Correctness and running time
theorem staged_correct {before after : Heap} {value result : Int}
    (execution : CallableClient.twice.Run Staged.code before value after result) :
    after = before.tick "callable_work" 4 ∧ result = value + 2 :=
  CallableClient.correct Staged.code Staged.facts 2 Staged.summary execution

/-- The first source tick remains observable inside both nested adapters,
    before either the first call or the client has returned. -/
theorem direct_first_tick (heap : Heap) (value : Int) :
    ∃ state : CallableClient.Configuration Direct.code,
      CallableClient.Step Direct.code
        (.active heap (.imported (Direct.code.entry value) [] .afterFirst) []) state ∧
      state.heap = heap.tick "callable_work" := by
  open Algo.callable_direct.Algo2LeanGenerated in
    exact ⟨_, CallableClient.Step.imported _ _ _ _ _ _
      (InterfaceAdapter.Step.imported _ _ _ _ _ _
        (Step.successor_pc3 heap { v0 := value } [])), rfl⟩

end CallableBindings
