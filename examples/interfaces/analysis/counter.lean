import Algo.counter.Generated
import Algo2LeanLib.CallCost
import Algo2LeanLib.HeapFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


open Algo2LeanCore Algo2LeanGenerated Algo.counter

/-- The small behavioral contract used by the client. A representation describes
    one shared mutable object; costs are increments from the actual input heap.
    Operations preserve allocation, all sequences and collections, object classes,
    and every object except the represented receiver. -/
structure CounterContract (code : Counter.Code) where
  Represents : Heap → ObjectRef → Int → Prop
  readCost : Nat
  writeCost : Nat
  valid : ∀ {heap ref value}, Represents heap ref value → code.valid heap ref = true
  read : ∀ {heap ref value}, Represents heap ref value →
    ∃ after, Counter.get.Call code heap ref after value ∧
      Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" readCost) ∧
      heap.Modifies after [] [ref]
  write : ∀ {heap ref old} (value : Int), Represents heap ref old →
    ∃ after, Counter.put.Call code heap (ref, value) after () ∧
      Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" writeCost) ∧
      heap.Modifies after [] [ref]
