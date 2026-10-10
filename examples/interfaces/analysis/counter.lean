import Algo.counter.Generated
import Algo2LeanLib.CallCost

open Algo2LeanCore Algo2LeanGenerated Algo.counter

/-- The small behavioral contract used by the client. A representation describes
    one shared mutable object; costs are increments from the actual input heap. -/
structure CounterContract (code : Counter.Code) where
  Represents : Heap → ObjectRef → Int → Prop
  readCost : Nat
  writeCost : Nat
  valid : ∀ {heap ref value}, Represents heap ref value → code.valid heap ref = true
  read : ∀ {heap ref value}, Represents heap ref value →
    ∃ after, Counter.get.Call code heap ref after value ∧
      Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" readCost)
  write : ∀ {heap ref old} (value : Int), Represents heap ref old →
    ∃ after, Counter.put.Call code heap (ref, value) after () ∧
      Represents after ref value ∧
      heap.Increments after (Clocks.single "counter_work" writeCost)
