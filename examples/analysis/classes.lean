import ClassesGenerated

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `counter_alias_observes_increment`: Shared-object mutation.
- `read_counter_output`: Counter output.
- `chain_sum_summary`: Reusable linked-list sum contract.
- `chain_sum_output`: Linked-list sum correctness.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace ClassesAnalysis

-- Method specifications describe a supplied object and heap. They work under
-- every suspended caller, so clients can reuse them without inspecting methods.
theorem counter_read_summary (heap : Heap) (counter : Ref_Counter) (value : Int)
    (valid : is_Counter heap counter)
    (stored : field_Counter_value heap counter = some value) :
    Counter.read.Call heap counter heap value := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.Counter_read_pc2 _ _ _ (by simp [stored]))
  simpa [stored] using Reaches.single
    (Step.Counter_read_pc1 heap
      { v0 := counter, t1 := (field_Counter_value heap counter).getD 0 } stack)

theorem counter_add_summary (heap : Heap) (counter : Ref_Counter) (value delta : Int)
    (valid : is_Counter heap counter)
    (stored : field_Counter_value heap counter = some value) :
    Counter.add.Call heap (counter, delta)
      (set_Counter_value heap counter (value + delta)) () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.Counter_add_pc6 _ _ _)
  apply Reaches.prepend (Step.Counter_add_pc5 _ _ _ (by simp [stored]))
  apply Reaches.prepend (Step.Counter_add_pc4 _ _ _)
  apply Reaches.prepend (Step.Counter_add_pc3 _ _ _ valid)
  apply Reaches.prepend (Step.Counter_add_pc2 _ _ _)
  simpa [stored] using Reaches.single
    (Step.Counter_add_pc1 (set_Counter_value heap counter
      ((field_Counter_value heap counter).getD 0 + delta))
      { v0 := counter, v1 := delta, t3 := counter,
        t4 := (field_Counter_value heap counter).getD 0, t5 := delta } stack)

-- Sharing is expressed by equality of references. An observer holding the
-- original reference sees the value written through any alias of that object.
theorem counter_alias_observes_increment (heap : Heap) (counter alias : Ref_Counter)
    (value delta : Int) (valid : is_Counter heap counter)
    (stored : field_Counter_value heap counter = some value) (shared : alias = counter) :
    ∃ after, Counter.add.Call heap (alias, delta) after () ∧
      field_Counter_value after counter = some (value + delta) := by
  subst alias
  exact ⟨_, counter_add_summary heap counter value delta valid stored,
    field_Counter_value_set heap counter (value + delta) valid⟩

theorem read_counter_summary (heap : Heap) (counter : Ref_Counter) (value : Int)
    (valid : is_Counter heap counter)
    (stored : field_Counter_value heap counter = some value) :
    read_counter.Call heap counter heap value := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.read_counter_pc4 _ _ _)
  apply Reaches.prepend (Step.read_counter_pc3 _ _ _ valid)
  apply Reaches.prepend (Step.read_counter_pc2 _ _ _)
  apply Reaches.trans ((counter_read_summary heap counter value valid stored).2 _)
  exact Reaches.single (Step.read_counter_pc1 _ _ _)

theorem read_counter_output (heap : Heap) (counter : Ref_Counter) (value : Int)
    (valid : is_Counter heap counter)
    (stored : field_Counter_value heap counter = some value) :
    read_counter.Returns (heap, counter) value := by
  have summary := read_counter_summary heap counter value valid stored
  exact ⟨heap, summary.1, summary.2.root⟩

-- This invariant describes a finite nonempty chain using only the class
-- interface. Unrelated objects and aliases elsewhere in the heap are allowed.
inductive Chain (heap : Heap) : Ref_Node → List Int → Prop where
  | last (node : Ref_Node) (value : Int)
      (valid : is_Node heap node)
      (stored : field_Node_value heap node = some value)
      (endOfChain : field_Node_next heap node = some none) :
      Chain heap node [value]
  | link (node tail : Ref_Node) (value : Int) (values : List Int)
      (valid : is_Node heap node)
      (stored : field_Node_value heap node = some value)
      (next : field_Node_next heap node = some (some tail))
      (rest : Chain heap tail values) :
      Chain heap node (value :: values)

theorem last_node_summary (heap : Heap) (node : Ref_Node) (value : Int)
    (valid : is_Node heap node)
    (stored : field_Node_value heap node = some value)
    (endOfChain : field_Node_next heap node = some none) :
    Node.sum.Call heap node heap value := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.Node_sum_pc11 _ _ _ (by simp [endOfChain]))
  apply Reaches.prepend (Step.Node_sum_pc10 _ _ _)
  apply Reaches.prepend (Step.Node_sum_pc9_true _ _ _ (by simp [endOfChain]))
  apply Reaches.prepend (Step.Node_sum_pc2 _ _ _ (by simp [stored]))
  simpa [stored] using Reaches.single (Step.Node_sum_pc1 heap
    { v0 := node, v1 := (field_Node_next heap node).getD none,
      t2 := decide ((field_Node_next heap node).getD none = none),
      t3 := (field_Node_value heap node).getD 0 } stack)

theorem linked_node_summary (heap : Heap) (node tail : Ref_Node) (value total : Int)
    (valid : is_Node heap node)
    (stored : field_Node_value heap node = some value)
    (next : field_Node_next heap node = some (some tail))
    (tailSummary : Node.sum.Call heap tail heap total) :
    Node.sum.Call heap node heap (value + total) := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.Node_sum_pc11 _ _ _ (by simp [next]))
  apply Reaches.prepend (Step.Node_sum_pc10 _ _ _)
  apply Reaches.prepend (Step.Node_sum_pc9_false _ _ _ (by simp [next]))
  apply Reaches.prepend (Step.Node_sum_pc8 _ _ _ (by simp [stored]))
  apply Reaches.prepend (Step.Node_sum_pc7 _ _ _)
  apply Reaches.prepend (Step.Node_sum_pc6 _ _ _ (by simpa [next] using! tailSummary.1))
  apply Reaches.prepend (Step.Node_sum_pc5 _ _ _)
  simp only [next, Option.getD_some]
  apply Reaches.trans (tailSummary.2 _)
  apply Reaches.prepend (Step.Node_sum_pc4 _ _ _)
  simpa [stored] using Reaches.single (Step.Node_sum_pc3 heap
    { v0 := node, v1 := some tail, t2 := decide (some tail = (none : Option Ref_Node)),
      t4 := (field_Node_value heap node).getD 0 + total,
      t5 := (field_Node_value heap node).getD 0, t6 := total, t7 := some tail } stack)

-- The proof follows the data structure. It reuses the method specification for
-- the tail, keeps the entire heap unchanged, and needs no explicit transcript.
theorem chain_sum_summary (heap : Heap) (node : Ref_Node) (values : List Int)
    (chain : Chain heap node values) :
    Node.sum.Call heap node heap values.sum := by
  induction chain with
  | last node value valid stored endOfChain =>
      simpa using last_node_summary heap node value valid stored endOfChain
  | link node tail value values valid stored next rest tailSummary =>
      simpa using linked_node_summary heap node tail value values.sum
        valid stored next tailSummary

-- Main result: Correctness
theorem chain_sum_output (heap : Heap) (node : Ref_Node) (values : List Int)
    (chain : Chain heap node values) :
    Node.sum.Returns (heap, node) values.sum := by
  have summary := chain_sum_summary heap node values chain
  exact ⟨heap, summary.1, summary.2.root⟩

end ClassesAnalysis
