import ObjectSequencesGenerated

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `shared_node_observed`: Shared object mutation is observable.
- `shallow_copy_summary`: Reusable shallow-copy contract.
- `shallow_copy_observations`: Fresh sequence with shared element objects.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace ObjectSequencesAnalysis

-- Reading an element's field needs only facts about that entry and that node.
-- No invariant over every entry or recursive traversal of the heap is needed.
theorem read_value_summary (heap : Heap) (nodes : CollectionRef) (index : Int)
    (node : Ref_Node) (value : Int)
    (valid : seq_Node.valid heap nodes)
    (entry : seq_Node.get heap nodes index = some node)
    (stored : field_Node_value heap node = some value) :
    read_value.Call heap (nodes, index) heap value := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.read_value_pc2 _ _ _ (by simp [entry, stored]))
  simpa [entry, stored] using Reaches.single
    (Step.read_value_pc1 heap
      { v0 := nodes, v1 := index,
        t2 := (field_Node_value heap ((seq_Node.get heap nodes index).getD 0)).getD 0 }
      stack)

-- The exact heap effect is an update to the referenced node, not replacement
-- of the sequence entry. This summary can be reused by any caller.
theorem set_value_summary (heap : Heap) (nodes : CollectionRef) (index value : Int)
    (node : Ref_Node)
    (valid : seq_Node.valid heap nodes)
    (entry : seq_Node.get heap nodes index = some node)
    (nodeValid : is_Node heap node) :
    set_value.Call heap (nodes, index, value)
      (set_Node_value heap node value) () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.set_value_pc3 _ _ _ (by simp [entry, nodeValid]))
  apply Reaches.prepend (Step.set_value_pc2 _ _ _)
  simpa [entry] using Reaches.single
    (Step.set_value_pc1 (set_Node_value heap ((seq_Node.get heap nodes index).getD 0) value)
      { v0 := nodes, v1 := index, v2 := value } stack)

-- A node field update preserves sequence identities and entries.
theorem entries_preserved (heap : Heap) (nodes : CollectionRef) (index value : Int)
    (node : Ref_Node) :
    seq_Node.get (set_Node_value heap node value) nodes index =
      seq_Node.get heap nodes index := by
  simp [set_Node_value, SequenceType.get, SequenceType.valid, Heap.validSequence,
    Heap.sequenceType, Heap.readElement]

-- The two references and indices may be different. Sharing the element node
-- is enough: an observer reads the new field value through its own sequence.
theorem shared_node_observed (heap : Heap) (nodes observer : CollectionRef)
    (index otherIndex value : Int) (node : Ref_Node)
    (valid : seq_Node.valid heap nodes)
    (observerValid : seq_Node.valid heap observer)
    (entry : seq_Node.get heap nodes index = some node)
    (shared : seq_Node.get heap observer otherIndex = some node)
    (nodeValid : is_Node heap node) :
    ∃ after, set_value.Call heap (nodes, index, value) after () ∧
      read_value.Call after (observer, otherIndex) after value := by
  refine ⟨set_Node_value heap node value,
    set_value_summary heap nodes index value node valid entry nodeValid, ?_⟩
  have valid' : seq_Node.valid (set_Node_value heap node value) observer := by
    simpa [SequenceType.valid, Heap.validSequence, Heap.sequenceType,
      set_Node_value] using observerValid
  have entry' : seq_Node.get (set_Node_value heap node value) observer otherIndex =
      some node := by rw [entries_preserved, shared]
  have summary := read_value_summary (set_Node_value heap node value) observer
    otherIndex node value valid' entry' (field_Node_value_set heap node value nodeValid)
  exact summary

-- A shallow copy has a concise heap specification using the shared descriptor.
theorem shallow_copy_summary (heap : Heap) (nodes : CollectionRef)
    (valid : seq_Node.valid heap nodes) :
    shallow_copy.Call heap nodes
      (seq_Node.copy heap nodes).1 (seq_Node.copy heap nodes).2 := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.shallow_copy_pc3 _ _ _)
  apply Reaches.prepend (Step.shallow_copy_pc2 _ _ _ valid)
  exact Reaches.single (Step.shallow_copy_pc1 _ _ _ (seq_Node.valid_copy heap nodes))

-- The outer sequence is fresh, each element is the same node reference, and
-- every node's field is unchanged. The source copy does not clone the nodes.
theorem shallow_copy_observations (heap : Heap) (nodes : CollectionRef)
    (valid : seq_Node.valid heap nodes) :
    let copied := seq_Node.copy heap nodes
    copied.2 ≠ nodes ∧
      (∀ index, seq_Node.get copied.1 copied.2 index = seq_Node.get heap nodes index) ∧
      (∀ node, field_Node_value copied.1 node = field_Node_value heap node) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · change heap.nextCollection ≠ nodes
    exact Ne.symm (Nat.ne_of_lt valid.1)
  · intro index
    exact seq_Node.get_copy heap nodes index valid
  · intro node
    simp [SequenceType.copy, Heap.createSequence, field_Node_value, is_Node,
      Heap.objectClass, Heap.readField]

-- Main result: Correctness
theorem shallow_copy_output (heap : Heap) (nodes : CollectionRef)
    (valid : seq_Node.valid heap nodes) :
    shallow_copy.Returns (heap, nodes) (seq_Node.copy heap nodes) := by
  have summary := shallow_copy_summary heap nodes valid
  exact ⟨summary.1, summary.2.root⟩

end ObjectSequencesAnalysis
