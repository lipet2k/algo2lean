open Algo2LeanCore

example : aliases_and_copy.Returns () true := by
  unfold aliases_and_copy.Returns
  algo_steps

example : nested.Returns () 8 := by
  unfold nested.Returns
  algo_steps

example : nested_integers.Returns () 8 := by
  unfold nested_integers.Returns
  algo_steps

example : primitive_sequences.Returns () true := by
  unfold primitive_sequences.Returns
  algo_steps

example : assignment_order.Returns () 123 := by
  unfold assignment_order.Returns
  algo_steps

example : read_order.Returns () 23 := by
  unfold read_order.Returns
  algo_steps

example : contextual.Returns () true := by
  unfold contextual.Returns
  algo_steps

-- Human-built heaps use typed builders, with no raw cell encodings.
def inputNode : Heap × Ref_Node :=
  let slots := seq_Node_optional.const ({} : Heap) none
  create_Node slots.1 6 slots.2

def inputSequence : Heap × CollectionRef :=
  seq_Node.const inputNode.1 inputNode.2

example : identity.Returns inputSequence inputSequence := by
  unfold identity.Returns
  algo_steps

example : «at».Returns (inputSequence.1, inputSequence.2, -9)
    (inputSequence.1, inputNode.2) := by
  unfold «at».Returns
  algo_steps

-- Allocation order matches constructors: the object is allocated before its fields.
def made : Heap × CollectionRef :=
  let heap := set_Node_value (({} : Heap).allocateObject "Node") 0 6
  let slots := seq_Node_optional.const heap none
  let heap := set_Node_children slots.1 0 slots.2
  seq_Node.const heap 0

example : make.ReturnsWithCost 6 made (fun _ => 0) := by
  refine ⟨?_, ?_⟩
  · algo_steps
  · funext name
    rfl

example : make.Returns 6 made := by
  have run : make.ReturnsWithCost 6 made (fun _ => 0) := by
    refine ⟨?_, ?_⟩
    · algo_steps
    · funext name; rfl
  exact run.returns

-- The local observation is independent of reachability or a whole transcript.
theorem replacement_local {before after : Configuration}
    (transition : Step before after) (location : named.At.replace before) :
    named.At.after after ∧ named.Element.values after (-1) = named.Local.node before := by
  cases transition <;>
    simp_all [named.At.replace, named.At.after, named.Element.values,
      named.Local.values, named.Local.node, Config.heap]

-- The shared operation lemma works for arbitrary mathematical heaps/indices.
example (heap : Heap) (values : CollectionRef) (node : Ref_Node) (i : Int)
    (valid : seq_Node.valid heap values) :
    seq_Node.get (seq_Node.set heap values i node) values i = some node := by
  simp [valid]
