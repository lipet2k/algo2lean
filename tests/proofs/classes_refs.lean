-- A cyclic reference and an ordinary alias observe the same mutable object.
-- Nested sequence assignment also retains the sequence identity in the field.
example : aliased_cycle.Returns () 82 := by
  unfold aliased_cycle.Returns
  algo_steps

example : nullable_identity.Returns () true := by
  unfold nullable_identity.Returns
  algo_steps

-- An initialized null field is readable; a missing field has no value.
example : initialized_null.Returns () true := by
  unfold initialized_null.Returns
  algo_steps

example : field_Empty_next (({} : Heap).allocateObject "Empty") 0 = none := by
  decide

example : field_Empty_next
    (set_Empty_next (({} : Heap).allocateObject "Empty") 0 none) 0 = some none := by
  decide

example : choose_node.Returns false (({} : Heap), none) := by
  unfold choose_node.Returns
  algo_steps

def chosenNode := create_Node (({} : Heap).allocate (fun _ => 7)) 7 none 0

example : choose_node.Returns true (chosenNode.1, some chosenNode.2) := by
  unfold choose_node.Returns
  algo_steps

example : nullable_calls.Returns () 10 := by
  unfold nullable_calls.Returns
  algo_steps

-- The output interface exposes the heap needed to use a returned object.
def inputNode := create_Node (({} : Heap).allocate (fun _ => 9)) 9 none 0

example : identity.Returns inputNode inputNode := by
  unfold identity.Returns
  algo_steps

example : node_value.Returns inputNode 9 := by
  unfold node_value.Returns
  algo_steps

example : field_Node_value inputNode.1 inputNode.2 = some 9 := by
  decide
