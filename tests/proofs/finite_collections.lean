open Algo2LeanCore Algo2LeanGenerated

-- Duplicate literal keys overwrite once; aliases see mutation and deletion.
example : dictionary_updates.Returns () (7, 9, 1, true) := by
  unfold dictionary_updates.Returns
  algo_steps

example : set_updates.Returns () (2, true, false) := by
  unfold set_updates.Returns
  algo_steps

-- A present null value is distinguished from an absent key.
example : nullable_values.Returns () (true, true, false) := by
  unfold nullable_values.Returns
  algo_steps

-- Copy creates a distinct container while retaining shared object identities.
example : shallow_copy.Returns () (9, 1, 2) := by
  unfold shallow_copy.Returns
  algo_steps

example : nested_values.Returns () 1 := by
  unfold nested_values.Returns
  algo_steps

-- Mutating a key object's fields does not change key equality.
example : identity_keys.Returns () (4, true) := by
  unfold identity_keys.Returns
  algo_steps

-- Every literal key and value is evaluated in source order, including duplicates.
example : literal_order.Returns () (1213, 3) := by
  unfold literal_order.Returns
  algo_steps

-- get's default is eagerly evaluated even when the key exists.
example : default_order.Returns () (8, 12) := by
  unfold default_order.Returns
  algo_steps

-- Assignment evaluates the value before the target dictionary and key.
example : assignment_order.Returns () (21, 2) := by
  unfold assignment_order.Returns
  algo_steps

-- Keys are snapshotted once in first-insertion order; mutation changes no current iteration.
example : dictionary_snapshot.Returns () (213, 3) := by
  unfold dictionary_snapshot.Returns
  algo_steps

example : set_snapshot.Returns () (213, 3) := by
  unfold set_snapshot.Returns
  algo_steps

-- A removed then reinserted key moves to the end of the next snapshot.
example : reinsert_order.Returns () 231 := by
  unfold reinsert_order.Returns
  algo_steps

example : snapshot_evaluated_once.Returns () (1, 3) := by
  unfold snapshot_evaluated_once.Returns
  algo_steps

example : nullable_loop.Returns () true := by
  unfold nullable_loop.Returns
  algo_steps

-- Duplicate entries still evaluate every argument once, including its explicit tick.
private def literalHeap : Heap :=
  let initial := (create_Cell ({} : Heap) 0).1
  let first := (set_Cell_value initial 0 1).tick "arguments"
  let second := (set_Cell_value first 0 12).tick "arguments"
  let third := (set_Cell_value second 0 121).tick "arguments"
  let fourth := (set_Cell_value third 0 1213).tick "arguments"
  («dict[Int, Int]».create fourth [(1, 2), (1, 3)]).1

example : literal_order.ReturnsWithCost () (1213, 3)
    (fun name => if name = "arguments" then 4 else 0) := by
  refine ⟨literalHeap, ?_, ?_⟩
  · unfold literalHeap
    algo_steps
  · funext name
    by_cases named : name = "arguments" <;>
      simp [literalHeap, literal_order.load, create_Cell, set_Cell_value,
        DictType.create, Heap.allocateCollection, Heap.cost, Heap.tick, named]

-- The snapshot visits exactly the three original keys, despite insertions/deletions.
private def snapshotHeap : Heap :=
  let initial := («dict[Int, Int]».create ({} : Heap) [(2, 0), (1, 0), (3, 0), (2, 5)]).1
  let changed := «dict[Int, Int]».set («dict[Int, Int]».erase initial 0 1) 0 4 0
  ((changed.tick "visited").tick "visited").tick "visited"

example : dictionary_snapshot.ReturnsWithCost () (213, 3)
    (fun name => if name = "visited" then 3 else 0) := by
  refine ⟨snapshotHeap, ?_, ?_⟩
  · unfold snapshotHeap
    algo_steps
  · funext name
    by_cases named : name = "visited" <;>
      simp [snapshotHeap, dictionary_snapshot.load, Heap.cost, Heap.tick, named]
