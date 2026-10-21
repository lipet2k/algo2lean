import ParallelNestedGenerated

open Algo2LeanGenerated Algo2LeanParallel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/- The outer collection contains actual row identities. Distinct row indices
need not imply distinct memory: `aliased` intentionally shares one row. -/
def distinctRows : Heap :=
  ({ nextRef := 2 } : Heap).allocateSequence "Seq[Int]"
    (fun i => .seqValue (if i = 0 then 0 else 1))

def aliasedRows : Heap :=
  ({ nextRef := 2 } : Heap).allocateSequence "Seq[Int]" (fun _ => .seqValue 0)

syntax "nested_steps" : tactic
macro_rules
  | `(tactic| nested_steps) => `(tactic| first
    | exact Eval.ret (by rfl)
    | (apply Eval.step (by rfl); nested_steps)
    | (apply Eval.call (by rfl) <;> nested_steps)
    | (apply Eval.fork (by rfl) <;> nested_steps)
    | exact Access.empty_compatible _ rfl
    | (apply Access.Compatible.mk <;> simp_all [Access.union, Access.empty, Access.readSeq, Access.writeSeq,
        Access.read, Access.write, distinctRows, aliasedRows, seq_Seq_Int,
        SequenceType.get, SequenceType.valid, SequenceType.copy, SequenceType.const,
        SequenceType.create, SequenceType.set, Heap.createSequence, Heap.writeElement,
        Heap.allocate, Heap.validSequence, Heap.sequenceType,
        Heap.readElement, Heap.allocateSequence, Heap.read, Heap.write,
        ValueCodec.seq, ObjectValue.asSeq]))

/-- Repeated reads of an aliased row remain valid. -/
theorem shared_nested_reads : ∃ cost access,
    pair_read.ParallelCall aliasedRows (0, 0, 1) aliasedRows (0, 0) cost access := by
  unfold pair_read.ParallelCall pair_read.ValidInput
  exact ⟨_, _, by decide, by nested_steps⟩

/-- Separate allocated row identities permit parallel writes at equal columns. -/
theorem distinct_nested_writes : ∃ cost access,
    pair_write.ParallelCall distinctRows (0, 0, 1)
      (distinctRows.write 0 0 7 |>.write 1 0 8) (7, 8) cost access := by
  unfold pair_write.ParallelCall pair_write.ValidInput
  exact ⟨_, _, by decide, by nested_steps⟩

/-- Two concrete source calls record the same inner cell when outer row slots
alias. Those actual records cannot satisfy the fork independence premise. -/
theorem aliased_writes_conflict : ∃ lc la rc ra,
    put.ParallelCall aliasedRows (0, 0, 0, 7) (aliasedRows.write 0 0 7) 7 lc la ∧
    put.ParallelCall (aliasedRows.write 0 0 7) (0, 1, 0, 8)
      (aliasedRows.write 0 0 7 |>.write 0 0 8) 8 rc ra ∧
    ¬ Access.Compatible la ra := by
  refine ⟨_, _, _, _, ⟨by unfold put.ValidInput; decide, by nested_steps⟩, ⟨by unfold put.ValidInput; decide, by nested_steps⟩, ?_⟩
  intro compatible
  exact (compatible.left_write (.seq 0 0) (by simp only [Access.union, Access.empty, Access.read, Access.writeSeq, Access.write]; decide)).2
    (by simp only [Access.union, Access.empty, Access.read, Access.writeSeq, Access.write]; decide)

/-- Equal row identities still permit disjoint columns; safety is checked at
actual cells, not merely by declaring a whole row exclusively owned. -/
theorem same_row_disjoint_columns : ∃ lc la rc ra,
    put.ParallelCall aliasedRows (0, 0, -2, 7) (aliasedRows.write 0 (-2) 7) 7 lc la ∧
    put.ParallelCall (aliasedRows.write 0 (-2) 7) (0, 1, 4, 8)
      (aliasedRows.write 0 (-2) 7 |>.write 0 4 8) 8 rc ra ∧
    Access.Compatible la ra := by
  refine ⟨_, _, _, _, ⟨by unfold put.ValidInput; decide, by nested_steps⟩,
    ⟨by unfold put.ValidInput; decide, by nested_steps⟩, ?_⟩
  nested_steps

/-- Changing a row pointer conflicts with looking that pointer up, even when
the fetched element belongs to a different ordinary sequence. -/
theorem outer_write_read_conflict : ∃ lc la rc ra,
    replace.ParallelCall distinctRows (0, 0, 1) (seq_Seq_Int.set distinctRows 0 0 1) 0 lc la ∧
    fetch.ParallelCall (seq_Seq_Int.set distinctRows 0 0 1) (0, 0, 0)
      (seq_Seq_Int.set distinctRows 0 0 1) 0 rc ra ∧
    ¬ Access.Compatible la ra := by
  refine ⟨_, _, _, _, ⟨by unfold replace.ValidInput; decide, by nested_steps⟩, ⟨by unfold fetch.ValidInput; decide, by nested_steps⟩, ?_⟩
  intro compatible
  exact (compatible.left_write (.collection 0 0) (by simp only [Access.union, Access.empty, Access.write]; decide)).1
    (by simp only [Access.union, Access.empty, Access.readSeq, Access.read]; decide)

/-- A shallow copy records its fresh outer allocation, so it remains forbidden
inside a fork child. Existing inner rows are shared, rather than copied. -/
theorem copied_rows_allocate : ∃ cost access,
    copy_rows.ParallelCall distinctRows 0 (seq_Seq_Int.copy distinctRows 0).1 1 cost access ∧
    ∀ other, ¬ Access.Compatible access other := by
  refine ⟨_, _, ⟨by unfold copy_rows.ValidInput; decide, by nested_steps⟩, ?_⟩
  intro other compatible
  have impossible : true = false := compatible.left_no_allocation
  cases impossible

/-- Allocation and row replacement before a fork remain available; the generated
ordinary-call bridge checks this complete source path as well. -/
theorem allocated_nested_output : ∃ final cost access,
    fresh.ParallelCall {} () final 1 cost access ∧
    seq_Seq_Int.get final 1 0 = some 0 ∧ seq_Seq_Int.get final 1 1 = some 1 ∧
    final.read 0 0 = 7 ∧ final.read 1 0 = 8 := by
  refine ⟨_, _, _, ⟨True.intro, by
    repeat (apply Eval.step (by rfl))
    apply Eval.call (by rfl)
    · nested_steps
    · repeat (apply Eval.step (by rfl))
      apply Eval.call (by rfl)
      · dsimp only [SequenceType.copy, SequenceType.const, SequenceType.create,
          SequenceType.set, Heap.createSequence, Heap.writeElement, Heap.allocate,
          Heap.allocateSequence, Heap.readElement, seq_Seq_Int, ValueCodec.seq]
        nested_steps
      · nested_steps⟩, ?_, ?_, ?_, ?_⟩ <;> rfl

#print axioms shared_nested_reads
#print axioms distinct_nested_writes
#print axioms aliased_writes_conflict
#print axioms same_row_disjoint_columns
#print axioms outer_write_read_conflict
#print axioms copied_rows_allocate
#print axioms allocated_nested_output
#print axioms fresh.ParallelCall.call
