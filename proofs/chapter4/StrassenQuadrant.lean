import StrassenHelpers

/-! A square-block copy composes the verified row copier, preserving arbitrary
shared input rows while allocating the result row by row. -/
open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace MatrixStrassenHelpers

private def quadrantPrefix (values : Values) (count : Nat) : Values := fun i j =>
  if 0 ≤ i ∧ i < (count : Int) then values i j else 0

private theorem quadrant_prefix_next (values : Values) (i : Nat) :
    (fun j => if j = (i : Int) then values i else quadrantPrefix values i j) =
      quadrantPrefix values (i + 1) := by
  funext j k
  by_cases same : j = (i : Int)
  · subst j
    simp only
    change values i k = if 0 ≤ (i : Int) ∧ (i : Int) < ((i + 1 : Nat) : Int) then values i k else 0
    rw [if_pos (by omega)]
  · simp only [if_neg same]
    have eqRange : (0 ≤ j ∧ j < (i : Int)) ↔ (0 ≤ j ∧ j < ((i + 1 : Nat) : Int)) := by omega
    simp only [quadrantPrefix, eqRange]

private theorem quadrant_prefix_zero (values : Values) :
    quadrantPrefix values 0 = fun _ _ => 0 := by
  funext i j
  simp only [quadrantPrefix, Int.natCast_zero]
  rw [if_neg (by omega)]


/-- Copy a square block into a fresh nested matrix, preserving all input objects
    and charging exactly one copy for each of its h² entries. -/
theorem quadrant_contract (heap : Heap) (a : CollectionRef) (av : Values)
    (n row col : Int) (h : Nat) (sa : Stored heap a av) (_positive : 0 < h) :
    ∃ after result, matrix_quadrant.Call heap (a, n, (h : Int), row, col) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.quadrantValues n h row col av) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (h * h) name) := by
  -- Internal loop derivations are local to this source-facing contract.
  have quadrantMatrixLoop (remaining : Nat) (base heap : Heap) (s : State_matrix_quadrant)
      (h i : Nat) (av : Values) (bound : s.v2 = (h : Int)) (index : s.v6 = (i : Int))
      (finish : i + remaining = h) (sa : Stored base s.v0 av)
      (frame : Extends base heap) (fresh : base.nextCollection ≤ s.v5)
      (stored : Stored heap s.v5 (quadrantPrefix (fun r c =>
        if 0 ≤ c ∧ c < (h : Int) then av (s.v3 + r) (s.v4 + c) else 0) i)) :
      ∃ after, Summary Step heap (.fn_matrix_quadrant 4 s) after (.fn_matrix_quadrant s.v5) ∧
        Extends base after ∧ Stored after s.v5 (StrassenValues.quadrantValues s.v1 h s.v3 s.v4 av) ∧
        (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (remaining * h) name) := by
    induction remaining generalizing heap s i with
    | zero =>
      have ieq : i = h := by omega
      subst i
      refine ⟨heap, ?_, frame, ?_, ?_⟩
      · intro stack
        apply Reaches.prepend (Step.matrix_quadrant_pc4 ..)
        apply Reaches.prepend (Step.matrix_quadrant_pc3_false _ _ _ (by simp [bound, index]))
        apply Reaches.prepend (Step.matrix_quadrant_pc2 ..)
        exact Reaches.single (Step.matrix_quadrant_pc1 _ _ _ stored.1)
      · have eqValues : quadrantPrefix (fun r c => if 0 ≤ c ∧ c < (h : Int)
            then av (s.v3 + r) (s.v4 + c) else 0) h =
            StrassenValues.quadrantValues s.v1 h s.v3 s.v4 av := by
          funext r c
          simp only [quadrantPrefix, StrassenValues.quadrantValues]
          grind
        rw [eqValues] at stored
        exact stored
      · intro name; simp [Clocks.single]
    | succ remaining ih =>
      have ai := sa.mono frame
      obtain ⟨one, row, rowRun, rowFrame, rowValid, rowFresh, rowValue, rowClocks⟩ :=
        quadrant_row_contract heap ((rows.get heap s.v0 (s.v3 + s.v6)).getD 0) h s.v4
          (ai.row_valid (s.v3 + s.v6))
      let nextHeap := rows.set one s.v5 s.v6 row
      let next : State_matrix_quadrant := { s with v6 := s.v6 + 1, t8 := decide (s.v6 < s.v2), t9 := row, t10 := s.v6, t11 := s.v5, t12 := (rows.get heap s.v0 (s.v3 + s.v6)).getD 0, t13 := s.v2, t14 := s.v4 }
      have nextFrame : Extends base nextHeap := (frame.trans rowFrame).set s.v5 fresh s.v6 row
      have nextStored : Stored nextHeap next.v5 (quadrantPrefix (fun r c =>
          if 0 ≤ c ∧ c < (h : Int) then av (next.v3 + r) (next.v4 + c) else 0) (i + 1)) := by
        have st := (stored.mono rowFrame).set s.v6 row _ rowValid rowValue
        have rowEq : (fun c => if 0 ≤ c ∧ c < (h : Int) then
            heap.read ((rows.get heap s.v0 (s.v3 + s.v6)).getD 0) (s.v4 + c) else 0) =
            (fun c => if 0 ≤ c ∧ c < (h : Int) then av (s.v3 + (i : Int)) (s.v4 + c) else 0) := by
          funext c; rw [ai.read, index]
        rw [rowEq, index, quadrant_prefix_next
          (fun r c => if 0 ≤ c ∧ c < (h : Int) then av (s.v3 + r) (s.v4 + c) else 0) i] at st
        simpa only [nextHeap, next, index] using st
      obtain ⟨after, completed, afterFrame, afterStored, afterClocks⟩ :=
        ih nextHeap next (i + 1) bound (by dsimp [next]; omega) (by omega) sa nextFrame fresh nextStored
      refine ⟨after, ?_, afterFrame, afterStored, ?_⟩
      · intro stack
        apply Reaches.prepend (Step.matrix_quadrant_pc4 ..)
        apply Reaches.prepend (Step.matrix_quadrant_pc3_true _ _ _ (by simp [bound, index]; omega))
        apply Reaches.prepend (Step.matrix_quadrant_pc12 _ _ _ (by exact ai.row (s.v3 + s.v6)))
        apply Reaches.prepend (Step.matrix_quadrant_pc11 ..)
        apply Reaches.prepend (Step.matrix_quadrant_pc10 ..)
        apply Reaches.prepend (Step.matrix_quadrant_pc9 ..)
        simp only [bound]
        apply Reaches.trans (rowRun.2 _)
        apply Reaches.prepend (Step.matrix_quadrant_pc8 ..)
        apply Reaches.prepend (Step.matrix_quadrant_pc7 ..)
        apply Reaches.prepend (Step.matrix_quadrant_pc6 _ _ _ (by exact rowFrame.valid stored.1))
        apply Reaches.prepend (Step.matrix_quadrant_pc5 ..)
        simpa only [next, nextHeap, bound, show seq_Seq_Int = rows from rfl] using completed stack
      · intro name
        rw [afterClocks]
        change one.clocks name + _ = _
        rw [rowClocks]
        by_cases same : name = "copied_cells" <;> simp [Clocks.single, same, Nat.add_mul] <;> omega
  let initialized := (rows.const (heap.allocate (fun _ => 0)) heap.nextRef).1
  have frame : Extends heap initialized := (extends_allocate heap _).trans (extends_const _ _)
  have stored : Stored initialized heap.nextCollection (fun _ _ => 0) :=
    stored_const (heap.allocate (fun _ => 0)) heap.nextRef _ (Nat.lt_succ_self _) (by simp [Heap.allocate])
  let state : State_matrix_quadrant := { v0 := a, v1 := n, v2 := h, v3 := row, v4 := col, v5 := heap.nextCollection, t15 := heap.nextCollection, t16 := heap.nextRef }
  obtain ⟨after, completed, afterFrame, afterStored, afterClocks⟩ :=
    quadrantMatrixLoop h heap initialized state h 0 av rfl rfl (by omega) sa frame (Nat.le_refl _)
      (by simpa only [state, quadrant_prefix_zero] using stored)
  refine ⟨after, heap.nextCollection, ⟨sa.1, ?_⟩, afterFrame, afterStored, afterClocks⟩
  intro stack
  apply Reaches.prepend (Step.matrix_quadrant_pc17 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc16 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc15 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc14 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc13 ..)
  exact completed stack

end MatrixStrassenHelpers
