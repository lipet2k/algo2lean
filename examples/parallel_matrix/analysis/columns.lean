import dot
import Algo2LeanLib.ParallelMatrixAccess

/-! Parallel output columns reuse the verified parallel dot product. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds Algo2Lean.ParallelMatrix
namespace ParallelMatrixColumns

/-- The only facts about the dot-product source required by the column traversal. -/
def VerifiedDot : Prop := ∀ (h : Heap) (a : SeqRef) (b : CollectionRef) (column first : Int)
    (count : Nat) (brows : Int → SeqRef), a < h.nextRef → MatrixView h b first count brows →
    ∃ cost access,
      parallel_matrix_dot.ParallelCall h (a,b,column,first,↑count) h
        (dot (h.read a) (matrixValues h brows) column first count) cost access ∧
      cost.work ≤ 64 * nodes count ∧ cost.span ≤ 64 * height count ∧
      Access.Within access (dotAccess a b brows first count)

/-- Exact values of the completed output-column interval. -/
def Result (before after : Heap) (a out : SeqRef) (brows : Int → SeqRef)
    (n : Nat) (lo : Int) (count : Nat) : Prop :=
  ∀ j, lo ≤ j → j < lo+count →
    after.read out j = dot (before.read a) (matrixValues before brows) j 0 n

private theorem work_combine (n count l r : Nat) (large : 1 < count)
    (hl : l ≤ (64*nodes n+32)*nodes (count/2))
    (hr : r ≤ (64*nodes n+32)*nodes (count-count/2)) :
    l+r+24 ≤ (64*nodes n+32)*nodes count := by
  rw [nodes_step count large, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

private theorem span_combine (n count l r : Nat) (large : 1 < count)
    (hl : l ≤ 32*height (count/2)+64*height n)
    (hr : r ≤ 32*height (count-count/2)+64*height n) :
    max l r+24 ≤ 32*height count+64*height n := by
  rw [height_step count large, Nat.mul_add, Nat.mul_one]
  have a := Nat.le_max_left (height (count/2)) (height (count-count/2))
  have b := Nat.le_max_right (height (count/2)) (height (count-count/2))
  omega

/-- The traversal modifies only its assigned output interval; correctness and
costs refer to that same source execution. -/
theorem from_dot (dotContract : VerifiedDot)
    (h : Heap) (a : SeqRef) (b : CollectionRef) (out : SeqRef) (n : Nat)
    (lo : Int) (count : Nat) (brows : Int → SeqRef)
    (ha : a < h.nextRef) (ho : out < h.nextRef) (vb : MatrixView h b 0 n brows)
    (different : a ≠ out) (bDifferent : ∀ i : Int, 0 ≤ i → i < n → out ≠ brows i) :
    ∃ final cost access,
      parallel_matrix_columns.ParallelCall h (a,b,out,↑n,lo,↑count) final 0 cost access ∧
      SeqFrame h final out lo count ∧ Result h final a out brows n lo count ∧
      cost.work ≤ (64*nodes n+32)*nodes count ∧
      cost.span ≤ 32*height count+64*height n ∧
      Access.Within access (columnsAccess a b out brows n lo count) := by
  induction count using Nat.strongRecOn generalizing h lo with
  | ind count ih =>
    by_cases zero : count = 0
    · subst count
      refine ⟨h, _, _, ⟨⟨ha, vb.valid, ho⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.ret
        rfl⟩, SeqFrame.refl _ _ _ _, ?_, ?_, ?_, ?_⟩
      · intro j jl jh; omega
      · simp [Cost.seq,Cost.one]
      · simp only [Cost.seq,Cost.one,height_zero]
        omega
      · simp [Access.Within,Access.union,Access.empty]
    · by_cases one : count = 1
      · subst count
        obtain ⟨dc, da, run, dw, ds, dr⟩ := dotContract h a b lo 0 n brows ha vb
        refine ⟨h.write out lo (dot (h.read a) (matrixValues h brows) lo 0 n), _, _,
          ⟨⟨ha,vb.valid,ho⟩, by
          repeat (apply Eval.step; · rfl)
          apply Eval.call
          · rfl
          · exact run.2
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext]; rw [if_pos ho]
          apply Eval.step
          · rfl
          apply Eval.ret
          rfl⟩, SeqFrame.write h out lo 1 lo _ (by omega) (by omega), ?_, ?_, ?_, ?_⟩
        · intro j jl jh
          have same : j = lo := by omega
          subst j
          simp [Heap.read,Heap.write]
        · simp only [Cost.work_seq,Cost.one,nodes_one]
          omega
        · simp only [Cost.span_seq,Cost.one,height_one]
          omega
        · have dd := dr.trans (columnsAccess_dot a b out brows n lo 1)
          have wr := columnsAccess_write a b out brows n lo lo 1 (by omega) (by omega)
          repeat first | apply Access.Within.union | exact Access.Within.empty _ | exact dd | exact wr
      · have large : 1 < count := by omega
        have ls : count/2 < count := by omega
        have rs : count-count/2 < count := by omega
        obtain ⟨middle, lc, la, left, lf, lresult, lw, lspan, lr⟩ :=
          ih (count/2) ls h lo ha ho vb
        have ma : a < middle.nextRef := by rw [lf.nextRef]; exact ha
        have mo : out < middle.nextRef := by rw [lf.nextRef]; exact ho
        obtain ⟨final, rc, ra, right, rf, rresult, rw, rspan, rr⟩ :=
          ih (count-count/2) rs middle (lo+↑(count/2)) ma mo (vb.seqFrame lf)
        have safe := (columnsAccess_compatible a b out brows n lo (lo+↑(count/2))
          (count/2) (count-count/2) different bDifferent (by omega)).of_within lr rr
        have div : Int.fdiv (↑count) 2 = (↑(count/2) : Int) := (Int.ofNat_fdiv count 2).symm
        have sub : (↑count : Int)-↑(count/2) = ↑(count-count/2) := by omega
        have positive : ¬ (↑count : Int) ≤ 0 := by omega
        have notOne : (↑count : Int) ≠ 1 := by omega
        refine ⟨final, _, _, ⟨⟨ha,vb.valid,ho⟩, by
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext,positive,decide_false]; rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext,notOne,decide_false]; rfl
          repeat (apply Eval.step; · rfl)
          apply Eval.fork
          · rfl
          · simpa only [div] using left.2
          · simpa only [div,sub] using right.2
          · exact safe
          repeat (apply Eval.step; · rfl)
          apply Eval.ret
          rfl⟩, (lf.weaken (by omega) (by omega)).trans (rf.weaken (by omega) (by omega)), ?_, ?_, ?_, ?_⟩
        · intro j jl jh
          by_cases before : j < lo+↑(count/2)
          · rw [rf.outside out j (Or.inr (Or.inl before))]
            exact lresult j jl before
          · rw [rresult j (by omega) (by omega)]
            exact dot_seqFrame lf a brows j n different bDifferent
        · simpa only [Cost.work_seq,Cost.work_fork,Cost.one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
            using work_combine n count lc.work rc.work large lw rw
        · simpa only [Cost.span_seq,Cost.span_fork,Cost.one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
            using span_combine n count lc.span rc.span large lspan rspan
        · have lm := lr.trans (columnsAccess_mono a b out brows n lo lo (count/2) count (by omega) (by omega))
          have rm := rr.trans (columnsAccess_mono a b out brows n (lo+↑(count/2)) lo (count-count/2) count (by omega) (by omega))
          repeat first | apply Access.Within.union | exact Access.Within.empty _ | exact lm | exact rm

/-- Reuse the proved dot-product implementation for a complete column traversal. -/
theorem call_contract
    (h : Heap) (a : SeqRef) (b : CollectionRef) (out : SeqRef) (n : Nat)
    (lo : Int) (count : Nat) (brows : Int → SeqRef)
    (ha : a < h.nextRef) (ho : out < h.nextRef) (vb : MatrixView h b 0 n brows)
    (different : a ≠ out) (bDifferent : ∀ i : Int, 0 ≤ i → i < n → out ≠ brows i) :
    ∃ final cost access,
      parallel_matrix_columns.ParallelCall h (a,b,out,↑n,lo,↑count) final 0 cost access ∧
      SeqFrame h final out lo count ∧ Result h final a out brows n lo count ∧
      cost.work ≤ (64*nodes n+32)*nodes count ∧
      cost.span ≤ 32*height count+64*height n ∧
      Access.Within access (columnsAccess a b out brows n lo count) := by
  apply from_dot _ h a b out n lo count brows ha ho vb different bDifferent
  intro h a b column first count brows ha vb
  exact ParallelMatrixDot.call_contract h a b brows column first count ha vb

end ParallelMatrixColumns
