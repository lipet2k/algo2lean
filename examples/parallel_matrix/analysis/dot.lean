import ParallelMatrixGenerated
import Algo2LeanLib.ParallelMatrix

/-!
Balanced row-by-column reduction over actual nested arrays. Every used outer
lookup is defined and refers to an allocated row. The execution preserves the
entire heap; all accesses are reads, so repeated input row references are safe.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds Algo2Lean.ParallelMatrix

namespace ParallelMatrixDot

private theorem combine_work (l r nl nr : Nat) (hl : l ≤ 64*nl) (hr : r ≤ 64*nr) :
    l+r+22 ≤ 64*(nl+nr+1) := by omega

private theorem combine_span (l r nl nr : Nat) (hl : l ≤ 64*nl) (hr : r ≤ 64*nr) :
    max l r+22 ≤ 64*(max nl nr+1) := by
  have left := Nat.mul_le_mul_left 64 (Nat.le_max_left nl nr)
  have right := Nat.mul_le_mul_left 64 (Nat.le_max_right nl nr)
  omega

/-- A completed call computes the finite dot product, with linear work and
logarithmic span measured on the same heap-preserving execution. -/
theorem call_contract (h : Heap) (a : SeqRef) (b : CollectionRef) (brows : Int → SeqRef)
    (column first : Int) (count : Nat) (validA : a < h.nextRef)
    (view : MatrixView h b first count brows) :
    ∃ cost access,
      parallel_matrix_dot.ParallelCall h (a,b,column,first,↑count) h
        (dot (h.read a) (matrixValues h brows) column first count) cost access ∧
      cost.work ≤ 64 * nodes count ∧ cost.span ≤ 64 * height count ∧
      Access.Within access (dotAccess a b brows first count) := by
  induction count using Nat.strongRecOn generalizing first with
  | ind count ih =>
    by_cases zero : count = 0
    · subst count
      refine ⟨_, _, ⟨⟨validA, view.valid⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.ret
        rfl⟩, ?_, ?_, ?_⟩
      · simp [Cost.seq, Cost.one]
      · simp [Cost.seq, Cost.one]
      · simp [Access.Within, Access.union, Access.empty]
    · by_cases one : count = 1
      · subst count
        have get : seq_Seq_Int.get h b first = some (brows first) := view.get first (by omega) (by omega)
        have validB := view.allocated first (by omega) (by omega)
        refine ⟨_, _, ⟨⟨validA, view.valid⟩, by
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, get, Option.isSome_some, Option.getD_some]
            rw [if_pos ⟨validA, by trivial, validB⟩]
          apply Eval.ret
          simp only [parallelNext, dot_one, matrixValues]
          rfl⟩, ?_, ?_, ?_⟩
        · simp [Cost.seq, Cost.one]
        · simp [Cost.seq, Cost.one]
        · have allowed : Access.Within
              (Access.union (Access.readSeq a first)
                (Access.union (Access.readSeq (brows first) column) (Access.read (.collection b first))))
              (dotAccess a b brows first 1) :=
            Access.Within.union_mono (rowAccess_read a first)
              (Access.Within.union (matrixReadAccess_inner b brows first 1 first column (by omega) (by omega))
                (matrixReadAccess_outer b brows first 1 first (by omega) (by omega)))
          repeat first | exact allowed | exact Access.Within.empty _ | apply Access.Within.union
      · have large : 1 < count := by omega
        have leftView := view.mono first (count/2) (by omega) (by omega)
        have rightView := view.mono (first+↑(count/2)) (count-count/2) (by omega) (by omega)
        obtain ⟨lc, la, left, lw, ls, lr⟩ := ih (count/2) (by omega) first leftView
        obtain ⟨rc, ra, right, rw, rs, rr⟩ :=
          ih (count-count/2) (by omega) (first+↑(count/2)) rightView
        have div : Int.fdiv (↑count) 2 = (↑(count/2) : Int) := (Int.ofNat_fdiv count 2).symm
        have castSub : (↑count : Int)-↑(count/2) = ↑(count-count/2) := by omega
        have positive : ¬ (↑count : Int) ≤ 0 := by omega
        have notOne : (↑count : Int) ≠ 1 := by omega
        have safe := (dotAccess_compatible a a b b brows brows first (first+↑(count/2))
          (count/2) (count-count/2)).of_within lr rr
        refine ⟨_, _, ⟨⟨validA, view.valid⟩, by
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, positive, decide_false] <;> rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, notOne, decide_false] <;> rfl
          repeat (apply Eval.step; · rfl)
          apply Eval.fork
          · rfl
          · simpa only [div] using left.2
          · simpa only [div, castSub] using right.2
          · exact safe
          repeat (apply Eval.step; · rfl)
          apply Eval.ret
          simp only [parallelNext]
          rw [dot_split (h.read a) (matrixValues h brows) column first count (count/2) (by omega)]⟩,
          ?_, ?_, ?_⟩
        · rw [nodes_step count large]
          simpa only [Cost.work_seq, Cost.work_fork, Cost.one, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using
            combine_work lc.work rc.work (nodes (count/2)) (nodes (count-count/2)) lw rw
        · rw [height_step count large]
          simpa only [Cost.span_seq, Cost.span_fork, Cost.one, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using
            combine_span lc.span rc.span (height (count/2)) (height (count-count/2)) ls rs
        · have leftWithin := lr.trans (dotAccess_mono a b brows first first count (count/2) (by omega) (by omega))
          have rightWithin := rr.trans (dotAccess_mono a b brows first (first+↑(count/2)) count
            (count-count/2) (by omega) (by omega))
          repeat first | exact leftWithin | exact rightWithin | exact Access.Within.empty _ | apply Access.Within.union

end ParallelMatrixDot
