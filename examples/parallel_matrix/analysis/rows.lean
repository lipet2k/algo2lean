import columns

/-! Parallel row traversal composes verified column traversals. Output rows
must be distinct physical sequences and separate from all used input rows. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds Algo2Lean.ParallelMatrix
namespace ParallelMatrixRows

/-- The row-by-column product on the assigned rectangle. -/
def Result (before after : Heap) (arows brows outrows : Int → SeqRef)
    (n : Nat) (lo : Int) (count : Nat) : Prop :=
  ∀ i j : Int, lo ≤ i → i < lo+count → 0 ≤ j → j < n →
    after.read (outrows i) j = dot (before.read (arows i)) (matrixValues before brows) j 0 n

private theorem work_combine (n count l r : Nat) (large : 1 < count)
    (hl : l ≤ ((64*nodes n+32)*nodes n+32)*nodes (count/2))
    (hr : r ≤ ((64*nodes n+32)*nodes n+32)*nodes (count-count/2)) :
    l+r+24 ≤ ((64*nodes n+32)*nodes n+32)*nodes count := by
  rw [nodes_step count large,Nat.mul_add,Nat.mul_add,Nat.mul_one]
  omega

private theorem span_combine (n count l r : Nat) (large : 1 < count)
    (hl : l ≤ 32*height (count/2)+96*height n)
    (hr : r ≤ 32*height (count-count/2)+96*height n) :
    max l r+24 ≤ 32*height count+96*height n := by
  rw [height_step count large,Nat.mul_add,Nat.mul_one]
  have a := Nat.le_max_left (height (count/2)) (height (count-count/2))
  have b := Nat.le_max_right (height (count/2)) (height (count-count/2))
  omega

/-- Termination, the matrix product, framing, safe accesses, and balanced-tree
work/span bounds for the same completed row traversal. -/
theorem call_contract (h : Heap) (a b out : CollectionRef) (n : Nat) (lo : Int) (count : Nat)
    (arows brows outrows : Int → SeqRef)
    (va : MatrixView h a 0 n arows) (vb : MatrixView h b 0 n brows)
    (vo : MatrixView h out 0 n outrows)
    (distinct : DistinctRows outrows n) (separate : SeparateRows arows brows outrows n)
    (lower : 0 ≤ lo) (upper : lo+count ≤ n) :
    ∃ final cost access,
      parallel_matrix_rows.ParallelCall h (a,b,out,↑n,lo,↑count) final 0 cost access ∧
      RowsFrame h final outrows lo count n ∧ Result h final arows brows outrows n lo count ∧
      cost.work ≤ ((64*nodes n+32)*nodes n+32)*nodes count ∧
      cost.span ≤ 32*height count+96*height n ∧
      Access.Within access (rowsAccess a b out arows brows outrows n lo count) := by
  induction count using Nat.strongRecOn generalizing h lo with
  | ind count ih =>
    by_cases zero : count = 0
    · subst count
      refine ⟨h, _, _, ⟨⟨va.valid,vb.valid,vo.valid⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.ret
        rfl⟩, RowsFrame.refl _ _ _ _ _, ?_, ?_, ?_, ?_⟩
      · intro i j il ih jl jh; omega
      · simp only [Cost.seq,Cost.one,nodes_zero,Nat.mul_one]
        omega
      · simp only [Cost.seq,Cost.one,height_zero]
        omega
      · simp [Access.Within,Access.union,Access.empty]
    · by_cases one : count = 1
      · subst count
        have validHigh : lo < n := by omega
        have getA : seq_Seq_Int.get h a lo = some (arows lo) := va.get lo lower (by omega)
        have getOut : seq_Seq_Int.get h out lo = some (outrows lo) := vo.get lo lower (by omega)
        obtain ⟨final,cc,ca,run,frame,result,work,span,within⟩ :=
          ParallelMatrixColumns.call_contract h (arows lo) b (outrows lo) n 0 n brows
            (va.allocated lo lower (by omega)) (vo.allocated lo lower (by omega)) vb
            (separate lo lo lower validHigh lower validHigh).1.symm
            (fun i il ih => (separate lo i lower validHigh il ih).2)
        refine ⟨final,_,_,⟨⟨va.valid,vb.valid,vo.valid⟩, by
          repeat (apply Eval.step; · rfl)
          apply Eval.step
          · simp only [parallelNext,getA]; rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext,getOut]; rfl
          repeat (apply Eval.step; · rfl)
          apply Eval.call
          · rfl
          · simpa only [getA,getOut,Option.getD_some] using run.2
          repeat (apply Eval.step; · rfl)
          apply Eval.ret
          rfl⟩, RowsFrame.of_seq outrows lo n frame,?_,?_,?_,?_⟩
        · intro i j il ih jl jh
          have same : i = lo := by omega
          subst i
          exact result j jl (by omega)
        · simp only [Cost.work_seq,Cost.one,nodes_one,Nat.mul_one]
          omega
        · simp only [Cost.span_seq,Cost.one,height_one]
          omega
        · have ac := rowsAccess_outerA a b out arows brows outrows n lo 1 lo lower validHigh
          have oc := rowsAccess_outerOut a b out arows brows outrows n lo 1 lo (by omega) (by omega)
          have cc := within.trans (rowsAccess_columns a b out arows brows outrows n lo 1 lo (by omega) (by omega) lower validHigh)
          repeat first | exact Access.Within.empty _ | exact ac | exact oc | exact cc | apply Access.Within.union
      · have large : 1 < count := by omega
        have ls : count/2 < count := by omega
        have rs : count-count/2 < count := by omega
        obtain ⟨middle,lc,la,left,lf,lresult,lw,lspan,lr⟩ :=
          ih (count/2) ls h lo va vb vo lower (by omega)
        obtain ⟨final,rc,ra,right,rf,rresult,rw,rspan,rr⟩ :=
          ih (count-count/2) rs middle (lo+↑(count/2)) (va.rowsFrame lf) (vb.rowsFrame lf)
            (vo.rowsFrame lf) (by omega) (by omega)
        have safe := (rowsAccess_compatible a b out arows brows outrows n lo (lo+↑(count/2))
          (count/2) (count-count/2) distinct separate lower (by omega) (by omega) (by omega) (by omega)).of_within lr rr
        have div : Int.fdiv (↑count) 2 = (↑(count/2) : Int) := (Int.ofNat_fdiv count 2).symm
        have sub : (↑count : Int)-↑(count/2) = ↑(count-count/2) := by omega
        have positive : ¬ (↑count : Int) ≤ 0 := by omega
        have notOne : (↑count : Int) ≠ 1 := by omega
        refine ⟨final,_,_,⟨⟨va.valid,vb.valid,vo.valid⟩, by
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
          rfl⟩, (lf.weaken (by omega) (by omega)).trans (rf.weaken (by omega) (by omega)), ?_,?_,?_,?_⟩
        · intro i j il ih jl jh
          by_cases before : i < lo+↑(count/2)
          · rw [rf.outside (outrows i) j (Or.inl ?_)]
            · exact lresult i j il before jl jh
            · intro k kl kh equal
              have eq := distinct i k (by omega) (by omega) (by omega) (by omega) equal
              omega
          · rw [rresult i j (by omega) (by omega) jl jh]
            exact dot_rowsFrame lf arows brows i j (by omega) (by omega) lower (by omega) separate
        · simpa only [Cost.work_seq,Cost.work_fork,Cost.one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
            using work_combine n count lc.work rc.work large lw rw
        · simpa only [Cost.span_seq,Cost.span_fork,Cost.one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
            using span_combine n count lc.span rc.span large lspan rspan
        · have lm := lr.trans (rowsAccess_mono a b out arows brows outrows n lo lo (count/2) count (by omega) (by omega))
          have rm := rr.trans (rowsAccess_mono a b out arows brows outrows n (lo+↑(count/2)) lo (count-count/2) count (by omega) (by omega))
          repeat first | exact Access.Within.empty _ | exact lm | exact rm | apply Access.Within.union

end ParallelMatrixRows

namespace ParallelMatrixIntoAnalysis

/-- The complete preallocated entry point preserves every outer collection and
all storage outside the output rectangle. Work and span describe that same call. -/
theorem call_contract (h : Heap) (a b out : CollectionRef) (n : Nat)
    (arows brows outrows : Int → SeqRef)
    (va : MatrixView h a 0 n arows) (vb : MatrixView h b 0 n brows)
    (vo : MatrixView h out 0 n outrows)
    (distinct : DistinctRows outrows n) (separate : SeparateRows arows brows outrows n) :
    ∃ final cost access,
      parallel_matrix_multiply_into.ParallelCall h (a,b,out,↑n) final 0 cost access ∧
      RowsFrame h final outrows 0 n n ∧ ParallelMatrixRows.Result h final arows brows outrows n 0 n ∧
      cost.work ≤ 4096*(n+1)^3 ∧ cost.span ≤ 256*(Nat.log2 n+2) ∧
      Access.Within access (rowsAccess a b out arows brows outrows n 0 n) := by
  obtain ⟨final,cost,access,run,frame,result,work,span,within⟩ :=
    ParallelMatrixRows.call_contract h a b out n 0 n arows brows outrows va vb vo distinct separate (by omega) (by omega)
  refine ⟨final,_,_,⟨⟨va.valid,vb.valid,vo.valid⟩, by
    repeat (apply Eval.step; · rfl)
    apply Eval.call
    · rfl
    · exact run.2
    repeat (apply Eval.step; · rfl)
    apply Eval.ret
    rfl⟩,frame,result,?_,?_,?_⟩
  · simpa only [Cost.work_seq,Cost.one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using Nat.le_trans (Nat.add_le_add_right work 10) (matrix_work_cubic n)
  · simpa only [Cost.span_seq,Cost.one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using Nat.le_trans (Nat.add_le_add_right span 10) (matrix_span_log n)
  · repeat first | exact Access.Within.empty _ | exact within | apply Access.Within.union

-- Main result: Correctness
/-- Every well-formed square input has a terminating source call which stores
its row-by-column product in the preallocated, separate output rows. -/
theorem correctness (h : Heap) (a b out : CollectionRef) (n : Nat)
    (arows brows outrows : Int → SeqRef)
    (va : MatrixView h a 0 n arows) (vb : MatrixView h b 0 n brows)
    (vo : MatrixView h out 0 n outrows)
    (distinct : DistinctRows outrows n) (separate : SeparateRows arows brows outrows n) :
    ∃ final, parallel_matrix_multiply_into.Call h (a,b,out,↑n) final 0 ∧
      RowsFrame h final outrows 0 n n ∧ ParallelMatrixRows.Result h final arows brows outrows n 0 n := by
  obtain ⟨final,cost,access,run,frame,result,_,_,_⟩ :=
    call_contract h a b out n arows brows outrows va vb vo distinct separate
  exact ⟨final,run.call,frame,result⟩

/-- The source-connected frame also gives explicit preservation of every used
input row, even when input rows alias one another. -/
theorem inputs_preserved {h final : Heap} {arows brows outrows : Int → SeqRef} {n : Nat}
    (frame : RowsFrame h final outrows 0 n n) (separate : SeparateRows arows brows outrows n) :
    ∀ i : Int, 0 ≤ i → i < n →
      final.read (arows i) = h.read (arows i) ∧ final.read (brows i) = h.read (brows i) := by
  intro i il ih
  constructor
  · exact frame.read_other _ (fun j jl jh => (separate j i jl (by omega) il ih).1.symm)
  · exact frame.read_other _ (fun j jl jh => (separate j i jl (by omega) il ih).2.symm)

/-- Every completed parallel evaluation satisfies the matrix-product contract. -/
theorem correctness_of_parallel_call (h : Heap) (a b out : CollectionRef) (n : Nat)
    (arows brows outrows : Int → SeqRef)
    (va : MatrixView h a 0 n arows) (vb : MatrixView h b 0 n brows)
    (vo : MatrixView h out 0 n outrows)
    (distinct : DistinctRows outrows n) (separate : SeparateRows arows brows outrows n)
    {final : Heap} {value : Int} {cost : Cost} {access : Access}
    (run : parallel_matrix_multiply_into.ParallelCall h (a,b,out,↑n) final value cost access) :
    value = 0 ∧ RowsFrame h final outrows 0 n n ∧ ParallelMatrixRows.Result h final arows brows outrows n 0 n := by
  obtain ⟨other,measured,accesses,witness,frame,result,_,_,_⟩ :=
    call_contract h a b out n arows brows outrows va vb vo distinct separate
  have equal := witness.2.deterministic run.2
  have valueEqual := Algo2LeanGenerated.Result.fn_parallel_matrix_multiply_into.inj equal.2.1
  exact ⟨valueEqual.symm,by simpa only [equal.1] using frame,by simpa only [equal.1] using result⟩

/-- Concrete bounds include both the row traversal and its public wrapper. -/
theorem running_time_explicit (h : Heap) (a b out : CollectionRef) (n : Nat)
    (arows brows outrows : Int → SeqRef)
    (va : MatrixView h a 0 n arows) (vb : MatrixView h b 0 n brows)
    (vo : MatrixView h out 0 n outrows)
    (distinct : DistinctRows outrows n) (separate : SeparateRows arows brows outrows n)
    {final : Heap} {value : Int} {cost : Cost} {access : Access}
    (run : parallel_matrix_multiply_into.ParallelCall h (a,b,out,↑n) final value cost access) :
    cost.work ≤ 4096*(n+1)^3 ∧ cost.span ≤ 256*(Nat.log2 n+2) := by
  obtain ⟨other,measured,accesses,witness,_,_,work,span,_⟩ :=
    call_contract h a b out n arows brows outrows va vb vo distinct separate
  have equal := run.2.deterministic witness.2
  rw [equal.2.2.1]
  exact ⟨work,span⟩

-- Main result: Running time
/-- A positive uniform constant gives cubic work and logarithmic span for every
nonnegative dimension, including zero and non-power-of-two dimensions. -/
theorem running_time : ∃ C : Nat, 0 < C ∧
    ∀ (h : Heap) (a b out : CollectionRef) (n : Nat) (arows brows outrows : Int → SeqRef),
    MatrixView h a 0 n arows → MatrixView h b 0 n brows → MatrixView h out 0 n outrows →
    DistinctRows outrows n → SeparateRows arows brows outrows n →
    ∀ {final : Heap} {value : Int} {cost : Cost} {access : Access},
    parallel_matrix_multiply_into.ParallelCall h (a,b,out,↑n) final value cost access →
    cost.work ≤ C*(n+1)^3 ∧ cost.span ≤ C*(Nat.log2 n+2) := by
  refine ⟨4096,by decide,?_⟩
  intro h a b out n arows brows outrows va vb vo distinct separate final value cost access run
  have bound := running_time_explicit h a b out n arows brows outrows va vb vo distinct separate run
  exact ⟨bound.1,Nat.le_trans bound.2 (Nat.mul_le_mul_right _ (by decide : 256 ≤ 4096))⟩

end ParallelMatrixIntoAnalysis
