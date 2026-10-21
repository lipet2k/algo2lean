import ParallelMatrixGenerated
import Algo2LeanLib.ParallelMatrixAllocation

/-! The source allocator creates one distinct zero row at each requested index.
Its linear work and span include the actual sequential allocation instructions. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelMatrix

namespace ParallelMatrixAllocationAnalysis

/-- Termination, the exact allocated heap, and linear same-execution costs.
`Allocation.rows` provides fresh row identities and preserves caller storage. -/
theorem call_contract (h : Heap) (out : CollectionRef) (first : Int) (count : Nat)
    (valid : rowType.valid h out) :
    ∃ cost access,
      matrix_new_rows.ParallelCall h (out,first,↑count)
        (Allocation.rows h out first count) 0 cost access ∧
      cost.work ≤ 32*count+4 ∧ cost.span ≤ 32*count+4 := by
  induction count generalizing h first with
  | zero =>
    refine ⟨_, _, ⟨valid, by
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.ret
      rfl⟩, ?_, ?_⟩ <;> simp [Cost.seq, Cost.one]
  | succ count ih =>
    have nextValid : rowType.valid (Allocation.step h out first) out := by simpa using valid
    obtain ⟨measured, accesses, run, work, span⟩ := ih (Allocation.step h out first) (first+1) nextValid
    have positive : ¬ (↑(count+1) : Int) ≤ 0 := by omega
    have sub : (↑(count+1) : Int)-1 = ↑count := by omega
    refine ⟨_, _, ⟨valid, by
      apply Eval.step
      · rfl
      apply Eval.step
      · simp only [parallelNext, positive, decide_false]; rfl
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.step
      · simp only [parallelNext]
        rw [if_pos (show seq_Seq_Int.valid (h.allocate (fun _ => 0)) out from valid)]
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.call
      · rfl
      · simpa only [sub, Allocation.step, rowType, seq_Seq_Int] using run.2
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.ret
      rfl⟩, ?_, ?_⟩
    · simp only [Cost.work_seq, Cost.one]; omega
    · simp only [Cost.span_seq, Cost.one]; omega

end ParallelMatrixAllocationAnalysis
