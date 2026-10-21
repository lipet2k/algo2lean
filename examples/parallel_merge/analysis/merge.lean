import ParallelMergeGenerated
import Algo2LeanLib.ParallelMergeSpec
import Algo2LeanLib.ParallelMergeAccess
import Algo2LeanLib.ParallelMergeCost
import binary_search

/-!
CLRS §26.3 parallel merging, connected to the generated fork–join execution.
The two sorted input slices may overlap; the output sequence is distinct.
Every input multiplicity is retained, including repeated equal keys.
-/
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelMerge

namespace ParallelMergeAnalysis

private theorem combine_work (a b c A B C D : Nat) (ha : a ≤ A) (hb : b ≤ B)
    (hc : c ≤ C) (bound : A+B+C+40 ≤ D) : a+b+c+40 ≤ D := by omega

private theorem combine_span (a b c A B C D : Nat) (ha : a ≤ A) (hb : b ≤ B)
    (hc : c ≤ C) (bound : max A B+C+40 ≤ D) : max a b+c+40 ≤ D := by
  have both : max a b ≤ max A B := Nat.max_le.mpr
    ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩
  omega

/-- Reuse arbitrary valid work/span recurrence bounds while verifying the actual
source execution. The constant overhead includes the larger-slice swap and fork.
All source calls, reads, and writes are retained by this contract. -/
theorem merge_contract_with_bounds (W S : Nat → Nat)
    (work0 : 12 ≤ W 0) (span0 : 12 ≤ S 0)
    (workStep : ∀ m n j : Nat, 0 < m → n ≤ m → j ≤ n →
      W (m/2+j) + W (m-m/2-1+(n-j)) + 32*(Nat.log2 (n+1)+1)+40 ≤ W (m+n))
    (spanStep : ∀ m n j : Nat, 0 < m → n ≤ m → j ≤ n →
      max (S (m/2+j)) (S (m-m/2-1+(n-j))) + 32*(Nat.log2 (n+1)+1)+40 ≤ S (m+n))
    (h : Heap) (a out : SeqRef) (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat) (dst : Int)
    (ha : a < h.nextRef) (ho : out < h.nextRef) (different : a ≠ out)
    (firstSorted : (interval (h.read a) lo1 m).Pairwise (· ≤ ·))
    (secondSorted : (interval (h.read a) lo2 n).Pairwise (· ≤ ·)) :
    ∃ final cost access,
      p_merge.ParallelCall h (a, lo1, ↑m, lo2, ↑n, out, dst) final 0 cost access ∧
      SeqFrame h final out dst (m+n) ∧
      MergeResult (interval (h.read a) lo1 m) (interval (h.read a) lo2 n)
        (interval (final.read out) dst (m+n)) ∧
      cost.work ≤ W (m+n) ∧ cost.span ≤ S (m+n) ∧
      Access.Within access (mergeAccess a out lo1 m lo2 n dst) := by
  generalize size : m+n = total
  induction total using Nat.strongRecOn generalizing h lo1 m lo2 n dst with
  | ind total ih =>
    have body (m n : Nat) (lo1 lo2 : Int) (size : m+n = total) (order : n ≤ m)
        (firstSorted : (interval (h.read a) lo1 m).Pairwise (· ≤ ·))
        (secondSorted : (interval (h.read a) lo2 n).Pairwise (· ≤ ·)) (s : State_p_merge) :
        ∃ final cost access,
          Eval parallelNext h (Frame.fn_p_merge 34
            {s with v0 := a, v1 := lo1, v2 := ↑m, v3 := lo2, v4 := ↑n, v5 := out, v6 := dst})
            final (Result.fn_p_merge 0) cost access ∧
          SeqFrame h final out dst (m+n) ∧
          MergeResult (interval (h.read a) lo1 m) (interval (h.read a) lo2 n)
            (interval (final.read out) dst (m+n)) ∧
          cost.work + 8 ≤ W (m+n) ∧ cost.span + 8 ≤ S (m+n) ∧
          Access.Within access (mergeAccess a out lo1 m lo2 n dst) := by
      by_cases empty : m = 0
      · have emptyN : n = 0 := by omega
        subst m; subst n
        refine ⟨h, _, _, by
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          exact Eval.ret rfl,
          SeqFrame.refl _ _ _ _, ?_, ?_, ?_, ?_⟩
        · simp [MergeResult, interval]
        · simpa [Cost.seq, Cost.one] using work0
        · simpa [Cost.seq, Cost.one] using span0
        · simp [Access.Within, Access.union, Access.empty]
      · have positive : 0 < m := by omega
        have halfSmall : m/2 < m := by omega
        obtain ⟨j, bc, ba, binary, lower, bw, bs, br⟩ :=
          ParallelMergeSearch.call_contract h a lo2 n (h.read a (lo1 + ↑(m/2))) ha secondSorted
        have jBound : j ≤ n := lower.1
        let pivot := h.read a (lo1 + ↑(m/2))
        let pivotIndex := dst + ↑(m/2) + ↑j
        let written := h.write out pivotIndex pivot
        have wrote : SeqFrame h written out dst (m+n) :=
          SeqFrame.write h out dst (m+n) pivotIndex pivot (by dsimp [pivotIndex]; omega)
            (by dsimp [pivotIndex]; omega)
        have sourceWritten : written.read a = h.read a := wrote.read_other different
        have leftSmall : m/2+j < total := by omega
        have rightSmall : m-m/2-1+(n-j) < total := by omega
        have leftFirst : (interval (written.read a) lo1 (m/2)).Pairwise (· ≤ ·) := by
          rw [sourceWritten]
          simpa using sorted_subinterval (h.read a) lo1 m 0 (m/2) firstSorted (by omega)
        have leftSecond : (interval (written.read a) lo2 j).Pairwise (· ≤ ·) := by
          rw [sourceWritten]
          simpa using sorted_subinterval (h.read a) lo2 n 0 j secondSorted (by omega)
        obtain ⟨middle, lc, la, left, lf, lm, lw, ls, lr⟩ :=
          ih (m/2+j) leftSmall written lo1 (m/2) lo2 j dst ha ho leftFirst leftSecond rfl
        have sourceMiddle : middle.read a = h.read a :=
          (lf.read_other different).trans sourceWritten
        have ma : a < middle.nextRef := by rw [lf.nextRef]; exact ha
        have mo : out < middle.nextRef := by rw [lf.nextRef]; exact ho
        have rightFirst : (interval (middle.read a) (lo1+↑(m/2)+1) (m-m/2-1)).Pairwise (· ≤ ·) := by
          rw [sourceMiddle]
          have sorted := sorted_subinterval (h.read a) lo1 m (m/2+1) (m-m/2-1) firstSorted (by omega)
          simpa [Int.natCast_add, Int.add_assoc] using sorted
        have rightSecond : (interval (middle.read a) (lo2+↑j) (n-j)).Pairwise (· ≤ ·) := by
          rw [sourceMiddle]
          exact sorted_subinterval (h.read a) lo2 n j (n-j) secondSorted (by omega)
        obtain ⟨final, rc, ra, right, rf, rm, rw, rs, rr⟩ :=
          ih (m-m/2-1+(n-j)) rightSmall middle (lo1+↑(m/2)+1) (m-m/2-1)
            (lo2+↑j) (n-j) (pivotIndex+1) ma mo rightFirst rightSecond rfl
        rw [sourceWritten] at lm
        rw [sourceMiddle] at rm
        have finalFrame := (wrote.trans (lf.weaken (by omega) (by omega))).trans
          (rf.weaken (by dsimp [pivotIndex]; omega) (by dsimp [pivotIndex]; omega))
        have sameLeft : interval (final.read out) dst (m/2+j) =
            interval (middle.read out) dst (m/2+j) := by
          apply interval_congr
          intro i low high
          apply rf.outside
          right; left
          dsimp [pivotIndex]; omega
        have finalPivot : final.read out pivotIndex = pivot := by
          rw [rf.outside out pivotIndex (Or.inr (Or.inl (by omega))),
            lf.outside out pivotIndex (Or.inr (Or.inr (by dsimp [pivotIndex]; omega)))]
          simp [written, Heap.read, Heap.write]
        have merged := merge_slices (h.read a) lo1 lo2 m n (m/2) j
          (interval (middle.read out) dst (m/2+j))
          (interval (final.read out) (pivotIndex+1) (m-m/2-1+(n-j)))
          halfSmall firstSorted lower lm rm
        have splitOutput := interval_pivot (final.read out) dst (m+n) (m/2+j) (by omega)
        have rightLength : m+n-(m/2+j)-1 = m-m/2-1+(n-j) := by omega
        have output : MergeResult (interval (h.read a) lo1 m) (interval (h.read a) lo2 n)
            (interval (final.read out) dst (m+n)) := by
          rw [splitOutput, rightLength, sameLeft]
          simp only [Int.natCast_add, ← Int.add_assoc]
          change MergeResult _ _ (interval (middle.read out) dst (m/2+j) ++
            final.read out pivotIndex :: interval (final.read out) (pivotIndex+1) (m-m/2-1+(n-j)))
          rw [finalPivot]
          exact merged
        have safe := (mergeAccess_compatible a out lo1 lo2 dst (lo1+↑(m/2)+1) (lo2+↑j)
          (pivotIndex+1) (m/2) j (m-m/2-1) (n-j) different
          (by dsimp [pivotIndex]; omega)).of_within lr rr
        have division : Int.fdiv (↑m) 2 = (↑(m/2) : Int) := (Int.ofNat_fdiv m 2).symm
        have rightM : (↑m : Int) - ↑(m/2) - 1 = ↑(m-m/2-1) := by omega
        have rightN : (↑n : Int) - ↑j = ↑(n-j) := by omega
        have notEmpty : ¬ (↑m : Int) ≤ 0 := by omega
        refine ⟨final, _, _, by
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, notEmpty, decide_false]; rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext]; rw [if_pos ha]
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.call
          · rfl
          · simpa only [division] using binary.2
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext]; rw [if_pos ho]
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.fork
          · rfl
          · simpa only [division] using left.2
          · simpa only [division, rightM, rightN] using right.2
          · exact safe
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          exact Eval.ret rfl,
          finalFrame, output, ?_, ?_, ?_⟩
        · simp only [Cost.work_seq, Cost.work_fork, Cost.one]
          have bound := combine_work lc.work rc.work bc.work _ _ _ _ lw rw bw
            (workStep m n j positive order jBound)
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
        · simp only [Cost.span_seq, Cost.span_fork, Cost.one]
          have bound := combine_span lc.span rc.span bc.span _ _ _ _ ls rs bs
            (spanStep m n j positive order jBound)
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
        · have rd := mergeAccess_read_left a out lo1 m lo2 n dst (lo1+↑(m/2)) (by omega) (by omega)
          have sr := br.trans (readInterval_within_mergeAccess a out lo1 m lo2 n dst)
          have wr := mergeAccess_write a out lo1 m lo2 n dst pivotIndex (by dsimp [pivotIndex]; omega)
            (by dsimp [pivotIndex]; omega)
          have la' := lr.trans (mergeAccess_mono a out lo1 lo2 dst lo1 lo2 dst (m/2) j m n
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
          have ra' := rr.trans (mergeAccess_mono a out (lo1+↑(m/2)+1) (lo2+↑j) (pivotIndex+1)
            lo1 lo2 dst (m-m/2-1) (n-j) m n
            (by omega) (by omega) (by omega) (by omega)
            (by dsimp [pivotIndex]; omega) (by dsimp [pivotIndex]; omega))
          simp only [division]
          repeat first
            | apply Access.Within.union
            | exact Access.Within.empty _
            | exact rd
            | exact sr
            | exact wr
            | exact la'
            | exact ra'
    subst total
    by_cases swap : m < n
    · obtain ⟨final, cost, access, run, frame, result, work, span, within⟩ :=
        body n m lo2 lo1 (by omega) (by omega) secondSorted firstSorted {v7 := lo1, v8 := ↑m, t39 := true}
      refine ⟨final, _, _, ⟨⟨ha, ho⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · simp only [parallelNext, show (↑m : Int) < ↑n by omega, decide_true]; rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        exact run⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [Nat.add_comm] using frame
      · simpa only [Nat.add_comm] using result.swap
      · simpa only [Cost.work_seq, Cost.one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using work
      · simpa only [Cost.span_seq, Cost.one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using span
      · have same : Access.Within access (mergeAccess a out lo1 m lo2 n dst) := by
          rw [mergeAccess_swap]
          exact within
        repeat first | apply Access.Within.union | exact Access.Within.empty _ | exact same
    · obtain ⟨final, cost, access, run, frame, result, work, span, within⟩ :=
        body m n lo1 lo2 rfl (by omega) firstSorted secondSorted {}
      refine ⟨final, _, _, ⟨⟨ha, ho⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · simp only [parallelNext, show ¬ (↑m : Int) < ↑n by omega, decide_false]; rfl
        exact run⟩, frame, result, ?_, ?_, ?_⟩
      · simp only [Cost.work_seq, Cost.one]; omega
      · simp only [Cost.span_seq, Cost.one]; omega
      · repeat first | apply Access.Within.union | exact Access.Within.empty _ | exact within

/-- Complete reusable CLRS parallel-merge contract. The output is sorted and
has exactly the two input multisets. Only its prescribed output slice changes;
work is linear and span is quadratic in the logarithm of the total length. -/
theorem merge_contract
    (h : Heap) (a out : SeqRef) (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat) (dst : Int)
    (ha : a < h.nextRef) (ho : out < h.nextRef) (different : a ≠ out)
    (firstSorted : (interval (h.read a) lo1 m).Pairwise (· ≤ ·))
    (secondSorted : (interval (h.read a) lo2 n).Pairwise (· ≤ ·)) :
    ∃ final cost access,
      p_merge.ParallelCall h (a, lo1, ↑m, lo2, ↑n, out, dst) final 0 cost access ∧
      SeqFrame h final out dst (m+n) ∧
      MergeResult (interval (h.read a) lo1 m) (interval (h.read a) lo2 n)
        (interval (final.read out) dst (m+n)) ∧
      cost.work ≤ 1024*(m+n+1) ∧ cost.span ≤ 4096*(Nat.log2 (m+n+1)+1)^2 ∧
      Access.Within access (mergeAccess a out lo1 m lo2 n dst) := by
  obtain ⟨final, cost, access, run, frame, result, work, span, within⟩ :=
    merge_contract_with_bounds mergeWork mergeSpan mergeWork_base mergeSpan_base
      mergeWork_step mergeSpan_step h a out lo1 m lo2 n dst ha ho different firstSorted secondSorted
  exact ⟨final, cost, access, run, frame, result,
    Nat.le_trans work (mergeWork_linear _), Nat.le_trans span (mergeSpan_quadratic _), within⟩

end ParallelMergeAnalysis
