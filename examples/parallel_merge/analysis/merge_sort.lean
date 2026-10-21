import merge
import Algo2LeanLib.ParallelMergeSpec
import Algo2LeanLib.ParallelSortAccess
import Algo2LeanLib.ParallelSortCost

/-!
Parallel merge sort reuses the full parallel-merge contract. Two preallocated
buffers alternate roles; siblings modify disjoint intervals of both buffers.
The original input, unrelated storage, and counters remain unchanged.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelMerge

namespace ParallelMergeSortAnalysis

private theorem work_combine (n l r m : Nat) (large : 1 < n)
    (hl : l ≤ sortWork (n/2)) (hr : r ≤ sortWork (n-n/2))
    (hm : m ≤ 1024*(n+1)) : l+r+m+31 ≤ sortWork n := by
  rw [sortWork_step n large]
  omega

private theorem span_combine (n l r m : Nat) (large : 1 < n)
    (hl : l ≤ sortSpan (n/2)) (hr : r ≤ sortSpan (n-n/2))
    (hm : m ≤ 4096*(Nat.log2 (n+1)+1)^2) : max l r+m+31 ≤ sortSpan n := by
  rw [sortSpan_step n large]
  have lm := Nat.le_trans hl (Nat.le_max_left (sortSpan (n/2)) (sortSpan (n-n/2)))
  have rm := Nat.le_trans hr (Nat.le_max_right (sortSpan (n/2)) (sortSpan (n-n/2)))
  omega

/-- The merge interface consumed by the sort proof: same-execution result,
frame, access permissions, and cost bounds. -/
def VerifiedMerge : Prop := ∀ (h : Heap) (a out : SeqRef) (lo1 lo2 dst : Int) (m n : Nat),
  a < h.nextRef → out < h.nextRef → a ≠ out →
  (interval (h.read a) lo1 m).Pairwise (· ≤ ·) →
  (interval (h.read a) lo2 n).Pairwise (· ≤ ·) →
  ∃ final cost access,
    p_merge.ParallelCall h (a, lo1, ↑m, lo2, ↑n, out, dst) final 0 cost access ∧
    SeqFrame h final out dst (m+n) ∧
    MergeResult (interval (h.read a) lo1 m) (interval (h.read a) lo2 n)
      (interval (final.read out) dst (m+n)) ∧
    cost.work ≤ 1024 * (m+n+1) ∧
    cost.span ≤ 4096 * (Nat.log2 (m+n+1)+1)^2 ∧
    Access.Within access (mergeAccess a out lo1 m lo2 n dst)

/-- The sort proof uses only the public contract of its merge subroutine. -/
theorem sort_into_from_merge (mergeContract : VerifiedMerge)
    (h : Heap) (a out scratch : SeqRef) (lo : Int) (n : Nat)
    (ha : a < h.nextRef) (ho : out < h.nextRef) (hs : scratch < h.nextRef)
    (ao : a ≠ out) (as_ : a ≠ scratch) (os : out ≠ scratch) :
    ∃ final cost access,
      sort_into.ParallelCall h (a, lo, ↑n, out, scratch) final 0 cost access ∧
      BuffersFrame h final out scratch lo n ∧
      SortResult (interval (h.read a) lo n) (interval (final.read out) lo n) ∧
      cost.work ≤ sortWork n ∧ cost.span ≤ sortSpan n ∧
      Access.Within access (sortAccess a out scratch lo n) := by
  induction n using Nat.strongRecOn generalizing h out scratch lo with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨h, _, _, ⟨⟨ha, ho, hs⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.ret
        rfl⟩, BuffersFrame.refl _ _ _ _ _, ?_, ?_, ?_, ?_⟩
      · simp [SortResult]
      · simp [sortWork, Cost.seq, Cost.one]
      · simp [sortSpan, Cost.seq, Cost.one]
      · simp [Access.Within, Access.union, Access.empty]
    · by_cases one : n = 1
      · subst n
        refine ⟨h.write out lo (h.read a lo), _, _, ⟨⟨ha, ho, hs⟩, by
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
            rw [if_pos ⟨ha, ho⟩]
          apply Eval.step
          · rfl
          apply Eval.ret
          rfl⟩, BuffersFrame.of_seq (SeqFrame.write h out lo 1 lo (h.read a lo) (by omega) (by omega)) scratch,
          ?_, ?_, ?_, ?_⟩
        · simp [SortResult, interval, Heap.read, Heap.write]
        · simp [sortWork, Cost.seq, Cost.one]
        · simp [sortSpan, Cost.seq, Cost.one]
        · have rd := sortAccess_read a out scratch a lo 1 lo (Or.inl rfl) (by omega) (by omega)
          have wr := sortAccess_write a out scratch out lo 1 lo (Or.inl rfl) (by omega) (by omega)
          repeat first | apply Access.Within.union | exact Access.Within.empty _ | exact rd | exact wr
      · have large : 1 < n := by omega
        have ls : n / 2 < n := by omega
        have rs : n - n / 2 < n := by omega
        have sum : n/2 + (n-n/2) = n := by omega
        obtain ⟨middle, lc, la, left, lf, lresult, lw, lspan, lr⟩ :=
          ih (n/2) ls h scratch out lo ha hs ho as_ ao os.symm
        have middleA : a < middle.nextRef := by rw [lf.nextRef]; exact ha
        have middleO : out < middle.nextRef := by rw [lf.nextRef]; exact ho
        have middleS : scratch < middle.nextRef := by rw [lf.nextRef]; exact hs
        obtain ⟨joined, rc, ra, right, rf, rresult, rw, rspan, rr⟩ :=
          ih (n-n/2) rs middle scratch out (lo + ↑(n/2)) middleA middleS middleO as_ ao os.symm
        have sourceSame : middle.read a = h.read a := lf.read_other as_ ao
        rw [sourceSame] at rresult
        have leftSame : interval (joined.read scratch) lo (n/2) =
            interval (middle.read scratch) lo (n/2) := by
          apply interval_congr
          intro i low high
          exact rf.outside scratch i (Or.inr (Or.inl high))
        rw [← leftSame] at lresult
        have joinedS : scratch < joined.nextRef := by rw [rf.nextRef, lf.nextRef]; exact hs
        have joinedO : out < joined.nextRef := by rw [rf.nextRef, lf.nextRef]; exact ho
        obtain ⟨final, mc, ma, merged, mf, mresult, mw, mspan, mr⟩ :=
          mergeContract joined scratch out lo (lo + ↑(n/2)) lo (n/2) (n-n/2)
            joinedS joinedO os.symm lresult.1 rresult.1
        rw [sum] at mf mresult mw mspan
        have spec := sort_merge _ _ _ _ _ lresult rresult mresult
        rw [← interval_append, sum] at spec
        have frame := ((lf.symm_buffers.weaken (by omega) (by omega)).trans
          (rf.symm_buffers.weaken (by omega) (by omega))).trans (BuffersFrame.of_seq mf scratch)
        have safe := (sortAccess_compatible a scratch out lo (lo + ↑(n/2)) (n/2) (n-n/2)
          (by omega)).of_within lr rr
        have lwithin := (lr.trans (sortAccess_swap a scratch out lo (n/2))).trans
          (sortAccess_mono a out scratch lo lo (n/2) n (by omega) (by omega))
        have rwithin := (rr.trans (sortAccess_swap a scratch out (lo + ↑(n/2)) (n-n/2))).trans
          (sortAccess_mono a out scratch (lo + ↑(n/2)) lo (n-n/2) n (by omega) (by omega))
        have mwithin := mr.trans (mergeAccess_within_sort a out scratch lo (n/2) (n-n/2))
        rw [sum] at mwithin
        have div : Int.fdiv (↑n) 2 = (↑(n/2) : Int) := (Int.ofNat_fdiv n 2).symm
        have sub : (↑n : Int) - ↑(n/2) = ↑(n-n/2) := by omega
        have positive : ¬ (↑n : Int) ≤ 0 := by omega
        have notOne : (↑n : Int) ≠ 1 := by omega
        refine ⟨final, _, _, ⟨⟨ha, ho, hs⟩, by
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, positive, decide_false] <;> rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, notOne, decide_false] <;> rfl
          apply Eval.step
          · rfl
          repeat (apply Eval.step; · rfl)
          apply Eval.fork
          · rfl
          · simpa only [div] using left.2
          · simpa only [div, sub] using right.2
          · exact safe
          repeat (apply Eval.step; · rfl)
          apply Eval.call
          · rfl
          · simpa only [div, sub] using merged.2
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.ret
          rfl⟩, frame, spec, ?_, ?_, ?_⟩
        · simp only [Cost.work_seq, Cost.work_fork, Cost.one]
          have bound := work_combine n lc.work rc.work mc.work large lw rw mw
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
        · simp only [Cost.span_seq, Cost.span_fork, Cost.one]
          have bound := span_combine n lc.span rc.span mc.span large lspan rspan mspan
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
        · repeat first | apply Access.Within.union | exact Access.Within.empty _ |
              exact lwithin | exact rwithin | exact mwithin

private theorem verified_merge : VerifiedMerge := by
  intro h a out lo1 lo2 dst m n ha ho different first second
  exact ParallelMergeAnalysis.merge_contract h a out lo1 m lo2 n dst ha ho different first second

/-- Complete reusable source contract for sorting into caller-supplied buffers.
Both buffer slices may change; every other cell and all counters are preserved.
The same completed execution satisfies the correctness and cost bounds. -/
theorem sort_into_contract (h : Heap) (a out scratch : SeqRef) (lo : Int) (n : Nat)
    (ha : a < h.nextRef) (ho : out < h.nextRef) (hs : scratch < h.nextRef)
    (ao : a ≠ out) (as_ : a ≠ scratch) (os : out ≠ scratch) :
    ∃ final cost access,
      sort_into.ParallelCall h (a, lo, ↑n, out, scratch) final 0 cost access ∧
      BuffersFrame h final out scratch lo n ∧
      SortResult (interval (h.read a) lo n) (interval (final.read out) lo n) ∧
      cost.work ≤ sortWork n ∧ cost.span ≤ sortSpan n ∧
      Access.Within access (sortAccess a out scratch lo n) :=
  sort_into_from_merge verified_merge h a out scratch lo n ha ho hs ao as_ os

/-- Explicit bounds on the completed sort, including its generated source
instructions, all merge calls, and fork/join overhead. -/
theorem sort_into_running_time (h : Heap) (a out scratch : SeqRef) (lo : Int) (n : Nat)
    (ha : a < h.nextRef) (ho : out < h.nextRef) (hs : scratch < h.nextRef)
    (ao : a ≠ out) (as_ : a ≠ scratch) (os : out ≠ scratch)
    {final : Heap} {value : Int} {cost : Cost} {access : Access}
    (run : sort_into.ParallelCall h (a, lo, ↑n, out, scratch) final value cost access) :
    cost.work ≤ 4224*(n+1)*(Nat.log2 (n+1)+1) ∧
    cost.span ≤ 131392*(Nat.log2 (n+1)+1)^3 := by
  obtain ⟨_, _, _, canonical, _, _, work, span, _⟩ :=
    sort_into_contract h a out scratch lo n ha ho hs ao as_ os
  have same := run.2.deterministic canonical.2
  rw [same.2.2.1]
  exact ⟨Nat.le_trans work (sortWork_nlog n), Nat.le_trans span (sortSpan_logcubed n)⟩

end ParallelMergeSortAnalysis
