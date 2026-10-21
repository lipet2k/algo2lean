import ParallelGenerated
import Algo2LeanLib.ParallelBounds
import Algo2LeanLib.ParallelSeq

/-! Reusable up-sweep contract for the generated parallel prefix-sum source.
The scratch representation retains precisely the subtree totals subsequently
read by the down-sweep. Source reads and scratch writes have disjoint bounds. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds

namespace ParallelPrefix

private theorem work_combine (a b l r : Nat) (ha : a ≤ 24*l) (hb : b ≤ 24*r) :
    a + b + 22 ≤ 24 * (l + r + 1) := by omega

private theorem span_combine (a b l r : Nat) (ha : a ≤ 24*l) (hb : b ≤ 24*r) :
    max a b + 22 ≤ 24 * (max l r + 1) := by
  have hl := Nat.mul_le_mul_left 24 (Nat.le_max_left l r)
  have hr := Nat.mul_le_mul_left 24 (Nat.le_max_right l r)
  omega

/-- Store subtree totals in a preallocated scratch slice. All caller counters
and storage outside that slice are preserved. Empty and odd sizes are included. -/
theorem upsweep_contract (h : Heap) (a sums : SeqRef) (lo : Int) (n : Nat)
    (ha : a < h.nextRef) (hs : sums < h.nextRef) (different : a ≠ sums) :
    ∃ final cost access,
      upsweep.ParallelCall h (a, sums, lo, ↑n) final
        (intervalSum (h.read a) lo n) cost access ∧
      SeqFrame h final sums lo n ∧
      PrefixTree (h.read a) (final.read sums) lo n ∧
      (0 < n → final.read sums (lo + ↑n - 1) = intervalSum (h.read a) lo n) ∧
      cost.work ≤ 24 * nodes n ∧ cost.span ≤ 24 * height n ∧
      Access.Within access (sliceAccess a sums lo n) := by
  induction n using Nat.strongRecOn generalizing h lo with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨h, _, _, ⟨⟨ha, hs⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        exact Eval.ret rfl⟩, SeqFrame.refl _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩
      · exact prefixTree_base _ _ _ _ (by decide)
      · omega
      · simp [Cost.seq, Cost.one]
      · simp [Cost.seq, Cost.one]
      · simp [Access.Within, Access.union, Access.empty]
    · by_cases one : n = 1
      · subst n
        refine ⟨h.write sums lo (h.read a lo), _, _, ⟨⟨ha, hs⟩, by
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext]; rw [if_pos ha]
          apply Eval.step
          · simp only [parallelNext]; rw [if_pos hs]
          apply Eval.step
          · rfl
          apply Eval.ret
          simp only [parallelNext, intervalSum_one]; rfl⟩,
          SeqFrame.write h sums lo 1 lo _ (by omega) (by omega), ?_, ?_, ?_, ?_, ?_⟩
        · exact prefixTree_base _ _ _ _ (by decide)
        · intro _; simp [Heap.read, Heap.write]
        · simp [Cost.seq, Cost.one]
        · simp [Cost.seq, Cost.one]
        · have rd := readSeq_within_slice a sums lo 1 lo (by omega) (by omega)
          have wr := writeSeq_within_slice a sums lo 1 lo (by omega) (by omega)
          simp only [Access.Within, Access.union, Access.empty] at rd wr ⊢
          rcases rd with ⟨rd, rdw, rda⟩
          rcases wr with ⟨wr, wrw, wra⟩
          constructor
          · intro x hx
            simp only [false_or, or_false] at hx
            exact hx.elim (rd x) (wr x)
          constructor
          · intro x hx
            simp only [false_or, or_false] at hx
            exact hx.elim (rdw x) (wrw x)
          · simp only [Bool.false_or, Bool.or_false, Bool.or_eq_true]
            exact fun h => h.elim rda wra
      · have large : 1 < n := by omega
        have leftSmall : n / 2 < n := by omega
        have rightSmall : n - n / 2 < n := by omega
        obtain ⟨middle, lc, la, left, lf, lt, rootLeft, lw, ls, lr⟩ :=
          ih (n / 2) leftSmall h lo ha hs
        have sameLeft := lf.read_other different
        have ma : a < middle.nextRef := by rw [lf.nextRef]; exact ha
        have ms : sums < middle.nextRef := by rw [lf.nextRef]; exact hs
        obtain ⟨joined, rc, ra, right, rf, rt, rootRight, rw, rs, rr⟩ :=
          ih (n - n / 2) rightSmall middle (lo + ↑(n / 2)) ma ms
        rw [sameLeft] at right rt rootRight
        have js : sums < joined.nextRef := by rw [rf.nextRef, lf.nextRef]; exact hs
        have safe := (sliceAccess_compatible a sums lo (lo + ↑(n / 2))
          (n / 2) (n - n / 2) different (by omega)).of_within lr rr
        have div : Int.fdiv (↑n) 2 = (↑(n / 2) : Int) := (Int.ofNat_fdiv n 2).symm
        have castSub : (↑n : Int) - ↑(n / 2) = ↑(n - n / 2) := by omega
        have positive : ¬ (↑n : Int) ≤ 0 := by omega
        have notOne : (↑n : Int) ≠ 1 := by omega
        have splitSum := intervalSum_split (h.read a) lo n (n / 2) (by omega)
        let total := intervalSum (h.read a) lo (n / 2) +
          intervalSum (h.read a) (lo + ↑(n / 2)) (n - n / 2)
        have finalFrame : SeqFrame h (joined.write sums (lo + ↑n - 1) total) sums lo n :=
          ((lf.weaken (by omega) (by omega)).trans (rf.weaken (by omega) (by omega))).trans
            (SeqFrame.write joined sums lo n (lo + ↑n - 1) total (by omega) (by omega))
        have leftTree : PrefixTree (h.read a) (joined.read sums) lo (n / 2) := by
          apply prefixTree_congr _ _ _ _ _ _ lt
          intro i lower upper
          exact (rf.outside sums i (Or.inr (Or.inl (by omega)))).symm
        have leftRoot : joined.read sums (lo + ↑(n / 2) - 1) =
            intervalSum (h.read a) lo (n / 2) := by
          rw [rf.outside sums _ (Or.inr (Or.inl (by omega)))]
          exact rootLeft (by omega)
        have joinedTree : PrefixTree (h.read a) (joined.read sums) lo n :=
          (prefixTree_step _ _ _ _ large).mpr ⟨leftRoot, leftTree, rt⟩
        refine ⟨joined.write sums (lo + ↑n - 1) total, _, _, ⟨⟨ha, hs⟩, by
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, positive, decide_false]; rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext, notOne, decide_false]; rfl
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
          · simpa only [div] using left.2
          · simpa only [div, castSub] using right.2
          · exact safe
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext]; rw [if_pos js]
          apply Eval.step
          · rfl
          apply Eval.ret
          simp only [parallelNext]
          rw [splitSum]⟩, finalFrame, ?_, ?_, ?_, ?_, ?_⟩
        · have storeEq : (joined.write sums (lo + ↑n - 1) total).read sums =
              (fun i => if i = lo + ↑n - 1 then total else joined.read sums i) := by
            funext i
            simp [Heap.read, Heap.write]
          rw [storeEq]
          exact prefixTree_write_last (h.read a) (joined.read sums) lo n total joinedTree
        · intro _; simp [Heap.read, Heap.write, total, splitSum]
        · simp only [Cost.work_seq, Cost.work_fork, Cost.one]
          rw [nodes_step n large]
          have bound := work_combine lc.work rc.work (nodes (n / 2)) (nodes (n - n / 2)) lw rw
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
        · simp only [Cost.span_seq, Cost.span_fork, Cost.one]
          rw [height_step n large]
          have bound := span_combine lc.span rc.span (height (n / 2)) (height (n - n / 2)) ls rs
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
        · have leftWithin := lr.trans (sliceAccess_mono a sums lo lo (n / 2) n (by omega) (by omega))
          have rightWithin := rr.trans (sliceAccess_mono a sums (lo + ↑(n / 2)) lo
            (n - n / 2) n (by omega) (by omega))
          have writeWithin := writeSeq_within_slice a sums lo n (lo + ↑n - 1) (by omega) (by omega)
          simp only [Access.Within, Access.union, Access.empty] at leftWithin rightWithin writeWithin ⊢
          rcases leftWithin with ⟨lread, lwrite, lalloc⟩
          rcases rightWithin with ⟨rread, rwrite, ralloc⟩
          rcases writeWithin with ⟨wread, wwrite, walloc⟩
          constructor
          · intro x hx
            simp only [false_or, or_false] at hx
            exact hx.elim (fun h => h.elim (lread x) (rread x)) (wread x)
          constructor
          · intro x hx
            simp only [false_or, or_false] at hx
            exact hx.elim (fun h => h.elim (lwrite x) (rwrite x)) (wwrite x)
          · simp only [Bool.false_or, Bool.or_false, Bool.or_eq_true]
            exact fun h => h.elim (fun h => h.elim lalloc ralloc) walloc

end ParallelPrefix
