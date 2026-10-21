import ParallelGenerated
import Algo2LeanLib.ParallelBounds
import Algo2LeanLib.ParallelSeq

/-! Exclusive prefix sums through two race-free fork–join traversals.
The reusable contracts retain the scratch representation, disjoint-slice
access permissions, and work/span costs of the generated source execution. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds

namespace ParallelPrefix

private theorem downsweep_span_combine (a b l r : Nat) (ha : a ≤ 24*l) (hb : b ≤ 24*r) :
    max a b + 23 ≤ 24 * (max l r + 1) := by
  have hl := Nat.mul_le_mul_left 24 (Nat.le_max_left l r)
  have hr := Nat.mul_le_mul_left 24 (Nat.le_max_right l r)
  omega

/-- The down-sweep writes the exclusive prefix of `source`, with the supplied
initial offset, into its output slice. Scratch and unrelated storage survive. -/
theorem downsweep_contract (h : Heap) (sums out : SeqRef) (source : Seq)
    (lo : Int) (n : Nat) (offset : Int)
    (hs : sums < h.nextRef) (ho : out < h.nextRef) (different : sums ≠ out)
    (tree : PrefixTree source (h.read sums) lo n) :
    ∃ final cost access, downsweep.ParallelCall h (sums, out, lo, ↑n, offset) final 0 cost access ∧
      SeqFrame h final out lo n ∧ IsExclusivePrefixSum source (final.read out) lo n offset ∧
      cost.work ≤ 24 * nodes n ∧ cost.span ≤ 24 * height n ∧
      Access.Within access (sliceAccess sums out lo n) := by
  induction n using Nat.strongRecOn generalizing h lo offset with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨h, _, _, ⟨⟨hs, ho⟩, by
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        exact Eval.ret rfl⟩, SeqFrame.refl _ _ _ _, ?_, ?_, ?_, ?_⟩
      · intro i hi; omega
      · simp [Cost.seq, Cost.one]
      · simp [Cost.seq, Cost.one]
      · simp [Access.Within, Access.union, Access.empty]
    · by_cases one : n = 1
      · subst n
        refine ⟨h.write out lo offset, _, _, ⟨⟨hs, ho⟩, by
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · dsimp only [parallelNext]; rw [if_pos ho]; rfl
          apply Eval.step
          · rfl
          exact Eval.ret rfl⟩, SeqFrame.write h out lo 1 lo offset (by omega) (by omega), ?_, ?_, ?_, ?_⟩
        · intro i hi
          have : i = 0 := by omega
          subst i
          simp [Heap.read_write_same, intervalSum]
        · simp [Cost.seq, Cost.one]
        · simp [Cost.seq, Cost.one]
        · repeat first
            | apply Access.Within.union
            | exact Access.Within.empty _
            | exact writeSeq_within_slice sums out lo 1 lo (by omega) (by omega)
      · have large : 1 < n := by omega
        have leftSmall : n / 2 < n := by omega
        have rightSmall : n - n / 2 < n := by omega
        have splitTree := (prefixTree_step source (h.read sums) lo n large).mp tree
        obtain ⟨middle, lc, la, left, lf, lp, lw, ls, lr⟩ :=
          ih (n / 2) leftSmall h lo offset hs ho splitTree.2.1
        have sameSums : middle.read sums = h.read sums := lf.read_other different
        have rightTree : PrefixTree source (middle.read sums) (lo + ↑(n / 2)) (n - n / 2) := by
          rw [sameSums]; exact splitTree.2.2
        obtain ⟨final, rc, ra, right, rf, rp, rw, rs, rr⟩ :=
          ih (n - n / 2) rightSmall middle (lo + ↑(n / 2))
            (offset + intervalSum source lo (n / 2))
            (by rw [lf.nextRef]; exact hs) (by rw [lf.nextRef]; exact ho) rightTree
        have div : Int.fdiv (↑n) 2 = (↑(n / 2) : Int) := (Int.ofNat_fdiv n 2).symm
        have castSub : (↑n : Int) - ↑(n / 2) = ↑(n - n / 2) := by omega
        have positive : ¬ (↑n : Int) ≤ 0 := by omega
        have notOne : (↑n : Int) ≠ 1 := by omega
        have safe := (sliceAccess_compatible sums out lo (lo + ↑(n / 2))
          (n / 2) (n - n / 2) different (by omega)).of_within lr rr
        refine ⟨final, _, _, ⟨⟨hs, ho⟩, by
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
          apply Eval.step
          · dsimp only [parallelNext]; rw [if_pos hs]; rfl
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
          · simpa only [div] using left.2
          · simpa only [div, castSub, splitTree.1] using right.2
          · exact safe
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          exact Eval.ret rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
        · exact (lf.weaken (by omega) (by omega)).trans (rf.weaken (by omega) (by omega))
        · have leftPreserved : IsExclusivePrefixSum source (final.read out) lo (n / 2) offset := by
            intro i hi
            rw [rf.outside out (lo + ↑i) (Or.inr (Or.inl (by omega)))]
            exact lp i hi
          have joined := exclusivePrefixSum_append source (final.read out) lo (n / 2) (n - n / 2)
            offset leftPreserved rp
          simpa only [Nat.add_sub_of_le (show n / 2 ≤ n by omega)] using joined
        · simp only [Cost.work_seq, Cost.work_fork, Cost.one]
          rw [nodes_step n large]
          omega
        · simp only [Cost.span_seq, Cost.span_fork, Cost.one]
          rw [height_step n large]
          have bound := downsweep_span_combine lc.span rc.span (height (n / 2)) (height (n - n / 2)) ls rs
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
        · have leftWithin := lr.trans (sliceAccess_mono sums out lo lo (n / 2) n (by omega) (by omega))
          have rightWithin := rr.trans (sliceAccess_mono sums out (lo + ↑(n / 2)) lo (n - n / 2) n (by omega) (by omega))
          have rootRead := readSeq_within_slice sums out lo n (lo + ↑(n / 2) - 1) (by omega) (by omega)
          simp only [div]
          repeat first
            | apply Access.Within.union
            | exact Access.Within.empty _
            | exact leftWithin
            | exact rightWithin
            | exact rootRead

end ParallelPrefix
