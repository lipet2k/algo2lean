import ParallelMergeGenerated
import Algo2LeanLib.ParallelMergeSpec
import Algo2LeanLib.ParallelBounds

/-!
The CLRS parallel merge's binary search returns a lower-bound position. The
contract keeps the heap unchanged, records all source reads, and bounds actual
generated instructions. Equal keys remain in the right partition.
-/
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds Algo2Lean.ParallelMerge

namespace ParallelMergeSearch

/-- A power-of-two size bound pays for one search level at a time. -/
theorem call_contract_depth (depth : Nat) (h : Heap) (a : SeqRef) (lo : Int) (n : Nat) (key : Int)
    (valid : a < h.nextRef) (sorted : (interval (h.read a) lo n).Pairwise (· ≤ ·))
    (size : n < 2^depth) :
    ∃ (k : Nat) (cost : Cost) (access : Access),
      binary_search.ParallelCall h (a,lo,↑n,key) h (↑k : Int) cost access ∧
      LowerBound (h.read a) lo n key k ∧
      cost.work ≤ 16*(depth+1) ∧ Access.Within access (readInterval a lo n) := by
  induction depth generalizing lo n with
  | zero =>
    have zero : n=0 := by simpa using size
    subst n
    refine ⟨0,_,_,⟨valid,by
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.step
      · rfl
      apply Eval.ret
      rfl⟩,?_,?_,?_⟩
    · simp [LowerBound]
    · simp [Cost.seq,Cost.one]
    · simp [Access.Within,Access.union,Access.empty]
  | succ depth ih =>
    by_cases zero : n=0
    · subst n
      refine ⟨0,_,_,⟨valid,by
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.step
        · rfl
        apply Eval.ret
        rfl⟩,?_,?_,?_⟩
      · simp [LowerBound]
      · simp [Cost.seq,Cost.one]; omega
      · simp [Access.Within,Access.union,Access.empty]
    · have positive : 0<n := by omega
      have halfSmall : n/2<n := by omega
      have scale : n < 2*(2^depth) := by simpa [Nat.pow_succ,Nat.mul_comm] using size
      have div : Int.fdiv (↑n) 2 = (↑(n/2) : Int) := (Int.ofNat_fdiv n 2).symm
      have nextCount : (↑n : Int)-↑(n/2)-1 = ↑(n-n/2-1) := by omega
      have notZero : ¬ (↑n : Int) ≤ 0 := by omega
      have read : Access.Within (Access.readSeq a (lo+↑(n/2))) (readInterval a lo n) :=
        readSeq_within a lo n _ (by omega) (by omega)
      by_cases less : h.read a (lo+↑(n/2)) < key
      · have sortedRight := sorted_subinterval (h.read a) lo n (n/2+1) (n-n/2-1) sorted (by omega)
        have shift : lo+↑(n/2+1)=lo+↑(n/2)+1 := by omega
        rw [shift] at sortedRight
        obtain ⟨k,c,access,run,bound,work,reads⟩ := ih (lo+↑(n/2)+1) (n-n/2-1) sortedRight (by omega)
        have result : LowerBound (h.read a) lo n key (n/2+1+k) := by
          exact LowerBound.right (h.read a) lo n (n/2) k key sorted halfSmall less bound
        have within := reads.trans (readInterval_mono a lo (lo+↑(n/2)+1) n (n-n/2-1) (by omega) (by omega))
        refine ⟨n/2+1+k,_,_,⟨valid,by
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext,notZero,decide_false]; rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · dsimp only [parallelNext]; rw [if_pos valid]; rfl
          apply Eval.step
          · simp only [parallelNext,div,less,decide_true]; rfl
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
          · simpa only [div,nextCount] using run.2
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.ret
          simp only [parallelNext]
          congr 1⟩,result,?_,?_⟩
        · simp only [Cost.seq,Cost.one]
          omega
        · change Access.Within _ _
          simp only [div]
          repeat first
            | apply Access.Within.union
            | exact Access.Within.empty _
            | exact within
            | exact read
      · have sortedLeft := sorted_subinterval (h.read a) lo n 0 (n/2) sorted (by omega)
        simp only [Int.natCast_zero,Int.add_zero] at sortedLeft
        obtain ⟨k,c,access,run,bound,work,reads⟩ := ih lo (n/2) sortedLeft (by omega)
        have result : LowerBound (h.read a) lo n key k := by
          exact LowerBound.left (h.read a) lo n (n/2) k key sorted halfSmall (by omega) bound
        have within := reads.trans (readInterval_mono a lo lo n (n/2) (by omega) (by omega))
        refine ⟨k,_,_,⟨valid,by
          apply Eval.step
          · rfl
          apply Eval.step
          · simp only [parallelNext,notZero,decide_false]; rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · dsimp only [parallelNext]; rw [if_pos valid]; rfl
          apply Eval.step
          · simp only [parallelNext,div,less,decide_false]; rfl
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
          · simpa only [div] using run.2
          apply Eval.ret
          rfl⟩,result,?_,?_⟩
        · simp only [Cost.seq,Cost.one]
          omega
        · simp only [div]
          repeat first
            | apply Access.Within.union
            | exact Access.Within.empty _
            | exact within
            | exact read

/-- Reusable lower-bound search: termination, exact partition, unchanged heap,
read-only access, and logarithmic work/span from the same source execution. -/
theorem call_contract (h : Heap) (a : SeqRef) (lo : Int) (n : Nat) (key : Int)
    (valid : a < h.nextRef) (sorted : (interval (h.read a) lo n).Pairwise (· ≤ ·)) :
    ∃ (k : Nat) (cost : Cost) (access : Access),
      binary_search.ParallelCall h (a,lo,↑n,key) h (↑k : Int) cost access ∧
      LowerBound (h.read a) lo n key k ∧
      cost.work ≤ 32*(Nat.log2 (n+1)+1) ∧ cost.span ≤ 32*(Nat.log2 (n+1)+1) ∧
      Access.Within access (readInterval a lo n) := by
  obtain ⟨k,c,access,run,bound,work,reads⟩ :=
    call_contract_depth (Nat.log2 n+1) h a lo n key valid sorted Nat.lt_log2_self
  have mono : Nat.log2 n ≤ Nat.log2 (n+1) := by
    by_cases zero : n=0
    · subst n; decide
    · exact (Nat.le_log2 (by omega : n+1≠0)).2 (Nat.le_trans (Nat.log2_self_le zero) (by omega))
  have total : c.work ≤ 32*(Nat.log2 (n+1)+1) := by omega
  exact ⟨k,c,access,run,bound,total,Nat.le_trans run.2.span_le_work total,reads⟩

end ParallelMergeSearch
