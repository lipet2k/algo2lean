import ParallelGenerated
import Algo2LeanLib.ParallelBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4096

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds

namespace ParallelSumAnalysis

/-- A completed source call returns the interval sum without changing any
heap field. Its access record contains only reads of the requested interval. -/
theorem call_contract (h : Heap) (a : SeqRef) (lo : Int) (n : Nat)
    (valid : a < h.nextRef) :
    ∃ cost access,
      parallel_sum.ParallelCall h (a, lo, ↑n) h (intervalSum (h.read a) lo n) cost access ∧
      cost.work ≤ 18 * nodes n ∧ cost.span ≤ 18 * height n ∧
      Access.Within access (readInterval a lo n) := by
  induction n using Nat.strongRecOn generalizing lo with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨_, _, ⟨valid, by
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
    · by_cases one : n = 1
      · subst n
        refine ⟨_, _, ⟨valid, by
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · rfl
          apply Eval.step
          · dsimp only [parallelNext]
            rw [if_pos valid]
            rfl
          apply Eval.ret
          simp only [parallelNext, intervalSum_one]
          rfl⟩, ?_, ?_, ?_⟩
        · simp [Cost.seq, Cost.one]
        · simp [Cost.seq, Cost.one]
        · simp [Access.Within, Access.union, Access.empty, Access.readSeq, Access.read,
            readInterval]
          omega
      · have large : 1 < n := by omega
        have leftSmall : n / 2 < n := by omega
        have rightSmall : n - n / 2 < n := by omega
        obtain ⟨lc, la, left, lw, ls, lr⟩ := ih (n / 2) leftSmall lo
        obtain ⟨rc, ra, right, rw, rs, rr⟩ := ih (n - n / 2) rightSmall (lo + ↑(n / 2))
        have div : Int.fdiv (↑n) 2 = (↑(n / 2) : Int) := (Int.ofNat_fdiv n 2).symm
        have castSub : (↑n : Int) - ↑(n / 2) = ↑(n - n / 2) := by omega
        have positive : ¬ (↑n : Int) ≤ 0 := by omega
        have notOne : (↑n : Int) ≠ 1 := by omega
        have safe := (readInterval_compatible a a lo (lo + ↑(n / 2))
          (n / 2) (n - n / 2)).of_within lr rr
        refine ⟨_, _, ⟨valid, by
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
          apply Eval.ret
          simp only [parallelNext]
          rw [intervalSum_split (h.read a) lo n (n / 2) (by omega)]⟩, ?_, ?_, ?_⟩
        · simp only [Cost.work_seq, Cost.work_fork, Cost.one]
          rw [nodes_step n large]
          omega
        · simp only [Cost.span_seq, Cost.span_fork, Cost.one]
          rw [height_step n large]
          have leftHeight := Nat.mul_le_mul_left 18
            (Nat.le_max_left (height (n / 2)) (height (n - n / 2)))
          have rightHeight := Nat.mul_le_mul_left 18
            (Nat.le_max_right (height (n / 2)) (height (n - n / 2)))
          omega
        · have leftWithin := lr.trans
            (readInterval_mono a lo lo n (n / 2) (by omega) (by omega))
          have rightWithin := rr.trans
            (readInterval_mono a lo (lo + ↑(n / 2)) n (n - n / 2) (by omega) (by omega))
          simp only [Access.Within, Access.union, Access.empty] at leftWithin rightWithin ⊢
          rcases leftWithin with ⟨lread, lwrite, lalloc⟩
          rcases rightWithin with ⟨rread, rwrite, ralloc⟩
          constructor
          · intro x hx
            simp only [false_or, or_false] at hx
            exact hx.elim (lread x) (rread x)
          constructor
          · intro x hx
            simp only [false_or, or_false] at hx
            exact hx.elim (lwrite x) (rwrite x)
          · simp only [Bool.false_or, Bool.or_false, Bool.or_eq_true]
            exact fun h => h.elim lalloc ralloc

/-- The reusable contract also covers negative source lengths as empty
intervals. Every counter and all caller-owned storage remain unchanged. -/
theorem call_contract_all (h : Heap) (a : SeqRef) (lo n : Int)
    (valid : a < h.nextRef) :
    ∃ cost access,
      parallel_sum.ParallelCall h (a, lo, n) h (intervalSum (h.read a) lo n.toNat) cost access ∧
      cost.work ≤ 18 * nodes n.toNat ∧ cost.span ≤ 18 * height n.toNat ∧
      Access.Within access (readInterval a lo n.toNat) := by
  by_cases nonnegative : 0 ≤ n
  · have cast : (↑n.toNat : Int) = n := Int.toNat_of_nonneg nonnegative
    simpa only [cast] using call_contract h a lo n.toNat valid
  · have empty : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have nonpositive : n ≤ 0 := by omega
    rw [empty]
    refine ⟨_, _, ⟨valid, by
      apply Eval.step
      · rfl
      apply Eval.step
      · simp only [parallelNext, nonpositive, decide_true] <;> rfl
      apply Eval.step
      · rfl
      apply Eval.ret
      rfl⟩, ?_, ?_, ?_⟩
    · simp [Cost.seq, Cost.one]
    · simp [Cost.seq, Cost.one]
    · simp [Access.Within, Access.union, Access.empty]

/-- Ordinary sequential callers reuse the serialization of the same verified
fork–join execution without repeating its correctness proof. -/
theorem sequential_call (h : Heap) (a : SeqRef) (lo n : Int)
    (valid : a < h.nextRef) :
    parallel_sum.Call h (a, lo, n) h (intervalSum (h.read a) lo n.toNat) := by
  obtain ⟨_, _, run, _, _, _⟩ := call_contract_all h a lo n valid
  exact run.call

-- Main result: Correctness
/-- Every completed structured execution returns the sum of the requested
interval and preserves the entire heap. Nonpositive lengths return zero. -/
theorem correctness (h final : Heap) (a : SeqRef) (lo n output : Int)
    (cost : Cost) (access : Access)
    (run : parallel_sum.ParallelCall h (a, lo, n) final output cost access) :
    final = h ∧ output = intervalSum (h.read a) lo n.toNat := by
  obtain ⟨_, _, canonical, _, _, _⟩ := call_contract_all h a lo n run.1
  obtain ⟨heap, result, _, _⟩ := run.2.deterministic canonical.2
  exact ⟨heap, Result.fn_parallel_sum.inj result⟩

/-- Concrete work/span bounds for the generated program, including argument
evaluation, control flow, calls, returns, and fork/join overhead. -/
theorem running_time_explicit (h final : Heap) (a : SeqRef) (lo n output : Int)
    (cost : Cost) (access : Access)
    (run : parallel_sum.ParallelCall h (a, lo, n) final output cost access) :
    cost.work ≤ 18 * (2 * n.toNat + 1) ∧
    cost.span ≤ 18 * (Nat.log2 n.toNat + 2) := by
  obtain ⟨_, _, canonical, work, span, _⟩ := call_contract_all h a lo n run.1
  obtain ⟨_, _, costs, _⟩ := run.2.deterministic canonical.2
  rw [costs]
  exact ⟨Nat.le_trans work (Nat.mul_le_mul_left 18 (nodes_le_linear n.toNat)),
    Nat.le_trans span (Nat.mul_le_mul_left 18 (height_le_logarithmic n.toNat))⟩

-- Main result: Running time
/-- A uniform linear work bound and logarithmic span bound. The constants are
independent of the input values, interval, length, and caller's heap. -/
theorem running_time : ∃ C : Nat, 0 < C ∧
    ∀ (h final : Heap) (a : SeqRef) (lo n output : Int) (cost : Cost) (access : Access),
      parallel_sum.ParallelCall h (a, lo, n) final output cost access →
      cost.work ≤ C * (n.toNat + 1) ∧
      cost.span ≤ C * (Nat.log2 n.toNat + 1) := by
  refine ⟨36, by decide, ?_⟩
  intro h final a lo n output cost access run
  have bounds := running_time_explicit h final a lo n output cost access run
  constructor <;> omega

end ParallelSumAnalysis
