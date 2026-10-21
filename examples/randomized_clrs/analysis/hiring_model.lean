import Algo2LeanProbability.Call
import Algo2LeanLib.Footprint
import Mathlib.Algebra.BigOperators.Fin
import Algo.shuffle_uniform.Analysis

/-!
The hiring model counts strict records in a sequence of candidate scores. The
operation accounting records one interview per candidate and one hire per
strict record, while preserving all data and unrelated clock values.
-/

noncomputable section
namespace HiringAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open scoped ENNReal

/-- Additional hires while scanning `count` candidates after an existing best
score. Equal scores do not cause a hire. -/
def recordsAfter (scores : Int → Int) (first best : Int) : Nat → Nat
  | 0 => 0
  | count + 1 => if best < scores first then
      1 + recordsAfter scores (first + 1) (scores first) count
    else recordsAfter scores (first + 1) best count

/-- The first candidate is hired; every later hire is a strict score record. -/
def recordCount (scores : Int → Int) : Nat → Nat
  | 0 => 0
  | count + 1 => 1 + recordsAfter scores 1 (scores 0) count

@[simp] theorem tick_read_function (heap : Heap) (clock : String) (amount : Nat)
    (ref : SeqRef) : (heap.tick clock amount).read ref = heap.read ref := rfl

/-- Aggregate clock effect of the scan, preserving the caller's data. -/
def account (heap : Heap) (interviews hires : Nat) : Heap :=
  (heap.tick "interviews" interviews).tick "hires" hires

@[simp] theorem account_zero (heap : Heap) : account heap 0 0 = heap := by
  simp [account]

@[simp] theorem account_read (heap : Heap) (interviews hires : Nat) (ref : SeqRef) (index : Int) :
    (account heap interviews hires).read ref index = heap.read ref index := rfl

@[simp] theorem account_nextRef (heap : Heap) (interviews hires : Nat) :
    (account heap interviews hires).nextRef = heap.nextRef := rfl

@[simp] theorem account_interviews (heap : Heap) (interviews hires : Nat) :
    Heap.cost heap (account heap interviews hires) "interviews" = interviews := by
  simp [Heap.cost, account]

@[simp] theorem account_hires (heap : Heap) (interviews hires : Nat) :
    Heap.cost heap (account heap interviews hires) "hires" = hires := by
  simp [Heap.cost, account]

theorem account_step (heap : Heap) (interviews hires : Nat) :
    account (heap.tick "interviews") interviews hires = account heap (interviews + 1) hires := by
  simp [account, Heap.tick_add, Nat.add_comm]

theorem account_hire_step (heap : Heap) (interviews hires : Nat) :
    account ((heap.tick "interviews").tick "hires") interviews hires =
      account heap (interviews + 1) (hires + 1) := by
  unfold account
  rw [Heap.tick_comm (heap.tick "interviews") "hires" "interviews" 1 interviews]
  simp [Heap.tick_add, Nat.add_comm]

/-- A candidate can cause at most one additional hire. -/
theorem recordsAfter_le (scores : Int → Int) (first best : Int) (count : Nat) :
    recordsAfter scores first best count ≤ count := by
  induction count generalizing first best with
  | zero => rfl
  | succ count ih =>
      simp only [recordsAfter]
      split
      · have := ih (first + 1) (scores first)
        omega
      · have := ih (first + 1) best
        omega

/-- The total number of hires is bounded by the number of interviews. -/
theorem recordCount_le (scores : Int → Int) (count : Nat) : recordCount scores count ≤ count := by
  cases count with
  | zero => rfl
  | succ count =>
      have := recordsAfter_le scores 1 (scores 0) count
      simp only [recordCount]
      omega


/-- Strict records that also exceed an existing best score. -/
def recordsAbove {n : Nat} (scores : Fin n → Int) (best : Int) : ℝ≥0∞ :=
  ∑ i, if best < scores i ∧ ∀ j, j < i → scores j < scores i then 1 else 0

private theorem record_tail {n : Nat} (scores : Fin (n + 1) → Int) (best : Int) (i : Fin n) :
    (best < scores i.succ ∧ ∀ j, j < i.succ → scores j < scores i.succ) ↔
      max best (scores 0) < scores i.succ ∧
        ∀ j : Fin n, j < i → scores j.succ < scores i.succ := by
  rw [max_lt_iff]
  constructor
  · rintro ⟨above, previous⟩
    exact ⟨⟨above, previous 0 (by simp)⟩, fun j less => previous j.succ (by simpa using less)⟩
  · rintro ⟨⟨above, first⟩, previous⟩
    refine ⟨above, ?_⟩
    intro j less
    cases j using Fin.cases with
    | zero => exact first
    | succ j => exact previous j (by simpa using less)

theorem recordsAbove_succ {n : Nat} (scores : Fin (n + 1) → Int) (best : Int) :
    recordsAbove scores best = (if best < scores 0 then 1 else 0) +
      recordsAbove (fun i : Fin n => scores i.succ) (max best (scores 0)) := by
  unfold recordsAbove
  rw [Fin.sum_univ_succ]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    simp only [record_tail]

theorem recordsAfter_eq_recordsAbove (scores : Int → Int) (first best : Int) (n : Nat) :
    (recordsAfter scores first best n : ℝ≥0∞) =
      recordsAbove (fun i : Fin n => scores (first + i.val)) best := by
  induction n generalizing first best with
  | zero => simp [recordsAfter, recordsAbove]
  | succ n ih =>
      rw [recordsAbove_succ]
      simp only [Fin.val_zero, Int.natCast_zero, add_zero]
      by_cases improves : best < scores first
      · simp only [recordsAfter, improves, ↓reduceIte, Nat.cast_add, Nat.cast_one,
          max_eq_right improves.le]
        rw [ih]
        congr 2
        funext i
        simp [Int.add_comm, Int.add_left_comm]
      · simp only [recordsAfter, improves, ↓reduceIte, zero_add,
          max_eq_left (le_of_not_gt improves)]
        rw [ih]
        congr 2
        funext i
        simp [Int.add_comm, Int.add_left_comm]

/-- The recursive hiring count equals the sum of strict record indicators. -/
theorem recordCount_eq_record_sum (scores : Int → Int) (n : Nat) :
    (recordCount scores n : ℝ≥0∞) =
      ∑ i : Fin n, if (∀ j : Fin n, j < i → scores j.val < scores i.val) then 1 else 0 := by
  cases n with
  | zero => simp [recordCount]
  | succ n =>
      rw [recordCount, Nat.cast_add, Nat.cast_one, recordsAfter_eq_recordsAbove,
        Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.not_lt_zero, false_implies, implies_true, ↓reduceIte]
      congr 1
      unfold recordsAbove
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply propext
      constructor
      · rintro ⟨above, previous⟩ j less
        cases j using Fin.cases with
        | zero => simpa [Int.add_comm] using above
        | succ j =>
            have := previous j (by simpa using less)
            simpa [Int.natCast_add, Int.add_comm] using this
      · intro previous
        refine ⟨?_, ?_⟩
        · have := previous 0 (by simp)
          simpa [Int.natCast_add, Int.add_comm] using this
        · intro j less
          have := previous j.succ (by simpa using less)
          simpa [Int.natCast_add, Int.add_comm] using this


open ShuffleAnalysis

/-- The deterministic record-count recursion on a shuffled heap has the same
expectation as record indicators under a uniform positional permutation. -/
theorem shuffled_record_count (heap : Heap) (ref : SeqRef) (n : Nat) :
    pmfExpected (shuffleLaw heap ref 0 n)
      (fun final => (recordCount (final.read ref) n : ℝ≥0∞)) =
    pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
      (fun permutation => ∑ i : Fin n,
        if (∀ j : Fin n, j < i → heap.read ref (permutation j).val <
          heap.read ref (permutation i).val) then 1 else 0) := by
  have uniform := shuffleLaw_uniform n heap ref 0
    (fun values => ∑ i : Fin n, if (∀ j : Fin n, j < i → values j < values i) then
      (1 : ℝ≥0∞) else 0)
  rw [permutationLaw_uniform] at uniform
  simpa [pmfExpected, recordCount_eq_record_sum, prefixValues] using uniform


end HiringAnalysis
