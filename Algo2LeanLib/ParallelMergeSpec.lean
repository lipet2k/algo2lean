import Algo2Lean
import Init.Data.List.Sort.Lemmas

/-!
Finite-interval specifications for parallel merging and merge sort.
These mathematical lemmas are independent of generated instructions. They retain
multiplicities, allow equal keys, and use arbitrary integer starting indices.
-/
namespace Algo2Lean.ParallelMerge
open Algo2LeanGenerated

/-- The finite list stored in an integer-indexed interval. -/
def interval (a : Seq) (lo : Int) : Nat → List Int
  | 0 => []
  | n + 1 => a lo :: interval a (lo + 1) n

@[simp] theorem interval_length (a : Seq) (lo : Int) (n : Nat) :
    (interval a lo n).length = n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih => simp [interval, ih]

@[simp] theorem interval_zero (a : Seq) (lo : Int) : interval a lo 0 = [] := rfl

@[simp] theorem interval_one (a : Seq) (lo : Int) : interval a lo 1 = [a lo] := rfl

theorem interval_append (a : Seq) (lo : Int) (m n : Nat) :
    interval a lo (m + n) = interval a lo m ++ interval a (lo + (m : Int)) n := by
  induction m generalizing lo with
  | zero => simp [interval]
  | succ m ih =>
    simp only [Nat.succ_add, interval, List.cons_append, ih]
    congr 3 <;> omega

theorem interval_congr (a b : Seq) (lo : Int) (n : Nat)
    (same : ∀ i, lo ≤ i → i < lo + (n : Int) → a i = b i) :
    interval a lo n = interval b lo n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    simp only [interval]
    congr 1
    · exact same lo (by omega) (by omega)
    · exact ih (lo + 1) (fun i low high => same i (by omega) (by omega))

theorem interval_get (a : Seq) (lo : Int) (n i : Nat) (valid : i < n) :
    (interval a lo n)[i]'(by simpa using valid) = a (lo + (i : Int)) := by
  induction n generalizing lo i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [interval]
    | succ i =>
      simp only [interval, List.getElem_cons_succ]
      rw [ih (lo + 1) i (by omega)]
      congr 1
      omega

theorem mem_interval (a : Seq) (lo : Int) (n : Nat) (x : Int) :
    x ∈ interval a lo n ↔ ∃ i : Nat, i < n ∧ x = a (lo + i) := by
  constructor
  · intro mem
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp mem
    have small : i < n := by simpa using hi
    exact ⟨i, small, (eq.symm.trans (interval_get a lo n i small))⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_iff_getElem.mpr ⟨i, by simpa using hi, interval_get a lo n i hi⟩

theorem interval_split (a : Seq) (lo : Int) (n k : Nat) (hk : k ≤ n) :
    interval a lo n = interval a lo k ++ interval a (lo + k) (n - k) := by
  have total : k + (n - k) = n := by omega
  simpa only [total] using interval_append a lo k (n - k)

theorem interval_pivot (a : Seq) (lo : Int) (n k : Nat) (hk : k < n) :
    interval a lo n = interval a lo k ++ a (lo + k) :: interval a (lo + k + 1) (n - k - 1) := by
  rw [interval_split a lo n k (by omega)]
  have size : n - k = (n - k - 1) + 1 := by omega
  rw [size, interval]
  simp only [Nat.add_sub_cancel]

/-- Sortedness gives the usual pointwise monotonicity, including equal indices. -/
theorem sorted_interval_mono (a : Seq) (lo : Int) (n : Nat)
    (sorted : (interval a lo n).Pairwise (· ≤ ·))
    (i j : Nat) (order : i ≤ j) (upper : j < n) : a (lo + i) ≤ a (lo + j) := by
  by_cases equal : i = j
  · subst j; exact Int.le_refl _
  · have hi : i < n := by omega
    have result := List.pairwise_iff_getElem.mp sorted i j (by simpa using hi)
      (by simpa using upper) (by omega)
    simpa only [interval_get a lo n i hi, interval_get a lo n j upper] using result

/-- Every finite subinterval of a sorted interval is sorted. -/
theorem sorted_subinterval (a : Seq) (lo : Int) (n start count : Nat)
    (sorted : (interval a lo n).Pairwise (· ≤ ·)) (inside : start + count ≤ n) :
    (interval a (lo + start) count).Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj order
  have hi' : i < count := by simpa using hi
  have hj' : j < count := by simpa using hj
  rw [interval_get a (lo + start) count i hi', interval_get a (lo + start) count j hj']
  have bound := sorted_interval_mono a lo n sorted (start + i) (start + j) (by omega) (by omega)
  simpa only [Int.natCast_add, Int.add_assoc] using bound

/-- A lower-bound position partitions the interval into keys below the target
and keys at least the target. The right endpoint is a valid empty suffix. -/
def LowerBound (a : Seq) (lo : Int) (n : Nat) (key : Int) (k : Nat) : Prop :=
  k ≤ n ∧ (∀ i : Nat, i < k → a (lo + i) < key) ∧
    (∀ i : Nat, k ≤ i → i < n → key ≤ a (lo + i))

@[simp] theorem LowerBound.zero (a : Seq) (lo key : Int) : LowerBound a lo 0 key 0 := by
  simp [LowerBound]

/-- Search the lower half when the pivot is already at least the target. -/
theorem LowerBound.left (a : Seq) (lo : Int) (n pivot k : Nat) (key : Int)
    (sorted : (interval a lo n).Pairwise (· ≤ ·)) (hp : pivot < n)
    (comparison : key ≤ a (lo + pivot)) (sub : LowerBound a lo pivot key k) :
    LowerBound a lo n key k := by
  refine ⟨by have := sub.1; omega, sub.2.1, ?_⟩
  intro i lower upper
  by_cases small : i < pivot
  · exact sub.2.2 i lower small
  · exact Int.le_trans comparison (sorted_interval_mono a lo n sorted pivot i (by omega) upper)

/-- Search above the pivot when it is strictly below the target. -/
theorem LowerBound.right (a : Seq) (lo : Int) (n pivot k : Nat) (key : Int)
    (sorted : (interval a lo n).Pairwise (· ≤ ·)) (hp : pivot < n)
    (comparison : a (lo + pivot) < key)
    (sub : LowerBound a (lo + pivot + 1) (n-pivot-1) key k) :
    LowerBound a lo n key (pivot + 1 + k) := by
  refine ⟨by have := sub.1; omega, ?_, ?_⟩
  · intro i upper
    by_cases small : i ≤ pivot
    · exact Int.lt_of_le_of_lt (sorted_interval_mono a lo n sorted i pivot small hp) comparison
    · have below : i-pivot-1 < k := by omega
      have result := sub.2.1 (i-pivot-1) below
      have index : lo + (pivot : Int) + 1 + ((i-pivot-1 : Nat) : Int) = lo + i := by omega
      rwa [index] at result
  · intro i lower upper
    have result := sub.2.2 (i-pivot-1) (by omega) (by omega)
    have index : lo + (pivot : Int) + 1 + ((i-pivot-1 : Nat) : Int) = lo + i := by omega
    rwa [index] at result

/-- Sorted output with exactly the input multiset, including duplicate keys. -/
def MergeResult (first second output : List Int) : Prop :=
  output.Pairwise (· ≤ ·) ∧ output.Perm (first ++ second)

/-- The ordinary reusable sorting specification. -/
def SortResult (input output : List Int) : Prop :=
  output.Pairwise (· ≤ ·) ∧ output.Perm input

theorem MergeResult.length {first second output : List Int}
    (result : MergeResult first second output) : output.length = first.length + second.length := by
  simpa using result.2.length_eq

theorem MergeResult.swap {first second output : List Int}
    (result : MergeResult first second output) : MergeResult second first output :=
  ⟨result.1, result.2.trans List.perm_append_comm⟩

theorem sorted_pivot_append (left right : List Int) (pivot : Int)
    (sl : left.Pairwise (· ≤ ·)) (sr : right.Pairwise (· ≤ ·))
    (bl : ∀ x ∈ left, x ≤ pivot) (br : ∀ x ∈ right, pivot ≤ x) :
    (left ++ pivot :: right).Pairwise (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨sl, List.pairwise_cons.mpr ⟨br, sr⟩, ?_⟩
  intro x hx y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact bl x hx
  · exact Int.le_trans (bl x hx) (br y hy)

private theorem pivot_permutation (a b c d : List Int) (pivot : Int) :
    ((a ++ c) ++ pivot :: (b ++ d)).Perm ((a ++ pivot :: b) ++ (c ++ d)) := by
  simp only [List.append_assoc, List.cons_append]
  apply List.Perm.append_left a
  apply List.Perm.trans List.perm_middle
  apply List.Perm.cons
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := c) (l₂ := b)).append_right d

/-- Combine the two independently merged halves around the selected pivot. -/
theorem pivot_merge (a b c d left right : List Int) (pivot : Int)
    (firstSorted : (a ++ pivot :: b).Pairwise (· ≤ ·))
    (secondLow : ∀ x ∈ c, x < pivot) (secondHigh : ∀ x ∈ d, pivot ≤ x)
    (leftResult : MergeResult a c left) (rightResult : MergeResult b d right) :
    MergeResult (a ++ pivot :: b) (c ++ d) (left ++ pivot :: right) := by
  have firstParts := List.pairwise_append.mp firstSorted
  have leftBound : ∀ x ∈ left, x ≤ pivot := by
    intro x hx
    rcases List.mem_append.mp (leftResult.2.mem_iff.mp hx) with ha | hc
    · exact firstParts.2.2 x ha pivot (by simp)
    · exact Int.le_of_lt (secondLow x hc)
  have rightBound : ∀ x ∈ right, pivot ≤ x := by
    intro x hx
    rcases List.mem_append.mp (rightResult.2.mem_iff.mp hx) with hb | hd
    · exact (List.pairwise_cons.mp firstParts.2.1).1 x hb
    · exact secondHigh x hd
  refine ⟨sorted_pivot_append left right pivot leftResult.1 rightResult.1 leftBound rightBound, ?_⟩
  exact (leftResult.2.append (List.Perm.cons pivot rightResult.2)).trans
    (pivot_permutation a b c d pivot)

/-- Source-indexed form of pivot merge, directly matching the CLRS recursive
intervals. Lower-bound search supplies the split in the second sorted input. -/
theorem merge_slices (a : Seq) (lo1 lo2 : Int) (m n k j : Nat) (left right : List Int)
    (pivotValid : k < m)
    (firstSorted : (interval a lo1 m).Pairwise (· ≤ ·))
    (bound : LowerBound a lo2 n (a (lo1 + k)) j)
    (leftResult : MergeResult (interval a lo1 k) (interval a lo2 j) left)
    (rightResult : MergeResult (interval a (lo1 + k + 1) (m-k-1))
      (interval a (lo2 + j) (n-j)) right) :
    MergeResult (interval a lo1 m) (interval a lo2 n)
      (left ++ a (lo1 + k) :: right) := by
  have first := interval_pivot a lo1 m k pivotValid
  have second := interval_split a lo2 n j bound.1
  rw [first, second]
  apply pivot_merge _ _ _ _ left right (a (lo1 + k))
  · rwa [← first]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (mem_interval a lo2 j x).mp hx
    exact bound.2.1 i hi
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (mem_interval a (lo2 + j) (n-j) x).mp hx
    have high := bound.2.2 (j + i) (by omega) (by omega)
    simpa only [Int.natCast_add, Int.add_assoc] using high
  · exact leftResult
  · exact rightResult

/-- Reuse independently sorted halves, then merge their outputs. -/
theorem sort_merge (a b left right output : List Int)
    (leftResult : SortResult a left) (rightResult : SortResult b right)
    (merged : MergeResult left right output) : SortResult (a ++ b) output :=
  ⟨merged.1, merged.2.trans (leftResult.2.append rightResult.2)⟩

end Algo2Lean.ParallelMerge
