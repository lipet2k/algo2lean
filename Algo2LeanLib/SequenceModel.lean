import Algo2Lean
import Init.Data.List.Perm

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


namespace Algo2LeanCore.SequenceModel

open Algo2LeanGenerated

/-- Read a finite interval of an infinite integer-indexed sequence. -/
def interval (a : Seq) (first : Int) : Nat → List Int
  | 0 => []
  | count + 1 => a first :: interval a (first + 1) count

@[simp] theorem interval_length (a : Seq) (first : Int) (count : Nat) :
    (interval a first count).length = count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih => simp [interval, ih]

theorem interval_append (a : Seq) (first : Int) (left right : Nat) :
    interval a first (left + right) =
      interval a first left ++ interval a (first + (left : Int)) right := by
  induction left generalizing first with
  | zero => simp [interval]
  | succ left ih =>
    simp only [Nat.succ_add, interval, List.cons_append, ih]
    congr 3 <;> omega

theorem interval_congr (a b : Seq) (first : Int) (count : Nat)
    (same : ∀ i, first ≤ i → i < first + (count : Int) → a i = b i) :
    interval a first count = interval b first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    simp only [interval]
    congr 1
    · exact same first (by omega) (by omega)
    · exact ih (first + 1) (fun i low high => same i (by omega) (by omega))

def Sorted (a : Seq) (first : Int) (count : Nat) : Prop :=
  (interval a first count).Pairwise (· ≤ ·)

/-- Sorting preserves the multiset in the interval and all outside values. -/
def SortedPermutation (before after : Seq) (first : Int) (count : Nat) : Prop :=
  (interval after first count).Pairwise (· ≤ ·) ∧
    (interval after first count).Perm (interval before first count) ∧
    ∀ i, i < first ∨ first + (count : Int) ≤ i → after i = before i

theorem value_mem (a : Seq) (first : Int) (count : Nat) (index : Int)
    (low : first ≤ index) (high : index < first + (count : Int)) :
    a index ∈ interval a first count := by
  induction count generalizing first with
  | zero => omega
  | succ count ih =>
    by_cases equal : index = first
    · subst index; simp [interval]
    · exact List.mem_cons_of_mem _ (ih (first + 1) (by omega) (by omega))

theorem sorted_tail (a : Seq) (first : Int) (count : Nat)
    (sorted : Sorted a first (count + 1)) : Sorted a (first + 1) count :=
  (List.pairwise_cons.mp sorted).2

theorem head_le (a : Seq) (first : Int) (count : Nat)
    (sorted : Sorted a first (count + 1)) (index : Int)
    (low : first ≤ index) (high : index < first + ((count + 1 : Nat) : Int)) :
    a first ≤ a index := by
  by_cases equal : index = first
  · subst index; exact Int.le_refl _
  · exact (List.pairwise_cons.mp sorted).1 _
      (value_mem a (first + 1) count index (by omega) (by omega))

/-- The finite-list sortedness used by sorting supplies the index-wise order
    used by independently proved searches. -/
theorem sorted_indices (a : Seq) (first : Int) (count : Nat)
    (sorted : Sorted a first count) (left right : Int)
    (low : first ≤ left) (ordered : left ≤ right) (high : right < first + (count : Int)) :
    a left ≤ a right := by
  induction count generalizing first with
  | zero => omega
  | succ count ih =>
    by_cases equal : left = first
    · subst left
      exact head_le a first count sorted right ordered high
    · exact ih (first + 1) (sorted_tail a first count sorted) (by omega) (by omega)

/-- A lower bound partitions a sorted interval at its first value at least key. -/
def LowerBound (a : Seq) (first : Int) (count : Nat) (key result : Int) : Prop :=
  first ≤ result ∧ result ≤ first + (count : Int) ∧
    (∀ index, first ≤ index → index < result → a index < key) ∧
    (∀ index, result ≤ index → index < first + (count : Int) → key ≤ a index)

end Algo2LeanCore.SequenceModel
