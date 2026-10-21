import Algo2LeanLib.ParallelSeq
import Algo2LeanLib.ParallelBounds

/-! Precise access bounds for merging two source slices into a disjoint output. -/
namespace Algo2LeanParallel
open Algo2LeanGenerated

/-- Read either input slice and write exactly within the combined output slice. -/
def mergeAccess (source target : SeqRef) (lo1 : Int) (m : Nat)
    (lo2 : Int) (n : Nat) (dst : Int) : Access where
  reads := fun x => ∃ i, x = .seq source i ∧
    ((lo1 ≤ i ∧ i < lo1 + (m : Int)) ∨ (lo2 ≤ i ∧ i < lo2 + (n : Int)))
  writes := fun x => ∃ i, x = .seq target i ∧ dst ≤ i ∧ i < dst + (m + n : Nat)
  allocates := false

theorem mergeAccess_read_left (source target : SeqRef) (lo1 : Int) (m : Nat)
    (lo2 : Int) (n : Nat) (dst i : Int) (lower : lo1 ≤ i) (upper : i < lo1 + m) :
    Access.Within (Access.readSeq source i) (mergeAccess source target lo1 m lo2 n dst) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; cases hx; exact ⟨i, rfl, Or.inl ⟨lower, upper⟩⟩
  · simp [Access.readSeq, Access.read]
  · simp [Access.readSeq, Access.read]

theorem mergeAccess_read_right (source target : SeqRef) (lo1 : Int) (m : Nat)
    (lo2 : Int) (n : Nat) (dst i : Int) (lower : lo2 ≤ i) (upper : i < lo2 + n) :
    Access.Within (Access.readSeq source i) (mergeAccess source target lo1 m lo2 n dst) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; cases hx; exact ⟨i, rfl, Or.inr ⟨lower, upper⟩⟩
  · simp [Access.readSeq, Access.read]
  · simp [Access.readSeq, Access.read]

theorem mergeAccess_write (source target : SeqRef) (lo1 : Int) (m : Nat)
    (lo2 : Int) (n : Nat) (dst i : Int) (lower : dst ≤ i) (upper : i < dst + (m+n : Nat)) :
    Access.Within (Access.writeSeq target i) (mergeAccess source target lo1 m lo2 n dst) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Access.writeSeq, Access.write]
  · intro x hx; cases hx; exact ⟨i, rfl, lower, upper⟩
  · simp [Access.writeSeq, Access.write]

theorem readInterval_within_mergeAccess (source target : SeqRef) (lo1 : Int) (m : Nat)
    (lo2 : Int) (n : Nat) (dst : Int) :
    Access.Within (Algo2Lean.ParallelBounds.readInterval source lo2 n)
      (mergeAccess source target lo1 m lo2 n dst) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨i, rfl, lower, upper⟩; exact ⟨i, rfl, Or.inr ⟨lower, upper⟩⟩
  · simp [Algo2Lean.ParallelBounds.readInterval]
  · simp [Algo2Lean.ParallelBounds.readInterval]

theorem mergeAccess_mono (source target : SeqRef)
    (lo1 lo2 dst outer1 outer2 output : Int) (m n size1 size2 : Nat)
    (l1 : outer1 ≤ lo1) (u1 : lo1+m ≤ outer1+size1)
    (l2 : outer2 ≤ lo2) (u2 : lo2+n ≤ outer2+size2)
    (ld : output ≤ dst) (ud : dst+(m+n : Nat) ≤ output+(size1+size2 : Nat)) :
    Access.Within (mergeAccess source target lo1 m lo2 n dst)
      (mergeAccess source target outer1 size1 outer2 size2 output) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨i, rfl, h | h⟩
    · exact ⟨i, rfl, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨i, rfl, Or.inr ⟨by omega, by omega⟩⟩
  · rintro x ⟨i, rfl, lower, upper⟩; exact ⟨i, rfl, by omega, by omega⟩
  · simp [mergeAccess]

theorem mergeAccess_swap (source target : SeqRef) (lo1 : Int) (m : Nat)
    (lo2 : Int) (n : Nat) (dst : Int) :
    mergeAccess source target lo1 m lo2 n dst = mergeAccess source target lo2 n lo1 m dst := by
  simp [mergeAccess, or_comm, Nat.add_comm]

/-- Read sharing is harmless; disjoint output slices exclude every cross-branch write conflict. -/
theorem mergeAccess_compatible (source target : SeqRef)
    (lo1 lo2 dst lo1' lo2' dst' : Int) (m n m' n' : Nat)
    (different : source ≠ target) (separate : dst + (m+n : Nat) ≤ dst') :
    Access.Compatible (mergeAccess source target lo1 m lo2 n dst)
      (mergeAccess source target lo1' m' lo2' n' dst') := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rintro x ⟨i, rfl, lower, upper⟩
    constructor
    · rintro ⟨j, equal, _⟩; cases equal; exact different rfl
    · rintro ⟨j, equal, lower', upper'⟩; cases equal; omega
  · rintro x ⟨i, rfl, lower, upper⟩
    constructor
    · rintro ⟨j, equal, _⟩; cases equal; exact different rfl
    · rintro ⟨j, equal, lower', upper'⟩; cases equal; omega

end Algo2LeanParallel
