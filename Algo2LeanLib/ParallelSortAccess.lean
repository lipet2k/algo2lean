import Algo2LeanLib.ParallelMergeAccess

/-! Preservation and access bounds for two reusable parallel sorting buffers. -/
namespace Algo2LeanParallel
open Algo2LeanGenerated

/-- Only the indicated interval of two buffers may change. -/
structure BuffersFrame (before after : Heap) (first second : SeqRef) (lo : Int) (n : Nat) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  clocks : after.clocks = before.clocks
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections
  outside : ∀ ref i, (ref ≠ first ∧ ref ≠ second) ∨ i < lo ∨ lo + (n : Int) ≤ i →
    after.read ref i = before.read ref i

namespace BuffersFrame

theorem refl (h : Heap) (first second : SeqRef) (lo : Int) (n : Nat) :
    BuffersFrame h h first second lo n :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem symm_buffers {h f : Heap} {first second : SeqRef} {lo : Int} {n : Nat}
    (frame : BuffersFrame h f first second lo n) : BuffersFrame h f second first lo n := by
  refine ⟨frame.nextRef, frame.nextObject, frame.objects, frame.clocks,
    frame.nextCollection, frame.collections, ?_⟩
  intro ref i outside
  apply frame.outside
  rcases outside with other | low | high
  · exact Or.inl other.symm
  · exact Or.inr (Or.inl low)
  · exact Or.inr (Or.inr high)

theorem trans {h m f : Heap} {first second : SeqRef} {lo : Int} {n : Nat}
    (a : BuffersFrame h m first second lo n) (b : BuffersFrame m f first second lo n) :
    BuffersFrame h f first second lo n :=
  ⟨b.nextRef.trans a.nextRef, b.nextObject.trans a.nextObject, b.objects.trans a.objects,
   b.clocks.trans a.clocks, b.nextCollection.trans a.nextCollection,
   b.collections.trans a.collections, fun r i outside => (b.outside r i outside).trans (a.outside r i outside)⟩

theorem weaken {h f : Heap} {first second : SeqRef} {lo outer : Int} {n size : Nat}
    (frame : BuffersFrame h f first second lo n) (lower : outer ≤ lo)
    (upper : lo + n ≤ outer + size) : BuffersFrame h f first second outer size := by
  refine ⟨frame.nextRef, frame.nextObject, frame.objects, frame.clocks,
    frame.nextCollection, frame.collections, ?_⟩
  intro ref i outside
  apply frame.outside
  rcases outside with other | low | high
  · exact Or.inl other
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem of_seq {h f : Heap} {first : SeqRef} {lo : Int} {n : Nat}
    (frame : SeqFrame h f first lo n) (second : SeqRef) :
    BuffersFrame h f first second lo n := by
  refine ⟨frame.nextRef, frame.nextObject, frame.objects, frame.clocks,
    frame.nextCollection, frame.collections, ?_⟩
  intro ref i outside
  apply frame.outside
  rcases outside with other | low | high
  · exact Or.inl other.1
  · exact Or.inr (Or.inl low)
  · exact Or.inr (Or.inr high)

theorem read_other {h f : Heap} {first second ref : SeqRef} {lo : Int} {n : Nat}
    (frame : BuffersFrame h f first second lo n) (a : ref ≠ first) (b : ref ≠ second) :
    f.read ref = h.read ref := by
  funext i
  exact frame.outside ref i (Or.inl ⟨a, b⟩)

end BuffersFrame

/-- Sorting reads the immutable source and either buffer, and writes only the
buffers. Every access stays within the current interval. -/
def sortAccess (source first second : SeqRef) (lo : Int) (n : Nat) : Access where
  reads := fun location => ∃ ref i, location = .seq ref i ∧
    (ref = source ∨ ref = first ∨ ref = second) ∧ lo ≤ i ∧ i < lo + (n : Int)
  writes := fun location => ∃ ref i, location = .seq ref i ∧
    (ref = first ∨ ref = second) ∧ lo ≤ i ∧ i < lo + (n : Int)
  allocates := false

theorem sortAccess_swap (source first second : SeqRef) (lo : Int) (n : Nat) :
    Access.Within (sortAccess source first second lo n) (sortAccess source second first lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨ref, i, rfl, which, low, high⟩
    exact ⟨ref, i, rfl, which.elim Or.inl (fun h => Or.inr h.symm), low, high⟩
  · rintro x ⟨ref, i, rfl, which, low, high⟩
    exact ⟨ref, i, rfl, which.symm, low, high⟩
  · simp [sortAccess]

theorem sortAccess_mono (source first second : SeqRef) (lo outer : Int) (n size : Nat)
    (lower : outer ≤ lo) (upper : lo + n ≤ outer + size) :
    Access.Within (sortAccess source first second lo n) (sortAccess source first second outer size) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨ref, i, rfl, which, low, high⟩
    exact ⟨ref, i, rfl, which, by omega, by omega⟩
  · rintro x ⟨ref, i, rfl, which, low, high⟩
    exact ⟨ref, i, rfl, which, by omega, by omega⟩
  · simp [sortAccess]

theorem sortAccess_compatible (source first second : SeqRef) (left right : Int) (m n : Nat)
    (disjoint : left + m ≤ right) :
    Access.Compatible (sortAccess source first second left m) (sortAccess source first second right n) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rintro x ⟨ref, i, rfl, _, low, high⟩
    constructor <;> rintro ⟨other, j, equal, _, low', high'⟩ <;> cases equal <;> omega
  · rintro x ⟨ref, i, rfl, _, low, high⟩
    constructor <;> rintro ⟨other, j, equal, _, low', high'⟩ <;> cases equal <;> omega

theorem sortAccess_read (source first second ref : SeqRef) (lo : Int) (n : Nat) (i : Int)
    (which : ref = source ∨ ref = first ∨ ref = second) (low : lo ≤ i) (high : i < lo + n) :
    Access.Within (Access.readSeq ref i) (sortAccess source first second lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x same; cases same; exact ⟨ref, i, rfl, which, low, high⟩
  · simp [Access.readSeq, Access.read]
  · simp [Access.readSeq, Access.read]

theorem sortAccess_write (source first second ref : SeqRef) (lo : Int) (n : Nat) (i : Int)
    (which : ref = first ∨ ref = second) (low : lo ≤ i) (high : i < lo + n) :
    Access.Within (Access.writeSeq ref i) (sortAccess source first second lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Access.writeSeq, Access.write]
  · intro x same; cases same; exact ⟨ref, i, rfl, which, low, high⟩
  · simp [Access.writeSeq, Access.write]

/-- A merge of adjacent buffer intervals fits the sorting access contract. -/
theorem mergeAccess_within_sort (source first second : SeqRef) (lo : Int) (m n : Nat) :
    Access.Within (mergeAccess second first lo m (lo + m) n lo)
      (sortAccess source first second lo (m+n)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨i, rfl, lowHigh | lowHigh⟩
    · exact ⟨second, i, rfl, Or.inr (Or.inr rfl), lowHigh.1, by omega⟩
    · exact ⟨second, i, rfl, Or.inr (Or.inr rfl), by omega, by omega⟩
  · rintro x ⟨i, rfl, low, high⟩
    exact ⟨first, i, rfl, Or.inl rfl, low, high⟩
  · simp [mergeAccess]

end Algo2LeanParallel
