import Algo2LeanLib.Parallel

/-! Slice preservation and access permissions for preallocated parallel arrays. -/
namespace Algo2LeanParallel
open Algo2LeanGenerated

/-- Exactly one sequence slice may change; all metadata, other storage, and
caller counters retain their original values. -/
structure SeqFrame (before after : Heap) (target : SeqRef) (lo : Int) (n : Nat) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  clocks : after.clocks = before.clocks
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections
  outside : ∀ ref i, ref ≠ target ∨ i < lo ∨ lo + (n : Int) ≤ i → after.read ref i = before.read ref i

namespace SeqFrame

theorem refl (h : Heap) (target : SeqRef) (lo : Int) (n : Nat) : SeqFrame h h target lo n :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem trans {h m f : Heap} {target : SeqRef} {lo : Int} {n : Nat}
    (a : SeqFrame h m target lo n) (b : SeqFrame m f target lo n) : SeqFrame h f target lo n :=
  ⟨b.nextRef.trans a.nextRef, b.nextObject.trans a.nextObject, b.objects.trans a.objects,
   b.clocks.trans a.clocks, b.nextCollection.trans a.nextCollection,
   b.collections.trans a.collections, fun r i outside => (b.outside r i outside).trans (a.outside r i outside)⟩

theorem weaken {h f : Heap} {target : SeqRef} {lo outer : Int} {n size : Nat}
    (frame : SeqFrame h f target lo n) (lower : outer ≤ lo) (upper : lo + n ≤ outer + size) :
    SeqFrame h f target outer size := by
  refine ⟨frame.nextRef, frame.nextObject, frame.objects, frame.clocks, frame.nextCollection,
    frame.collections, ?_⟩
  intro r i outside
  apply frame.outside r i
  rcases outside with other | low | high
  · exact Or.inl other
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem write (h : Heap) (target : SeqRef) (lo : Int) (n : Nat) (i value : Int)
    (lower : lo ≤ i) (upper : i < lo + n) : SeqFrame h (h.write target i value) target lo n := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro ref index outside
  simp only [Heap.read, Heap.write]
  split
  · rename_i hit
    rcases outside with other | low | high <;> simp_all <;> omega
  · rfl

theorem read_other {h f : Heap} {target ref : SeqRef} {lo : Int} {n : Nat}
    (frame : SeqFrame h f target lo n) (different : ref ≠ target) : f.read ref = h.read ref := by
  funext i
  exact frame.outside ref i (Or.inl different)

end SeqFrame

/-- A branch may read its source interval and write its output interval. -/
def sliceAccess (source target : SeqRef) (lo : Int) (n : Nat) : Access where
  reads := fun location => ∃ i, location = .seq source i ∧ lo ≤ i ∧ i < lo + (n : Int)
  writes := fun location => ∃ i, location = .seq target i ∧ lo ≤ i ∧ i < lo + (n : Int)
  allocates := false

theorem sliceAccess_mono (source target : SeqRef) (lo outer : Int) (n size : Nat)
    (lower : outer ≤ lo) (upper : lo + n ≤ outer + size) :
    Access.Within (sliceAccess source target lo n) (sliceAccess source target outer size) := by
  constructor
  · rintro x ⟨i, rfl, a, b⟩; exact ⟨i, rfl, by omega, by omega⟩
  constructor
  · rintro x ⟨i, rfl, a, b⟩; exact ⟨i, rfl, by omega, by omega⟩
  · simp [sliceAccess]

theorem readSeq_within_slice (source target : SeqRef) (lo : Int) (n : Nat) (i : Int)
    (lower : lo ≤ i) (upper : i < lo + n) :
    Access.Within (Access.readSeq source i) (sliceAccess source target lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; cases hx; exact ⟨i, rfl, lower, upper⟩
  · simp [Access.readSeq, Access.read]
  · simp [Access.readSeq, Access.read]

theorem writeSeq_within_slice (source target : SeqRef) (lo : Int) (n : Nat) (i : Int)
    (lower : lo ≤ i) (upper : i < lo + n) :
    Access.Within (Access.writeSeq target i) (sliceAccess source target lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Access.writeSeq, Access.write]
  · intro x hx; cases hx; exact ⟨i, rfl, lower, upper⟩
  · simp [Access.writeSeq, Access.write]

/-- Adjacent branches can share their read-only source, but their target must
be a different sequence and their writable intervals must not overlap. -/
theorem sliceAccess_compatible (source target : SeqRef) (left right : Int) (m n : Nat)
    (different : source ≠ target) (disjoint : left + m ≤ right) :
    Access.Compatible (sliceAccess source target left m) (sliceAccess source target right n) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rintro x ⟨i, rfl, lower, upper⟩
    constructor
    · rintro ⟨j, equal, _, _⟩; cases equal; exact different rfl
    · rintro ⟨j, equal, lower', upper'⟩; cases equal; omega
  · rintro x ⟨i, rfl, lower, upper⟩
    constructor
    · rintro ⟨j, equal, _, _⟩; cases equal; exact different rfl
    · rintro ⟨j, equal, lower', upper'⟩; cases equal; omega

end Algo2LeanParallel
