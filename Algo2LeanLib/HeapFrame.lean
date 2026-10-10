import Algo2Lean

namespace Algo2LeanGenerated

/-- A local storage footprint: only the listed sequences and objects may change.
    Allocation, classes, and object collections stay fixed. Clocks are handled by
    a separate cost contract, so the same frame applies to every cost model. -/
structure Heap.Modifies (before after : Heap) (sequences : List SeqRef)
    (objects : List ObjectRef) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections
  classes : after.objectClass = before.objectClass
  otherSequences : ∀ ref, ref ∉ sequences → after.store ref = before.store ref
  otherObjects : ∀ ref, ref ∉ objects → after.objects ref = before.objects ref

namespace Heap.Modifies

theorem refl (heap : Heap) (sequences : List SeqRef) (objects : List ObjectRef) :
    heap.Modifies heap sequences objects :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans {before middle after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (first : before.Modifies middle sequences objects)
    (second : middle.Modifies after sequences objects) : before.Modifies after sequences objects :=
  ⟨second.nextRef.trans first.nextRef, second.nextObject.trans first.nextObject,
    second.nextCollection.trans first.nextCollection, second.collections.trans first.collections,
    second.classes.trans first.classes,
    fun ref outside => (second.otherSequences ref outside).trans (first.otherSequences ref outside),
    fun ref outside => (second.otherObjects ref outside).trans (first.otherObjects ref outside)⟩

theorem tick {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (clock : String) (amount : Nat := 1) :
    before.Modifies (after.tick clock amount) sequences objects :=
  ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.collections,
    frame.classes, frame.otherSequences, frame.otherObjects⟩

theorem write {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : SeqRef) (index value : Int)
    (allowed : ref ∈ sequences) : before.Modifies (after.write ref index value) sequences objects := by
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.collections,
    frame.classes, ?_, frame.otherObjects⟩
  intro other outside
  have different : other ≠ ref := by intro same; exact outside (same ▸ allowed)
  simpa only [Heap.write, different, false_and, if_false] using frame.otherSequences other outside

theorem writeField {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : ObjectRef) (field : String)
    (value : ObjectValue) (allowed : ref ∈ objects) :
    before.Modifies (after.writeField ref field value) sequences objects := by
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.collections,
    ?_, frame.otherSequences, ?_⟩
  · funext other
    rw [Heap.objectClass_writeField]
    exact congrFun frame.classes other
  · intro other outside
    have different : other ≠ ref := by intro same; exact outside (same ▸ allowed)
    simpa only [Heap.writeField, if_neg different] using frame.otherObjects other outside

theorem read {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : SeqRef) (outside : ref ∉ sequences) :
    after.read ref = before.read ref := frame.otherSequences ref outside

theorem readField {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : ObjectRef) (outside : ref ∉ objects)
    (field : String) : after.readField ref field = before.readField ref field := by
  simp only [Heap.readField, frame.otherObjects ref outside]

end Heap.Modifies
end Algo2LeanGenerated
