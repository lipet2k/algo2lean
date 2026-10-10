import Algo2LeanLib.HeapFrame

namespace Algo2LeanGenerated

/-- Allocation-aware framing. Every previously allocated location outside the
    listed footprint keeps its contents; all existing object and collection
    type tags survive. Fresh locations may be allocated and initialized.
    Clocks have a separate contract and are intentionally unconstrained here. -/
structure Heap.Footprint (before after : Heap) (sequences : List SeqRef)
    (objects : List ObjectRef) (collections : List CollectionRef) : Prop where
  nextRef : before.nextRef ≤ after.nextRef
  nextObject : before.nextObject ≤ after.nextObject
  nextCollection : before.nextCollection ≤ after.nextCollection
  classes : ∀ ref, ref < before.nextObject → after.objectClass ref = before.objectClass ref
  types : ∀ ref, ref < before.nextCollection → after.sequenceType ref = before.sequenceType ref
  otherSequences : ∀ ref, ref < before.nextRef → ref ∉ sequences → after.store ref = before.store ref
  otherObjects : ∀ ref, ref < before.nextObject → ref ∉ objects → after.objects ref = before.objects ref
  otherCollections : ∀ ref, ref < before.nextCollection → ref ∉ collections →
    after.collections ref = before.collections ref

namespace Heap.Footprint

variable {before middle after : Heap} {sequences : List SeqRef}
  {objects : List ObjectRef} {collections : List CollectionRef}

theorem refl (heap : Heap) (sequences : List SeqRef) (objects : List ObjectRef)
    (collections : List CollectionRef) : heap.Footprint heap sequences objects collections :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem trans (first : before.Footprint middle sequences objects collections)
    (second : middle.Footprint after sequences objects collections) :
    before.Footprint after sequences objects collections :=
  ⟨Nat.le_trans first.nextRef second.nextRef,
    Nat.le_trans first.nextObject second.nextObject,
    Nat.le_trans first.nextCollection second.nextCollection,
    fun ref old => (second.classes ref (Nat.lt_of_lt_of_le old first.nextObject)).trans
      (first.classes ref old),
    fun ref old => (second.types ref (Nat.lt_of_lt_of_le old first.nextCollection)).trans
      (first.types ref old),
    fun ref old outside =>
      (second.otherSequences ref (Nat.lt_of_lt_of_le old first.nextRef) outside).trans
        (first.otherSequences ref old outside),
    fun ref old outside =>
      (second.otherObjects ref (Nat.lt_of_lt_of_le old first.nextObject) outside).trans
        (first.otherObjects ref old outside),
    fun ref old outside =>
      (second.otherCollections ref (Nat.lt_of_lt_of_le old first.nextCollection) outside).trans
        (first.otherCollections ref old outside)⟩

/-- A caller may reserve more locations than a callee actually changes. -/
theorem weaken (frame : before.Footprint after sequences objects collections)
    {moreSequences : List SeqRef} {moreObjects : List ObjectRef}
    {moreCollections : List CollectionRef}
    (seqs : ∀ ref ∈ sequences, ref ∈ moreSequences)
    (objs : ∀ ref ∈ objects, ref ∈ moreObjects)
    (colls : ∀ ref ∈ collections, ref ∈ moreCollections) :
    before.Footprint after moreSequences moreObjects moreCollections :=
  ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.classes, frame.types,
    fun ref old outside => frame.otherSequences ref old (fun member => outside (seqs ref member)),
    fun ref old outside => frame.otherObjects ref old (fun member => outside (objs ref member)),
    fun ref old outside => frame.otherCollections ref old (fun member => outside (colls ref member))⟩

theorem tick (frame : before.Footprint after sequences objects collections)
    (clock : String) (amount : Nat := 1) :
    before.Footprint (after.tick clock amount) sequences objects collections :=
  ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.classes, frame.types,
    frame.otherSequences, frame.otherObjects, frame.otherCollections⟩

theorem charge (frame : before.Footprint after sequences objects collections) (costs : Clocks) :
    before.Footprint (after.charge costs) sequences objects collections :=
  ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.classes, frame.types,
    frame.otherSequences, frame.otherObjects, frame.otherCollections⟩

/-- A write may target owned storage or storage allocated during this segment. -/
theorem write (frame : before.Footprint after sequences objects collections)
    (ref : SeqRef) (index value : Int) (allowed : ref ∈ sequences ∨ before.nextRef ≤ ref) :
    before.Footprint (after.write ref index value) sequences objects collections := by
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.classes, frame.types,
    ?_, frame.otherObjects, frame.otherCollections⟩
  intro other old outside
  have different : other ≠ ref := by
    intro same
    subst other
    rcases allowed with owned | fresh
    · exact outside owned
    · omega
  simpa only [Heap.write, different, false_and, if_false] using frame.otherSequences other old outside

theorem writeField (frame : before.Footprint after sequences objects collections)
    (ref : ObjectRef) (field : String) (value : ObjectValue)
    (allowed : ref ∈ objects ∨ before.nextObject ≤ ref) :
    before.Footprint (after.writeField ref field value) sequences objects collections := by
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, ?_, frame.types,
    frame.otherSequences, ?_, frame.otherCollections⟩
  · intro other old
    rw [Heap.objectClass_writeField]
    exact frame.classes other old
  · intro other old outside
    have different : other ≠ ref := by
      intro same
      subst other
      rcases allowed with owned | fresh
      · exact outside owned
      · omega
    simpa only [Heap.writeField, if_neg different] using frame.otherObjects other old outside

theorem writeElement (frame : before.Footprint after sequences objects collections)
    (ref : CollectionRef) (index : Int) (value : ObjectValue)
    (allowed : ref ∈ collections ∨ before.nextCollection ≤ ref) :
    before.Footprint (after.writeElement ref index value) sequences objects collections := by
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.classes, ?_,
    frame.otherSequences, frame.otherObjects, ?_⟩
  · intro other old
    rw [Heap.sequenceType_writeElement]
    exact frame.types other old
  · intro other old outside
    have different : other ≠ ref := by
      intro same
      subst other
      rcases allowed with owned | fresh
      · exact outside owned
      · omega
    simpa only [Heap.writeElement, if_neg different] using frame.otherCollections other old outside

theorem allocate (frame : before.Footprint after sequences objects collections) (contents : Seq) :
    before.Footprint (after.allocate contents) sequences objects collections := by
  refine ⟨Nat.le_trans frame.nextRef (Nat.le_succ _), frame.nextObject,
    frame.nextCollection, frame.classes, frame.types, ?_, frame.otherObjects, frame.otherCollections⟩
  intro ref old outside
  have different := Nat.ne_of_lt (Nat.lt_of_lt_of_le old frame.nextRef)
  simpa only [Heap.allocate, if_neg different] using frame.otherSequences ref old outside

theorem allocateObject (frame : before.Footprint after sequences objects collections)
    (className : String) :
    before.Footprint (after.allocateObject className) sequences objects collections := by
  refine ⟨frame.nextRef, Nat.le_trans frame.nextObject (Nat.le_succ _),
    frame.nextCollection, ?_, frame.types, frame.otherSequences, ?_, frame.otherCollections⟩
  · intro ref old
    have preserved := Heap.objects_allocateObject_old after className ref
      (Nat.lt_of_lt_of_le old frame.nextObject)
    simpa only [Heap.objectClass, preserved] using frame.classes ref old
  · intro ref old outside
    rw [Heap.objects_allocateObject_old after className ref
      (Nat.lt_of_lt_of_le old frame.nextObject)]
    exact frame.otherObjects ref old outside

theorem allocateSequence (frame : before.Footprint after sequences objects collections)
    (elementType : String) (values : Int → ObjectValue) :
    before.Footprint (after.allocateSequence elementType values) sequences objects collections := by
  refine ⟨frame.nextRef, frame.nextObject, Nat.le_trans frame.nextCollection (Nat.le_succ _),
    frame.classes, ?_, frame.otherSequences, frame.otherObjects, ?_⟩
  · intro ref old
    have preserved := Heap.collections_allocateSequence_old after elementType values ref
      (Nat.lt_of_lt_of_le old frame.nextCollection)
    simpa only [Heap.sequenceType, preserved] using frame.types ref old
  · intro ref old outside
    rw [Heap.collections_allocateSequence_old after elementType values ref
      (Nat.lt_of_lt_of_le old frame.nextCollection)]
    exact frame.otherCollections ref old outside

theorem read (frame : before.Footprint after sequences objects collections)
    (ref : SeqRef) (old : ref < before.nextRef) (outside : ref ∉ sequences) :
    after.read ref = before.read ref := frame.otherSequences ref old outside

theorem readField (frame : before.Footprint after sequences objects collections)
    (ref : ObjectRef) (old : ref < before.nextObject) (outside : ref ∉ objects) (field : String) :
    after.readField ref field = before.readField ref field := by
  simp only [Heap.readField, frame.otherObjects ref old outside]

theorem readElement (frame : before.Footprint after sequences objects collections)
    (ref : CollectionRef) (old : ref < before.nextCollection) (outside : ref ∉ collections)
    (index : Int) : after.readElement ref index = before.readElement ref index := by
  simp only [Heap.readElement, frame.otherCollections ref old outside]

theorem validSequence (frame : before.Footprint after sequences objects collections)
    (ref : CollectionRef) (elementType : String) (valid : before.validSequence ref elementType) :
    after.validSequence ref elementType :=
  ⟨Nat.lt_of_lt_of_le valid.1 frame.nextCollection, (frame.types ref valid.1).trans valid.2⟩

end Heap.Footprint

/-- Existing allocation-free frame contracts can be reused without reproving
    the implementation when a caller accepts an allocation-aware footprint. -/
theorem Heap.Modifies.footprint {before after : Heap} {sequences : List SeqRef}
    {objects : List ObjectRef} (frame : before.Modifies after sequences objects) :
    before.Footprint after sequences objects [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_eq frame.nextRef.symm
  · exact Nat.le_of_eq frame.nextObject.symm
  · exact Nat.le_of_eq frame.nextCollection.symm
  · intro ref _
    exact congrFun frame.classes ref
  · intro ref _
    simp only [Heap.sequenceType, frame.collections]
  · intro ref _ outside
    exact frame.otherSequences ref outside
  · intro ref _ outside
    exact frame.otherObjects ref outside
  · intro ref _ _
    exact congrFun frame.collections ref

end Algo2LeanGenerated
