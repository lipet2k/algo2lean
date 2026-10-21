import Algo2Lean

/-! Heap views shared by the array-of-arrays matrix examples. Input rows may
alias. Preservation concerns every allocated input object, not just the two
outer array references. Counter changes are stated separately by each program. -/

namespace Algo2LeanCore.MatrixHeap

open Algo2LeanGenerated

abbrev Values := Int → Int → Int

/-- The canonical element descriptor emitted for `Seq[Seq[Int]]`. -/
def rows : SequenceType SeqRef where
  name := "Seq[Int]"
  encode := ObjectValue.seqValue
  decode := ObjectValue.asSeq
  decode_encode := by intro value; rfl

/-- A well-formed outer array and its mathematical row values. Row references
need not be distinct; this includes shared rows and aliased input matrices. -/
def Stored (h : Heap) (matrix : CollectionRef) (values : Values) : Prop :=
  rows.valid h matrix ∧ ∀ i, ∃ row,
    rows.get h matrix i = some row ∧ row < h.nextRef ∧ h.store row = values i

/-- Observe one nested matrix entry. `Stored` hypotheses guarantee that the
outer and row references are valid, so the decoder fallback is never used. -/
def cell (h : Heap) (matrix : CollectionRef) (i j : Int) : Int :=
  h.read ((rows.get h matrix i).getD 0) j

/-- Old arrays, rows, and objects survive unchanged while fresh arrays/rows may
be allocated. Clocks can change, and are specified independently. -/
structure Extends (before after : Heap) : Prop where
  nextRef : before.nextRef ≤ after.nextRef
  nextCollection : before.nextCollection ≤ after.nextCollection
  store : ∀ r, r < before.nextRef → after.store r = before.store r
  collections : ∀ r, r < before.nextCollection → after.collections r = before.collections r
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects

theorem Extends.refl (h : Heap) : Extends h h :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Extends.trans {a b c : Heap} (first : Extends a b) (second : Extends b c) :
    Extends a c := by
  refine ⟨Nat.le_trans first.nextRef second.nextRef,
    Nat.le_trans first.nextCollection second.nextCollection, ?_, ?_,
    second.nextObject.trans first.nextObject, second.objects.trans first.objects⟩
  · intro r valid
    exact (second.store r (Nat.lt_of_lt_of_le valid first.nextRef)).trans (first.store r valid)
  · intro r valid
    exact (second.collections r (Nat.lt_of_lt_of_le valid first.nextCollection)).trans
      (first.collections r valid)

theorem Extends.valid {before after : Heap} (extension : Extends before after)
    {matrix : CollectionRef} (valid : rows.valid before matrix) : rows.valid after matrix := by
  refine ⟨Nat.lt_of_lt_of_le valid.1 extension.nextCollection, ?_⟩
  unfold Heap.sequenceType
  rw [extension.collections matrix valid.1]
  exact valid.2

theorem Extends.get {before after : Heap} (extension : Extends before after)
    {matrix : CollectionRef} (valid : rows.valid before matrix) (i : Int) :
    rows.get after matrix i = rows.get before matrix i := by
  simp only [SequenceType.get, valid, extension.valid valid, if_pos]
  unfold Heap.readElement
  rw [extension.collections matrix valid.1]

theorem Stored.mono {before after : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored before matrix values) (extension : Extends before after) :
    Stored after matrix values := by
  refine ⟨extension.valid stored.1, ?_⟩
  intro i
  obtain ⟨row, read, valid, contents⟩ := stored.2 i
  exact ⟨row, (extension.get stored.1 i).trans read,
    Nat.lt_of_lt_of_le valid extension.nextRef, (extension.store row valid).trans contents⟩

theorem Stored.row {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i : Int) :
    (rows.get h matrix i).isSome = true := by
  obtain ⟨row, read, _⟩ := stored.2 i
  simp [read]

theorem Stored.row_valid {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i : Int) :
    (rows.get h matrix i).getD 0 < h.nextRef := by
  obtain ⟨row, read, valid, _⟩ := stored.2 i
  simpa [read] using valid

theorem Stored.read {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i j : Int) :
    h.read ((rows.get h matrix i).getD 0) j = values i j := by
  obtain ⟨row, read, _, contents⟩ := stored.2 i
  simp [read, Heap.read, contents]

theorem Stored.unique {h : Heap} {matrix : CollectionRef} {a b : Values}
    (first : Stored h matrix a) (second : Stored h matrix b) : a = b := by
  funext i j
  exact (first.read i j).symm.trans (second.read i j)

theorem Stored.cell {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i j : Int) : cell h matrix i j = values i j :=
  stored.read i j

theorem extends_allocate (h : Heap) (values : Seq) : Extends h (h.allocate values) := by
  refine ⟨by simp, Nat.le_refl _, ?_, fun _ _ => rfl, rfl, rfl⟩
  intro r valid
  simp [Heap.allocate, Nat.ne_of_lt valid]

theorem extends_create (h : Heap) (values : Int → SeqRef) : Extends h (rows.create h values).1 := by
  refine ⟨Nat.le_refl _, by simp [SequenceType.create, Heap.createSequence],
    fun _ _ => rfl, ?_, rfl, rfl⟩
  intro r valid
  simp [SequenceType.create, Heap.createSequence, valid]

theorem extends_const (h : Heap) (row : SeqRef) : Extends h (rows.const h row).1 :=
  extends_create h (fun _ => row)

theorem extends_tick (h : Heap) (clock : String) (amount : Nat) : Extends h (h.tick clock amount) :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- Writing a row allocated after the old heap preserves that old heap. -/
theorem Extends.write {before after : Heap} (extension : Extends before after)
    (row : SeqRef) (fresh : before.nextRef ≤ row) (i value : Int) :
    Extends before (after.write row i value) := by
  refine ⟨extension.nextRef, extension.nextCollection, ?_, extension.collections,
    extension.nextObject, extension.objects⟩
  intro r valid
  have different : r ≠ row := by omega
  funext j
  simp [Heap.write, different, extension.store r valid]

/-- Installing a row in a newly allocated outer array preserves old matrices. -/
theorem Extends.set {before after : Heap} (extension : Extends before after)
    (matrix : CollectionRef) (fresh : before.nextCollection ≤ matrix) (i : Int) (row : SeqRef) :
    Extends before (rows.set after matrix i row) := by
  refine ⟨extension.nextRef, extension.nextCollection, extension.store, ?_,
    extension.nextObject, extension.objects⟩
  intro r valid
  have different : r ≠ matrix := by omega
  simp [SequenceType.set, Heap.writeElement, different, extension.collections r valid]

theorem stored_const (h : Heap) (row : SeqRef) (values : Seq) (valid : row < h.nextRef)
    (contents : h.store row = values) :
    Stored (rows.const h row).1 (rows.const h row).2 (fun _ => values) := by
  refine ⟨rows.valid_const h row, ?_⟩
  intro i
  exact ⟨row, rows.get_const h row i, valid, contents⟩

/-- Replace one row reference, leaving every other row value unchanged. -/
theorem Stored.set {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i : Int) (row : SeqRef) (newValues : Seq)
    (valid : row < h.nextRef) (contents : h.store row = newValues) :
    Stored (rows.set h matrix i row) matrix
      (fun j => if j = i then newValues else values j) := by
  refine ⟨(rows.valid_set h matrix matrix i row).mpr stored.1, ?_⟩
  intro j
  by_cases same : j = i
  · subst j
    refine ⟨row, rows.get_set_same h matrix i row stored.1, valid, ?_⟩
    simpa [SequenceType.set, Heap.writeElement] using contents
  · obtain ⟨old, read, allocated, oldValues⟩ := stored.2 j
    refine ⟨old, ?_, allocated, ?_⟩
    · simpa only [rows.get_set_other_index h matrix j i row same] using read
    · simpa [same, SequenceType.set, Heap.writeElement] using oldValues

@[simp] theorem rows_get_tick (h : Heap) (matrix : CollectionRef) (i : Int)
    (clock : String) (amount : Nat) :
    rows.get (h.tick clock amount) matrix i = rows.get h matrix i := rfl

@[simp] theorem rows_valid_tick (h : Heap) (matrix : CollectionRef)
    (clock : String) (amount : Nat) :
    rows.valid (h.tick clock amount) matrix ↔ rows.valid h matrix := Iff.rfl

@[simp] theorem rows_get_allocate (h : Heap) (matrix : CollectionRef) (i : Int) (values : Seq) :
    rows.get (h.allocate values) matrix i = rows.get h matrix i := rfl

@[simp] theorem rows_valid_allocate (h : Heap) (matrix : CollectionRef) (values : Seq) :
    rows.valid (h.allocate values) matrix ↔ rows.valid h matrix := Iff.rfl

@[simp] theorem rows_get_write (h : Heap) (matrix : CollectionRef) (i : Int)
    (row : SeqRef) (j value : Int) :
    rows.get (h.write row j value) matrix i = rows.get h matrix i := rfl

@[simp] theorem rows_valid_write (h : Heap) (matrix : CollectionRef)
    (row : SeqRef) (j value : Int) :
    rows.valid (h.write row j value) matrix ↔ rows.valid h matrix := Iff.rfl

/-- Every finite output row is freshly allocated, valid, and has its own identity. -/
def FreshRows (before after : Heap) (matrix : CollectionRef) (n : Nat) : Prop :=
  (∀ i : Nat, i < n → ∃ row, rows.get after matrix i = some row ∧
    before.nextRef ≤ row ∧ row < after.nextRef) ∧
  (∀ i j : Nat, i < n → j < n → rows.get after matrix i = rows.get after matrix j → i = j)

theorem FreshRows.before_mono {before middle after : Heap} {matrix : CollectionRef} {n : Nat}
    (fresh : FreshRows middle after matrix n) (bound : before.nextRef ≤ middle.nextRef) :
    FreshRows before after matrix n := by
  refine ⟨?_, fresh.2⟩
  intro i valid
  obtain ⟨row, read, lower, upper⟩ := fresh.1 i valid
  exact ⟨row, read, Nat.le_trans bound lower, upper⟩

end Algo2LeanCore.MatrixHeap
