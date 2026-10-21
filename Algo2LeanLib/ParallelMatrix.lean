import Algo2LeanLib.ParallelBounds
import Algo2LeanLib.ParallelSeq

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Matrix views and read permissions for integer arrays of row references.
Finite row ranges describe well-formed inputs without requiring unused entries
of the infinite outer sequence to contain allocated rows. Input rows may alias.
-/
namespace Algo2Lean.ParallelMatrix
open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds

/-- The runtime descriptor for an array whose elements are integer sequences. -/
def rowType : SequenceType SeqRef where
  name := "Seq[Int]"
  encode := ObjectValue.seqValue
  decode := ObjectValue.asSeq
  decode_encode := by intro value; rfl

/-- Every used row has its stated identity and is allocated. No separation
between input rows is imposed; the outer sequence itself has the correct tag. -/
structure MatrixView (h : Heap) (outer : CollectionRef) (lo : Int) (n : Nat)
    (rows : Int → SeqRef) : Prop where
  valid : rowType.valid h outer
  get : ∀ i, lo ≤ i → i < lo + n → rowType.get h outer i = some (rows i)
  allocated : ∀ i, lo ≤ i → i < lo + n → rows i < h.nextRef

theorem MatrixView.mono {h : Heap} {outer : CollectionRef} {lo : Int} {n : Nat}
    {rows : Int → SeqRef} (view : MatrixView h outer lo n rows)
    (first : Int) (count : Nat) (lower : lo ≤ first) (upper : first + count ≤ lo + n) :
    MatrixView h outer first count rows := by
  refine ⟨view.valid, ?_, ?_⟩
  · intro i low high; exact view.get i (by omega) (by omega)
  · intro i low high; exact view.allocated i (by omega) (by omega)

/-- Row identities remain a valid representation when allocation metadata and
outer collection storage are preserved. Integer row entries may change. -/
theorem MatrixView.transport {before after : Heap} {outer : CollectionRef} {lo : Int}
    {n : Nat} {rows : Int → SeqRef} (view : MatrixView before outer lo n rows)
    (nextRef : after.nextRef = before.nextRef)
    (nextCollection : after.nextCollection = before.nextCollection)
    (collections : after.collections = before.collections) :
    MatrixView after outer lo n rows := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [SequenceType.valid, Heap.validSequence, Heap.sequenceType, nextCollection,
      collections] using view.valid
  · intro i low high
    have same : rowType.get after outer i = rowType.get before outer i := by
      unfold SequenceType.get SequenceType.valid Heap.validSequence Heap.sequenceType Heap.readElement
      simp only [nextCollection, collections]
    rw [same]
    exact view.get i low high
  · intro i low high
    rw [nextRef]
    exact view.allocated i low high

/-- Allocating unrelated storage preserves an input view. Only the selected
outer collection must retain its contents, and allocation counters may grow. -/
theorem MatrixView.transport_alloc {before after : Heap} {outer : CollectionRef} {lo : Int}
    {n : Nat} {rows : Int → SeqRef} (view : MatrixView before outer lo n rows)
    (nextRef : before.nextRef ≤ after.nextRef)
    (nextCollection : before.nextCollection ≤ after.nextCollection)
    (collection : after.collections outer = before.collections outer) :
    MatrixView after outer lo n rows := by
  have validAfter : rowType.valid after outer := by
    refine ⟨Nat.lt_of_lt_of_le view.valid.1 nextCollection, ?_⟩
    simpa [Heap.sequenceType, collection] using view.valid.2
  refine ⟨validAfter, ?_, ?_⟩
  · intro i low high
    have same : rowType.get after outer i = rowType.get before outer i := by
      simp only [SequenceType.get, if_pos validAfter, if_pos view.valid]
      simp only [Heap.readElement, collection]
    rw [same]
    exact view.get i low high
  · intro i low high
    exact Nat.lt_of_lt_of_le (view.allocated i low high) nextRef

/-- Ordinary two-index mathematical values represented by a row map. -/
def matrixValues (h : Heap) (rows : Int → SeqRef) : Int → Int → Int :=
  fun i j => h.read (rows i) j

/-- The row-by-column sum over the requested contraction interval. -/
def dot (a : Int → Int) (b : Int → Int → Int) (column first : Int) (count : Nat) : Int :=
  intervalSum (fun k => a k * b k column) first count

@[simp] theorem dot_zero (a : Int → Int) (b : Int → Int → Int) (column first : Int) :
    dot a b column first 0 = 0 := rfl

@[simp] theorem dot_one (a : Int → Int) (b : Int → Int → Int) (column first : Int) :
    dot a b column first 1 = a first * b first column := by simp [dot]

theorem dot_split (a : Int → Int) (b : Int → Int → Int) (column first : Int)
    (count left : Nat) (bound : left ≤ count) :
    dot a b column first count = dot a b column first left +
      dot a b column (first + left) (count-left) :=
  intervalSum_split _ _ _ _ bound

theorem dot_congr (a a' : Int → Int) (b b' : Int → Int → Int) (column first : Int)
    (count : Nat) (sameA : ∀ i : Nat, i < count → a (first+i) = a' (first+i))
    (sameB : ∀ i : Nat, i < count → b (first+i) column = b' (first+i) column) :
    dot a b column first count = dot a' b' column first count := by
  apply intervalSum_congr
  intro i valid
  rw [sameA i valid, sameB i valid]

/-- Read any entry of one integer sequence. -/
def rowAccess (row : SeqRef) : Access where
  reads x := ∃ j, x = .seq row j
  writes _ := False
  allocates := false

/-- Read the row references and the integer entries of the specified row range. -/
def matrixReadAccess (outer : CollectionRef) (rows : Int → SeqRef) (lo : Int) (n : Nat) : Access where
  reads x := ∃ i, lo ≤ i ∧ i < lo+n ∧
    (x = .collection outer i ∨ ∃ j, x = .seq (rows i) j)
  writes _ := False
  allocates := false

/-- Permissions consumed by one row-column dot product. -/
def dotAccess (a : SeqRef) (b : CollectionRef) (rows : Int → SeqRef)
    (first : Int) (count : Nat) : Access :=
  Access.union (rowAccess a) (matrixReadAccess b rows first count)

theorem rowAccess_read (row : SeqRef) (i : Int) :
    Access.Within (Access.readSeq row i) (rowAccess row) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x same; exact ⟨i, same⟩
  · simp [Access.readSeq, Access.read]
  · simp [Access.readSeq, Access.read]

theorem matrixReadAccess_outer (outer : CollectionRef) (rows : Int → SeqRef)
    (lo : Int) (n : Nat) (i : Int) (lower : lo ≤ i) (upper : i < lo+n) :
    Access.Within (Access.read (.collection outer i)) (matrixReadAccess outer rows lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x same; exact ⟨i, lower, upper, Or.inl same⟩
  · simp [Access.read]
  · simp [Access.read]

theorem matrixReadAccess_inner (outer : CollectionRef) (rows : Int → SeqRef)
    (lo : Int) (n : Nat) (i j : Int) (lower : lo ≤ i) (upper : i < lo+n) :
    Access.Within (Access.readSeq (rows i) j) (matrixReadAccess outer rows lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x same; exact ⟨i, lower, upper, Or.inr ⟨j, same⟩⟩
  · simp [Access.readSeq, Access.read]
  · simp [Access.readSeq, Access.read]

theorem matrixReadAccess_mono (outer : CollectionRef) (rows : Int → SeqRef)
    (lo first : Int) (n count : Nat) (lower : lo ≤ first) (upper : first+count ≤ lo+n) :
    Access.Within (matrixReadAccess outer rows first count) (matrixReadAccess outer rows lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨i, low, high, access⟩; exact ⟨i, by omega, by omega, access⟩
  · simp [matrixReadAccess]
  · simp [matrixReadAccess]

theorem dotAccess_mono (a : SeqRef) (b : CollectionRef) (rows : Int → SeqRef)
    (lo first : Int) (n count : Nat) (lower : lo ≤ first) (upper : first+count ≤ lo+n) :
    Access.Within (dotAccess a b rows first count) (dotAccess a b rows lo n) := by
  exact Access.Within.union_mono (Access.Within.refl _)
    (matrixReadAccess_mono b rows lo first n count lower upper)

theorem dotAccess_compatible (a a' : SeqRef) (b b' : CollectionRef)
    (rows rows' : Int → SeqRef) (first first' : Int) (count count' : Nat) :
    Access.Compatible (dotAccess a b rows first count) (dotAccess a' b' rows' first' count') := by
  apply Access.reads_compatible <;> simp [dotAccess, Access.union, rowAccess, matrixReadAccess]

end Algo2Lean.ParallelMatrix
