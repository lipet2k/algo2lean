import Algo2LeanLib.ParallelMatrixAllocation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Fresh arrays of distinct zero rows, constructed before parallel evaluation.
The default row also exists and remains zero, so every outer index is defined.
-/
namespace Algo2Lean.ParallelMatrix
open Algo2LeanGenerated

/-- Allocate the shared default zero row and a fresh outer sequence. -/
def initialOuter (h : Heap) : Heap :=
  (rowType.const (h.allocate (fun _ => 0)) h.nextRef).1

/-- Allocate a distinct zero row for each of the requested output row indices. -/
def freshHeap (h : Heap) (n : Nat) : Heap :=
  Allocation.rows (initialOuter h) h.nextCollection 0 n

/-- The reference assigned to nonnegative output row `i`. -/
def freshRows (h : Heap) (i : Int) : SeqRef := h.nextRef+1+i.toNat

@[simp] theorem initial_nextRef (h : Heap) : (initialOuter h).nextRef = h.nextRef+1 := rfl
@[simp] theorem initial_nextCollection (h : Heap) :
    (initialOuter h).nextCollection = h.nextCollection+1 := rfl
@[simp] theorem initial_nextObject (h : Heap) : (initialOuter h).nextObject = h.nextObject := rfl
@[simp] theorem initial_objects (h : Heap) : (initialOuter h).objects = h.objects := rfl
@[simp] theorem initial_clocks (h : Heap) : (initialOuter h).clocks = h.clocks := rfl

@[simp] theorem initial_valid (h : Heap) : rowType.valid (initialOuter h) h.nextCollection :=
  rowType.valid_const (h.allocate (fun _ => 0)) h.nextRef

@[simp] theorem initial_get (h : Heap) (i : Int) :
    rowType.get (initialOuter h) h.nextCollection i = some h.nextRef :=
  rowType.get_const (h.allocate (fun _ => 0)) h.nextRef i

@[simp] theorem fresh_nextRef (h : Heap) (n : Nat) :
    (freshHeap h n).nextRef = h.nextRef+1+n := by simp [freshHeap]
@[simp] theorem fresh_nextCollection (h : Heap) (n : Nat) :
    (freshHeap h n).nextCollection = h.nextCollection+1 := by simp [freshHeap]
@[simp] theorem fresh_nextObject (h : Heap) (n : Nat) :
    (freshHeap h n).nextObject = h.nextObject := by simp [freshHeap]
@[simp] theorem fresh_objects (h : Heap) (n : Nat) :
    (freshHeap h n).objects = h.objects := by simp [freshHeap]
@[simp] theorem fresh_clocks (h : Heap) (n : Nat) :
    (freshHeap h n).clocks = h.clocks := by simp [freshHeap]

/-- Earlier integer sequences retain every entry. -/
theorem fresh_read_old (h : Heap) (n : Nat) (ref : SeqRef) (old : ref < h.nextRef) :
    (freshHeap h n).read ref = h.read ref := by
  have still : ref < (initialOuter h).nextRef := Nat.lt_trans old (Nat.lt_succ_self _)
  rw [freshHeap, Allocation.read_old _ _ _ _ ref still]
  change (h.allocate (fun _ => 0)).read ref = h.read ref
  funext i
  simp [Heap.read, Heap.allocate, Nat.ne_of_lt old]

/-- Earlier collections retain their complete runtime representation. -/
theorem fresh_collection_old (h : Heap) (n : Nat) (ref : CollectionRef)
    (old : ref < h.nextCollection) :
    (freshHeap h n).collections ref = h.collections ref := by
  rw [freshHeap, Allocation.other_collection _ _ _ _ _ (Nat.ne_of_lt old)]
  simp [initialOuter, SequenceType.const, SequenceType.create, Heap.createSequence,
    Heap.allocateSequence, Heap.allocate, Nat.ne_of_lt old]

/-- Every output row slot in the finite matrix names its allocated fresh row. -/
theorem fresh_view (h : Heap) (n : Nat) :
    MatrixView (freshHeap h n) h.nextCollection 0 n (freshRows h) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [freshHeap]
  · intro i low high
    have inside : i.toNat < n := by omega
    have found := Allocation.get_inside (initialOuter h) h.nextCollection 0 n i.toNat
      (initial_valid h) inside
    simpa [freshHeap, freshRows, Int.toNat_of_nonneg low] using found
  · intro i low high
    have inside : i.toNat < n := by omega
    simpa only [freshRows, fresh_nextRef] using Nat.add_lt_add_left inside (h.nextRef+1)

/-- Distinct used row indices denote distinct heap references. -/
theorem fresh_rows_injective (h : Heap) (i j : Int) (lowI : 0 ≤ i) (lowJ : 0 ≤ j)
    (same : freshRows h i = freshRows h j) : i = j := by
  have equalNat : i.toNat = j.toNat := Nat.add_left_cancel same
  have equalInt := congrArg Int.ofNat equalNat
  change (↑i.toNat : Int) = ↑j.toNat at equalInt
  rw [Int.toNat_of_nonneg lowI, Int.toNat_of_nonneg lowJ] at equalInt
  exact equalInt

/-- No new output row aliases an earlier sequence. -/
theorem fresh_rows_disjoint (h : Heap) (ref : SeqRef) (old : ref < h.nextRef) (i : Int) :
    freshRows h i ≠ ref := by
  apply Nat.ne_of_gt
  apply Nat.lt_of_lt_of_le old
  simpa only [freshRows, Nat.add_assoc] using Nat.le_add_right h.nextRef (1+i.toNat)

/-- All integer columns, including those outside the finite matrix, start at zero. -/
theorem fresh_read_zero (h : Heap) (n : Nat) (i : Int) (low : 0 ≤ i) (high : i < n) :
    (freshHeap h n).read (freshRows h i) = fun _ => 0 := by
  have inside : i.toNat < n := by omega
  exact Allocation.read_new (initialOuter h) h.nextCollection 0 n i.toNat inside

/-- Outer indices outside the finite matrix keep the allocated default row. -/
theorem fresh_get_outside (h : Heap) (n : Nat) (i : Int) (outside : i < 0 ∨ (n : Int) ≤ i) :
    rowType.get (freshHeap h n) h.nextCollection i = some h.nextRef := by
  rw [freshHeap, Allocation.get_outside _ _ _ _ _ _ (Or.inr (by simpa using outside))]
  exact initial_get h i

/-- The default row remains zero after the finite rows are allocated. -/
theorem fresh_default_zero (h : Heap) (n : Nat) :
    (freshHeap h n).read h.nextRef = fun _ => 0 := by
  rw [freshHeap, Allocation.read_old _ _ _ _ h.nextRef (by simp)]
  funext i
  change (h.allocate (fun _ => 0)).read h.nextRef i = 0
  simp [Heap.read, Heap.allocate]

/-- An input's finite row representation survives the output allocations. -/
theorem fresh_input_view {h : Heap} {input : CollectionRef} {lo : Int} {count : Nat}
    {rows : Int → SeqRef} (view : MatrixView h input lo count rows) (n : Nat) :
    MatrixView (freshHeap h n) input lo count rows := by
  apply view.transport_alloc
  · simpa only [fresh_nextRef, Nat.add_assoc] using Nat.le_add_right h.nextRef (1+n)
  · simp
  · exact fresh_collection_old h n input view.valid.1

/-- Every input matrix value in a represented row is unchanged. -/
theorem fresh_input_values {h : Heap} {input : CollectionRef} {lo : Int} {count : Nat}
    {rows : Int → SeqRef} (view : MatrixView h input lo count rows) (n : Nat)
    (i : Int) (low : lo ≤ i) (high : i < lo+count) :
    matrixValues (freshHeap h n) rows i = matrixValues h rows i :=
  fresh_read_old h n (rows i) (view.allocated i low high)

end Algo2Lean.ParallelMatrix
