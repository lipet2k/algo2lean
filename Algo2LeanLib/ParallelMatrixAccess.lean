import Algo2LeanLib.ParallelMatrix
import Algo2LeanLib.ParallelSeq

/-! Frames and access bounds for preallocated arrays of matrix rows. -/
namespace Algo2Lean.ParallelMatrix
open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds

/-- One output row can change only in its assigned column interval. -/
def columnsAccess (a b out : Nat) (brows : Int → SeqRef) (n : Nat) (lo : Int) (count : Nat) : Access where
  reads := (dotAccess a b brows 0 n).reads
  writes x := ∃ j : Int, x = .seq out j ∧ lo ≤ j ∧ j < lo + count
  allocates := false

theorem columnsAccess_dot (a b out : Nat) (brows : Int → SeqRef) (n : Nat) (lo : Int) (count : Nat) :
    Access.Within (dotAccess a b brows 0 n) (columnsAccess a b out brows n lo count) := by
  refine ⟨fun _ h => h, ?_, ?_⟩ <;> simp [dotAccess, rowAccess, matrixReadAccess, Access.union, columnsAccess]

theorem columnsAccess_write (a b out : Nat) (brows : Int → SeqRef) (n : Nat) (lo j : Int) (count : Nat)
    (lower : lo ≤ j) (upper : j < lo + count) :
    Access.Within (Access.writeSeq out j) (columnsAccess a b out brows n lo count) := by
  refine ⟨?_, ?_, fun h => h⟩
  · simp [Access.writeSeq, Access.write]
  · intro x hx
    exact ⟨j, hx, lower, upper⟩

theorem columnsAccess_mono (a b out : Nat) (brows : Int → SeqRef) (n : Nat)
    (lo outer : Int) (count size : Nat) (lower : outer ≤ lo) (upper : lo+count ≤ outer+size) :
    Access.Within (columnsAccess a b out brows n lo count) (columnsAccess a b out brows n outer size) := by
  refine ⟨fun _ h => h, ?_, fun h => h⟩
  rintro x ⟨j, same, low, high⟩
  exact ⟨j, same, by omega, by omega⟩

theorem columnsAccess_compatible (a b out : Nat) (brows : Int → SeqRef) (n : Nat)
    (left right : Int) (m count : Nat) (different : a ≠ out)
    (bDifferent : ∀ i : Int, 0 ≤ i → i < n → out ≠ brows i)
    (separate : left+m ≤ right) :
    Access.Compatible (columnsAccess a b out brows n left m) (columnsAccess a b out brows n right count) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rintro x ⟨j, rfl, low, high⟩
    constructor
    · intro rd
      rcases rd with rd | rd
      · rcases rd with ⟨k, equal⟩
        cases equal
        exact different rfl
      · rcases rd with ⟨i, il, ih, rd⟩
        rcases rd with equal | ⟨k, equal⟩
        · cases equal
        · cases equal
          exact bDifferent i il (by omega) rfl
    · rintro ⟨k, equal, kl, kh⟩
      cases equal
      omega
  · rintro x ⟨j, rfl, low, high⟩
    constructor
    · intro rd
      rcases rd with rd | rd
      · rcases rd with ⟨k, equal⟩
        cases equal
        exact different rfl
      · rcases rd with ⟨i, il, ih, rd⟩
        rcases rd with equal | ⟨k, equal⟩
        · cases equal
        · cases equal
          exact bDifferent i il (by omega) rfl
    · rintro ⟨k, equal, kl, kh⟩
      cases equal
      omega

/-- Every nested sequence's outer rows and validity survive a sequence-only frame. -/
theorem MatrixView.seqFrame {h f : Heap} {outer : CollectionRef} {lo : Int} {n : Nat}
    {rows : Int → SeqRef} (view : MatrixView h outer lo n rows)
    {out : SeqRef} {first : Int} {count : Nat} (frame : SeqFrame h f out first count) :
    MatrixView f outer lo n rows := by
  exact view.transport frame.nextRef frame.nextCollection frame.collections

/-- A sequence-only frame preserves the row/column finite product when its
writable row is disjoint from both inputs. -/
theorem dot_seqFrame {h f : Heap} {out : SeqRef} {lo : Int} {count : Nat}
    (frame : SeqFrame h f out lo count) (a : SeqRef) (brows : Int → SeqRef)
    (column : Int) (n : Nat) (different : a ≠ out)
    (bDifferent : ∀ i : Int, 0 ≤ i → i < n → out ≠ brows i) :
    dot (f.read a) (matrixValues f brows) column 0 n = dot (h.read a) (matrixValues h brows) column 0 n := by
  apply intervalSum_congr
  intro i hi
  simp only [Int.zero_add, matrixValues]
  rw [frame.read_other different, frame.read_other (bDifferent i (by omega) (by exact_mod_cast hi)).symm]

/-- Only the assigned rectangle of existing output rows may change. -/
structure RowsFrame (before after : Heap) (rows : Int → SeqRef) (lo : Int) (count n : Nat) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  clocks : after.clocks = before.clocks
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections
  outside : ∀ ref j, (∀ i, lo ≤ i → i < lo+count → ref ≠ rows i) ∨ j < 0 ∨ (n : Int) ≤ j → after.read ref j = before.read ref j

namespace RowsFrame

theorem refl (h : Heap) (rows : Int → SeqRef) (lo : Int) (count n : Nat) : RowsFrame h h rows lo count n :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩

theorem trans {h m f : Heap} {rows : Int → SeqRef} {lo : Int} {count n : Nat}
    (a : RowsFrame h m rows lo count n) (b : RowsFrame m f rows lo count n) : RowsFrame h f rows lo count n :=
  ⟨b.nextRef.trans a.nextRef,b.nextObject.trans a.nextObject,b.objects.trans a.objects,
   b.clocks.trans a.clocks,b.nextCollection.trans a.nextCollection,b.collections.trans a.collections,
   fun r j outside => (b.outside r j outside).trans (a.outside r j outside)⟩

theorem weaken {h f : Heap} {rows : Int → SeqRef} {lo outer : Int} {count size n : Nat}
    (frame : RowsFrame h f rows lo count n) (lower : outer ≤ lo) (upper : lo+count ≤ outer+size) :
    RowsFrame h f rows outer size n := by
  refine ⟨frame.nextRef,frame.nextObject,frame.objects,frame.clocks,frame.nextCollection,frame.collections,?_⟩
  intro r j outside
  apply frame.outside r j
  rcases outside with outside | low | high
  · exact Or.inl (fun i il ih => outside i (by omega) (by omega))
  · exact Or.inr (Or.inl low)
  · exact Or.inr (Or.inr high)

theorem of_seq {h f : Heap} (rows : Int → SeqRef) (lo : Int) (n : Nat)
    (frame : SeqFrame h f (rows lo) 0 n) : RowsFrame h f rows lo 1 n := by
  refine ⟨frame.nextRef,frame.nextObject,frame.objects,frame.clocks,frame.nextCollection,frame.collections,?_⟩
  intro r j outside
  apply frame.outside r j
  rcases outside with outside | low | high
  · exact Or.inl (outside lo (by omega) (by omega))
  · exact Or.inr (Or.inl low)
  · exact Or.inr (Or.inr (by simpa using high))

theorem read_other {h f : Heap} {rows : Int → SeqRef} {lo : Int} {count n : Nat}
    (frame : RowsFrame h f rows lo count n) (ref : SeqRef)
    (different : ∀ i, lo ≤ i → i < lo+count → ref ≠ rows i) : f.read ref = h.read ref := by
  funext j
  exact frame.outside ref j (Or.inl different)

end RowsFrame

theorem MatrixView.rowsFrame {h f : Heap} {outer : CollectionRef} {lo : Int} {n : Nat}
    {rows : Int → SeqRef} (view : MatrixView h outer lo n rows)
    {outrows : Int → SeqRef} {first : Int} {count size : Nat} (frame : RowsFrame h f outrows first count size) :
    MatrixView f outer lo n rows := by
  exact view.transport frame.nextRef frame.nextCollection frame.collections

/-- Different output indices name different physical integer sequences. -/
def DistinctRows (rows : Int → SeqRef) (n : Nat) : Prop :=
  ∀ i j : Int, 0 ≤ i → i < n → 0 ≤ j → j < n → rows i = rows j → i = j

/-- Every writable row is separate from both matrices' read-only rows. -/
def SeparateRows (arows brows outrows : Int → SeqRef) (n : Nat) : Prop :=
  ∀ i j : Int, 0 ≤ i → i < n → 0 ≤ j → j < n →
    outrows i ≠ arows j ∧ outrows i ≠ brows j

/-- Read the two input matrices and output row identities; write only the
assigned rows and valid columns. Actual row references determine safety. -/
def rowsAccess (a b out : CollectionRef) (arows brows outrows : Int → SeqRef)
    (n : Nat) (lo : Int) (count : Nat) : Access where
  reads x := (matrixReadAccess a arows 0 n).reads x ∨
    (matrixReadAccess b brows 0 n).reads x ∨
    ∃ i : Int, lo ≤ i ∧ i < lo+count ∧ x = .collection out i
  writes x := ∃ i j : Int, lo ≤ i ∧ i < lo+count ∧ 0 ≤ j ∧ j < n ∧ x = .seq (outrows i) j
  allocates := false

theorem rowsAccess_mono (a b out : CollectionRef) (arows brows outrows : Int → SeqRef)
    (n : Nat) (lo outer : Int) (count size : Nat) (lower : outer ≤ lo) (upper : lo+count ≤ outer+size) :
    Access.Within (rowsAccess a b out arows brows outrows n lo count)
      (rowsAccess a b out arows brows outrows n outer size) := by
  refine ⟨?_, ?_, fun h => h⟩
  · intro x rd
    rcases rd with rd | rd | ⟨i,il,ih,rd⟩
    · exact Or.inl rd
    · exact Or.inr (Or.inl rd)
    · exact Or.inr (Or.inr ⟨i,by omega,by omega,rd⟩)
  · rintro x ⟨i,j,il,ih,jl,jh,wr⟩
    exact ⟨i,j,by omega,by omega,jl,jh,wr⟩

theorem rowsAccess_columns (a b out : CollectionRef) (arows brows outrows : Int → SeqRef)
    (n : Nat) (lo : Int) (count : Nat) (i : Int)
    (il : lo ≤ i) (ih : i < lo+count) (validLow : 0 ≤ i) (validHigh : i < n) :
    Access.Within (columnsAccess (arows i) b (outrows i) brows n 0 n)
      (rowsAccess a b out arows brows outrows n lo count) := by
  refine ⟨?_,?_,fun h => h⟩
  · intro x rd
    rcases rd with ⟨j,rd⟩ | rd
    · exact Or.inl ⟨i,validLow,by omega,Or.inr ⟨j,rd⟩⟩
    · exact Or.inr (Or.inl rd)
  · rintro x ⟨j,wr,jl,jh⟩
    exact ⟨i,j,il,ih,jl,by omega,wr⟩

theorem rowsAccess_outerA (a b out : CollectionRef) (arows brows outrows : Int → SeqRef)
    (n : Nat) (lo : Int) (count : Nat) (i : Int) (il : 0 ≤ i) (ih : i < n) :
    Access.Within (Access.read (.collection a i)) (rowsAccess a b out arows brows outrows n lo count) := by
  refine ⟨?_,?_,fun h => h⟩
  · intro x rd
    exact Or.inl ⟨i,il,by omega,Or.inl rd⟩
  · simp [Access.read]

theorem rowsAccess_outerOut (a b out : CollectionRef) (arows brows outrows : Int → SeqRef)
    (n : Nat) (lo : Int) (count : Nat) (i : Int) (il : lo ≤ i) (ih : i < lo+count) :
    Access.Within (Access.read (.collection out i)) (rowsAccess a b out arows brows outrows n lo count) := by
  refine ⟨?_,?_,fun h => h⟩
  · intro x rd
    exact Or.inr (Or.inr ⟨i,il,ih,rd⟩)
  · simp [Access.read]

theorem rowsAccess_compatible (a b out : CollectionRef) (arows brows outrows : Int → SeqRef)
    (n : Nat) (left right : Int) (m count : Nat)
    (distinct : DistinctRows outrows n) (separate : SeparateRows arows brows outrows n)
    (ll : 0 ≤ left) (lh : left+m ≤ n) (rl : 0 ≤ right) (rh : right+count ≤ n)
    (disjoint : left+m ≤ right) :
    Access.Compatible (rowsAccess a b out arows brows outrows n left m)
      (rowsAccess a b out arows brows outrows n right count) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · rintro x ⟨i,j,il,ih,jl,jh,rfl⟩
    constructor
    · intro rd
      rcases rd with ⟨k,kl,kh,rd⟩ | ⟨k,kl,kh,rd⟩ | ⟨k,kl,kh,rd⟩
      · rcases rd with rd | ⟨q,rd⟩
        · cases rd
        · exact (separate i k (by omega) (by omega) kl (by omega)).1 (Location.seq.inj rd).1
      · rcases rd with rd | ⟨q,rd⟩
        · cases rd
        · exact (separate i k (by omega) (by omega) kl (by omega)).2 (Location.seq.inj rd).1
      · cases rd
    · rintro ⟨k,q,kl,kh,ql,qh,equal⟩
      have rowSame := (Location.seq.inj equal).1
      have same := distinct i k (by omega) (by omega) (by omega) (by omega) rowSame
      omega
  · rintro x ⟨i,j,il,ih,jl,jh,rfl⟩
    constructor
    · intro rd
      rcases rd with ⟨k,kl,kh,rd⟩ | ⟨k,kl,kh,rd⟩ | ⟨k,kl,kh,rd⟩
      · rcases rd with rd | ⟨q,rd⟩
        · cases rd
        · exact (separate i k (by omega) (by omega) kl (by omega)).1 (Location.seq.inj rd).1
      · rcases rd with rd | ⟨q,rd⟩
        · cases rd
        · exact (separate i k (by omega) (by omega) kl (by omega)).2 (Location.seq.inj rd).1
      · cases rd
    · rintro ⟨k,q,kl,kh,ql,qh,equal⟩
      have rowSame := (Location.seq.inj equal).1
      have same := distinct i k (by omega) (by omega) (by omega) (by omega) rowSame
      omega

theorem dot_rowsFrame {h f : Heap} {outrows : Int → SeqRef} {lo : Int} {count n : Nat}
    (frame : RowsFrame h f outrows lo count n) (arows brows : Int → SeqRef)
    (i column : Int) (il : 0 ≤ i) (ih : i < n)
    (lower : 0 ≤ lo) (upper : lo+count ≤ n)
    (separate : SeparateRows arows brows outrows n) :
    dot (f.read (arows i)) (matrixValues f brows) column 0 n =
      dot (h.read (arows i)) (matrixValues h brows) column 0 n := by
  apply dot_congr
  · intro k kh
    rw [frame.read_other (arows i) (fun r rl rh => (separate r i (by omega) (by omega) il ih).1.symm)]
  · intro k kh
    simp only [matrixValues,Int.zero_add]
    rw [frame.read_other (brows k) (fun r rl rh => (separate r k (by omega) (by omega) (by omega) (by exact_mod_cast kh)).2.symm)]


private theorem cubic_bound (x m : Nat) (size : x ≤ 2*m) (positive : 1 ≤ m) :
    ((64*x+32)*x+32)*x+10 ≤4096*m^3 := by
  have square : 1 ≤ m*m := Nat.mul_le_mul positive positive
  have cube : 1 ≤ m*m*m := Nat.mul_le_mul square positive
  have first : 64*x+32 ≤160*m := by omega
  have second := Nat.mul_le_mul first size
  have third : (64*x+32)*x+32 ≤352*(m*m) := by
    have normalize : 160*m*(2*m)=320*(m*m) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [normalize] at second
    omega
  have fourth := Nat.mul_le_mul third size
  have normalize : 352*(m*m)*(2*m)=704*(m*m*m) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [normalize] at fourth
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  omega

theorem matrix_work_cubic (n : Nat) :
    ((64*nodes n+32)*nodes n+32)*nodes n+10 ≤4096*(n+1)^3 := by
  apply cubic_bound
  · have := nodes_le_linear n; omega
  · omega

theorem matrix_span_log (n : Nat) :
    32*height n+96*height n+10≤256*(Nat.log2 n+2) := by
  have := height_le_logarithmic n
  omega

end Algo2Lean.ParallelMatrix
