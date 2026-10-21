import Algo2LeanLib.ParallelMatrix

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Sequential creation of distinct rows before entering a parallel matrix call. -/
namespace Algo2Lean.ParallelMatrix.Allocation
open Algo2LeanGenerated

/-- Allocate a zero row and store its fresh reference in the outer array. -/
def step (h : Heap) (out : CollectionRef) (lo : Int) : Heap :=
  rowType.set (h.allocate (fun _ => 0)) out lo h.nextRef

/-- The exact heap produced by the source row allocator. -/
def rows (h : Heap) (out : CollectionRef) (lo : Int) : Nat → Heap
  | 0 => h
  | n+1 => rows (step h out lo) out (lo+1) n

@[simp] theorem step_nextRef (h : Heap) (out : CollectionRef) (lo : Int) :
    (step h out lo).nextRef = h.nextRef+1 := rfl

@[simp] theorem rows_nextRef (h : Heap) (out : CollectionRef) (lo : Int) (n : Nat) :
    (rows h out lo n).nextRef = h.nextRef+n := by
  induction n generalizing h lo with
  | zero => simp [rows]
  | succ n ih => simp only [rows, ih, step_nextRef]; omega

@[simp] theorem rows_nextCollection (h : Heap) (out : CollectionRef) (lo : Int) (n : Nat) :
    (rows h out lo n).nextCollection = h.nextCollection := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih => rw [rows, ih]; rfl

@[simp] theorem rows_nextObject (h : Heap) (out : CollectionRef) (lo : Int) (n : Nat) :
    (rows h out lo n).nextObject = h.nextObject := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih => rw [rows, ih]; rfl

@[simp] theorem rows_objects (h : Heap) (out : CollectionRef) (lo : Int) (n : Nat) :
    (rows h out lo n).objects = h.objects := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih => rw [rows, ih]; rfl

@[simp] theorem rows_clocks (h : Heap) (out : CollectionRef) (lo : Int) (n : Nat) :
    (rows h out lo n).clocks = h.clocks := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih => rw [rows, ih]; rfl

@[simp] theorem valid_allocate (h : Heap) (a : CollectionRef) (v : Seq) :
    rowType.valid (h.allocate v) a ↔ rowType.valid h a := Iff.rfl

@[simp] theorem get_allocate (h : Heap) (a : CollectionRef) (i : Int) (v : Seq) :
    rowType.get (h.allocate v) a i = rowType.get h a i := rfl

@[simp] theorem valid_step (h : Heap) (out a : CollectionRef) (lo : Int) :
    rowType.valid (step h out lo) a ↔ rowType.valid h a := by simp [step]

@[simp] theorem valid_rows (h : Heap) (out a : CollectionRef) (lo : Int) (n : Nat) :
    rowType.valid (rows h out lo n) a ↔ rowType.valid h a := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih => simp [rows, ih]

/-- Existing sequences are never written while allocating fresh rows. -/
theorem read_old (h : Heap) (out : CollectionRef) (lo : Int) (n : Nat)
    (r : SeqRef) (old : r < h.nextRef) :
    (rows h out lo n).read r = h.read r := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih =>
    rw [rows, ih (step h out lo) (lo+1) (Nat.lt_trans old (Nat.lt_succ_self _))]
    funext i
    simp [step, SequenceType.set, Heap.writeElement, Heap.read, Heap.allocate,
      Nat.ne_of_lt old]

/-- Every other collection is preserved exactly. -/
theorem other_collection (h : Heap) (out other : CollectionRef) (lo : Int) (n : Nat)
    (different : other ≠ out) :
    (rows h out lo n).collections other = h.collections other := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih =>
    rw [rows, ih]
    simp [step, SequenceType.set, Heap.writeElement, Heap.allocate, different]

/-- Row slots outside the requested interval retain their original references. -/
theorem get_outside (h : Heap) (out other : CollectionRef) (lo index : Int) (n : Nat)
    (outside : other ≠ out ∨ index < lo ∨ lo+n ≤ index) :
    rowType.get (rows h out lo n) other index = rowType.get h other index := by
  induction n generalizing h lo with
  | zero => rfl
  | succ n ih =>
    have after : other ≠ out ∨ index < lo+1 ∨ (lo+1)+(n : Int) ≤ index := by
      rcases outside with different | low | high
      · exact Or.inl different
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    rw [rows, ih (step h out lo) (lo+1) after]
    by_cases same : other = out
    · subst other
      have ne : index ≠ lo := by
        rcases outside with no | low | high
        · exact False.elim (no rfl)
        · exact Int.ne_of_lt low
        · omega
      simp [step, ne]
    · simp [step, same]

/-- Every initialized slot points to its own fresh row. -/
theorem get_inside (h : Heap) (out : CollectionRef) (lo : Int) (n i : Nat)
    (valid : rowType.valid h out) (inside : i < n) :
    rowType.get (rows h out lo n) out (lo+i) = some (h.nextRef+i) := by
  induction n generalizing h lo i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp only [rows]
      rw [show lo + (↑(0 : Nat) : Int) = lo by omega, Nat.add_zero]
      rw [get_outside _ _ _ _ _ _ (Or.inr (Or.inl (by omega)))]
      simp [step, valid]
    | succ i =>
      have index : lo + (↑(i+1) : Int) = (lo+1)+i := by omega
      rw [rows, index, ih _ _ i (by simpa using valid) (by omega)]
      simp only [step_nextRef]; congr 1 <;> omega

/-- Newly created rows are zero at all mathematical integer indices. -/
theorem read_new (h : Heap) (out : CollectionRef) (lo : Int) (n i : Nat)
    (inside : i < n) : (rows h out lo n).read (h.nextRef+i) = fun _ => 0 := by
  induction n generalizing h lo i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp only [Nat.add_zero, rows]
      rw [read_old _ _ _ _ _ (by simp)]
      funext index
      simp [step, SequenceType.set, Heap.writeElement, Heap.read, Heap.allocate]
    | succ i =>
      have ref : h.nextRef+(i+1) = (step h out lo).nextRef+i := by simp; omega
      rw [rows, ref]
      exact ih _ _ i (by omega)

end Algo2Lean.ParallelMatrix.Allocation
