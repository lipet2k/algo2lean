import Algo2LeanLib.CallCost
import MatrixMultiplyGeneratedPoints
import Algo2LeanLib.MatrixHeap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
CLRS 4.1 on genuine arrays of row arrays. The inputs may share rows, including
with each other. A fresh row is allocated for every output row. The proof
constructs terminating executions and proves preservation of all pre-existing
objects, the mathematical matrix product, and exactly n³ scalar multiply-adds.
-/
open Algo2LeanCore Algo2LeanGenerated
open Algo2LeanCore.MatrixHeap

namespace MatrixMultiplyAnalysis

/-- The finite row-by-column sum, at arbitrary integer coordinates. -/
def dotFrom (a b : Values) (row column first : Int) : Nat → Int
  | 0 => 0
  | count + 1 => a row first * b first column + dotFrom a b row column (first + 1) count

def entry (a b : Values) (n : Nat) (row column : Int) : Int :=
  dotFrom a b row column 0 n

/-- Both coordinates outside the finite square have value zero. -/
def product (a b : Values) (n : Nat) : Values :=
  fun row column => if 0 ≤ row ∧ row < n ∧ 0 ≤ column ∧ column < n
    then entry a b n row column else 0

/-- Consecutive writes of a mathematical row to one fresh output object. -/
def fill (h : Heap) (r : SeqRef) (values : Seq) (first : Int) : Nat → Heap
  | 0 => h
  | count + 1 => fill (h.write r first (values first)) r values (first + 1) count

@[simp] theorem fill_nextRef (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).nextRef = h.nextRef := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih]

@[simp] theorem fill_clocks (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).clocks = h.clocks := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih]

@[simp] theorem fill_collections (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).collections = h.collections := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih]

@[simp] theorem fill_nextCollection (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).nextCollection = h.nextCollection := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simpa [fill, Heap.write] using ih (h.write r first (values first)) (first + 1)

theorem fill_other (h : Heap) (r other : SeqRef) (values : Seq) (first : Int) (count : Nat)
    (different : other ≠ r) : (fill h r values first count).store other = h.store other := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih =>
    rw [fill, ih]
    funext i
    simp [Heap.write, different]

theorem fill_outside (h : Heap) (r : SeqRef) (values : Seq) (first i : Int) (count : Nat)
    (outside : i < first ∨ first + (count : Int) ≤ i) :
    (fill h r values first count).store r i = h.store r i := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih =>
    rw [fill, ih]
    · have ne : i ≠ first := by omega
      simp [Heap.write, ne]
    · omega

theorem fill_inside (h : Heap) (r : SeqRef) (values : Seq) (first i : Int) (count : Nat)
    (inside : first ≤ i ∧ i < first + (count : Int)) :
    (fill h r values first count).store r i = values i := by
  induction count generalizing h first with
  | zero => omega
  | succ count ih =>
    rw [fill]
    by_cases eq : i = first
    · subst i
      rw [fill_outside _ _ _ _ _ _ (Or.inl (by omega))]
      simp [Heap.write]
    · apply ih
      omega

@[simp] theorem write_tick (h : Heap) (r : SeqRef) (index value : Int) (amount : Nat) :
    (h.tick "multiply_add" amount).write r index value =
      (h.write r index value).tick "multiply_add" amount := rfl

@[simp] theorem fill_tick (h : Heap) (r : SeqRef) (values : Seq) (first : Int)
    (count amount : Nat) :
    fill (h.tick "multiply_add" amount) r values first count =
      (fill h r values first count).tick "multiply_add" amount := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => exact ih (h.write r first (values first)) (first + 1)

/-- Finish a dot-product loop; nested inputs can share any of their row arrays. -/
theorem dot_loop (count : Nat) (state : Configuration)
    (a b : CollectionRef) (av bv : Values) (n row column first total : Int)
    (location : matrix_dot.At.dot_loop state)
    (ra : matrix_dot.Local.a state = some a)
    (rb : matrix_dot.Local.b state = some b)
    (rn : matrix_dot.Local.n state = some n)
    (rr : matrix_dot.Local.row state = some row)
    (rc : matrix_dot.Local.column state = some column)
    (rk : matrix_dot.Local.k state = some first)
    (rt : matrix_dot.Local.total state = some total)
    (bound : n = first + (count : Int))
    (va : Stored state.heap a av) (vb : Stored state.heap b bv) :
    matrix_dot.CallFrom state (state.heap.tick "multiply_add" count)
      (total + dotFrom av bv row column first count) := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_multiply => cases location
    | fn_matrix_row => cases location
    | fn_matrix_dot pc s =>
      have atLoop : pc = 4 := by unfold matrix_dot.At.dot_loop at location; split at location <;> simp_all
      subst pc
      simp [matrix_dot.Local.a, matrix_dot.Local.b, matrix_dot.Local.n, matrix_dot.Local.row,
        matrix_dot.Local.column, matrix_dot.Local.k, matrix_dot.Local.total] at ra rb rn rr rc rk rt
      dsimp only [Config.heap] at va vb ⊢
      induction count generalizing h s first total with
      | zero =>
        intro stack
        apply Reaches.prepend (Step.matrix_dot_pc4 ..)
        apply Reaches.prepend (Step.matrix_dot_pc3_false _ _ _ (by simp; omega))
        apply Reaches.prepend (Step.matrix_dot_pc2 ..)
        simpa [dotFrom, rt] using Reaches.single (Step.matrix_dot_pc1 h _ stack)
      | succ count ih =>
        obtain ⟨ar, ag, arvalid, arvalues⟩ := va.2 row
        obtain ⟨br, bg, brvalid, brvalues⟩ := vb.2 first
        have next := ih (h := h.tick "multiply_add")
          (s := { s with v5 := first + 1, v6 := total + av row first * bv first column, t8 := decide (s.v5 < s.v2) }) (first := first + 1)
          (total := total + av row first * bv first column)
          (bound := by omega) (location := True.intro) (va := va) (vb := vb)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (rc := rc) (rk := rfl) (rt := rfl)
        intro stack
        apply Reaches.prepend (Step.matrix_dot_pc4 ..)
        apply Reaches.prepend (Step.matrix_dot_pc3_true _ _ _ (by simp; omega))
        apply Reaches.prepend (Step.matrix_dot_pc7 ..)
        apply Reaches.prepend (Step.matrix_dot_pc6 _ _ _ (by
          simp [ra, rb, rr, rk, show seq_Seq_Int = rows from rfl, ag, bg, arvalid, brvalid]))
        apply Reaches.prepend (Step.matrix_dot_pc5 ..)
        simpa [dotFrom, ra, rb, rn, rr, rc, rk, rt, Heap.read, Heap.tick_add,
          Nat.add_comm 1, Int.add_assoc, show seq_Seq_Int = rows from rfl, ag, bg,
          arvalues, brvalues] using next stack

/-- One dot product costs exactly n scalar multiply-adds. -/
theorem dot_summary (h : Heap) (a b : CollectionRef) (av bv : Values)
    (n : Nat) (row column : Int) (va : Stored h a av) (vb : Stored h b bv) :
    matrix_dot.Call h (a, b, n, row, column) (h.tick "multiply_add" n)
      (entry av bv n row column) := by
  refine ⟨⟨va.1, vb.1⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.matrix_dot_pc9 ..)
  apply Reaches.prepend (Step.matrix_dot_pc8 ..)
  have run := dot_loop n (.active h (.fn_matrix_dot 4
    { v0 := a, v1 := b, v2 := n, v3 := row, v4 := column }) stack)
    a b av bv n row column 0 0 True.intro rfl rfl rfl rfl rfl rfl rfl (by omega) va vb
  simpa [Config.heap, entry] using run stack

theorem fill_extends {before after : Heap} (extension : Extends before after)
    (r : SeqRef) (fresh : before.nextRef ≤ r) (values : Seq) (first : Int) (count : Nat) :
    Extends before (fill after r values first count) := by
  induction count generalizing after first with
  | zero => exact extension
  | succ count ih => exact ih (extension.write r fresh first (values first)) (first + 1)

/-- Complete one output row while preserving the original nested inputs. -/
theorem columns_loop (count : Nat) (state : Configuration) (original : Heap)
    (a b : CollectionRef) (av bv : Values) (result : SeqRef) (n : Nat) (row first : Int)
    (location : matrix_row.At.columns_loop state)
    (ra : matrix_row.Local.a state = some a)
    (rb : matrix_row.Local.b state = some b)
    (rn : matrix_row.Local.n state = some (n : Int))
    (rr : matrix_row.Local.row state = some row)
    (ro : matrix_row.Local.result state = some result)
    (ri : matrix_row.Local.column state = some first)
    (bound : first + (count : Int) = n)
    (va : Stored original a av) (vb : Stored original b bv)
    (extension : Extends original state.heap) (fresh : original.nextRef ≤ result)
    (valid : result < state.heap.nextRef) :
    matrix_row.CallFrom state
      ((fill state.heap result (entry av bv n row) first count).tick
        "multiply_add" (count * n)) result := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_dot => cases location
    | fn_matrix_multiply => cases location
    | fn_matrix_row pc s =>
      have atLoop : pc = 4 := by unfold matrix_row.At.columns_loop at location; split at location <;> simp_all
      subst pc
      simp [matrix_row.Local.a, matrix_row.Local.b, matrix_row.Local.n,
        matrix_row.Local.row, matrix_row.Local.result, matrix_row.Local.column] at ra rb rn rr ro ri
      dsimp only [Config.heap] at extension valid ⊢
      induction count generalizing h s first with
      | zero =>
        intro stack
        apply Reaches.prepend (Step.matrix_row_pc4 ..)
        apply Reaches.prepend (Step.matrix_row_pc3_false _ _ _ (by simp [rn, ri]; omega))
        apply Reaches.prepend (Step.matrix_row_pc2 ..)
        simpa [fill, ro] using Reaches.single (Step.matrix_row_pc1 h _ stack (by simpa [ro] using valid))
      | succ count ih =>
        let value := entry av bv n row first
        let updated := (h.tick "multiply_add" n).write result first value
        have extended : Extends original updated :=
          (extension.trans (extends_tick h "multiply_add" n)).write result fresh first value
        have next := ih (h := updated)
          (s := { s with v5 := first + 1, v6 := value, t8 := decide (s.v5 < s.v2), t9 := value, t10 := a, t11 := b, t12 := n, t13 := row, t14 := first })
          (first := first + 1) (bound := by omega) (location := True.intro)
          (extension := extended) (valid := valid)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (ro := ro) (ri := rfl)
        intro stack
        apply Reaches.prepend (Step.matrix_row_pc4 ..)
        apply Reaches.prepend (Step.matrix_row_pc3_true _ _ _ (by simp [ri, rn]; omega))
        apply Reaches.prepend (Step.matrix_row_pc13 ..)
        apply Reaches.prepend (Step.matrix_row_pc12 ..)
        apply Reaches.prepend (Step.matrix_row_pc11 ..)
        apply Reaches.prepend (Step.matrix_row_pc10 ..)
        apply Reaches.prepend (Step.matrix_row_pc9 ..)
        apply Reaches.prepend (Step.matrix_row_pc8 ..)
        simp only [rn]
        apply Reaches.trans ((dot_summary h s.v0 s.v1 av bv n s.v3 s.v5
          (by simpa [ra] using va.mono extension) (by simpa [rb] using vb.mono extension)).2 _)
        apply Reaches.prepend (Step.matrix_row_pc7 ..)
        apply Reaches.prepend (Step.matrix_row_pc6 _ _ _ (by simpa [ro] using valid))
        apply Reaches.prepend (Step.matrix_row_pc5 ..)
        simpa [value, updated, ra, rb, rn, rr, ro, ri,
          fill, fill_tick, Heap.tick_add, Nat.succ_mul, Nat.add_comm] using next stack

/-- The completed fresh row and its exact cost. -/
def rowHeap (h : Heap) (av bv : Values) (n : Nat) (row : Int) : Heap :=
  (fill (h.allocate (fun _ => 0)) h.nextRef (entry av bv n row) 0 n).tick
    "multiply_add" (n * n)

def rowValues (av bv : Values) (n : Nat) (row : Int) : Seq :=
  fun column => if 0 ≤ column ∧ column < n then entry av bv n row column else 0

theorem row_summary (h : Heap) (a b : CollectionRef) (av bv : Values)
    (n : Nat) (row : Int) (va : Stored h a av) (vb : Stored h b bv) :
    matrix_row.Call h (a, b, n, row) (rowHeap h av bv n row) h.nextRef := by
  refine ⟨⟨va.1, vb.1⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.matrix_row_pc17 ..)
  apply Reaches.prepend (Step.matrix_row_pc16 ..)
  apply Reaches.prepend (Step.matrix_row_pc15 ..)
  apply Reaches.prepend (Step.matrix_row_pc14 ..)
  have run := columns_loop n (.active (h.allocate (fun _ => 0))
    (.fn_matrix_row 4 { v0 := a, v1 := b, v2 := n, v3 := row, v4 := h.nextRef, t15 := h.nextRef }) stack)
    h a b av bv h.nextRef n row 0 True.intro rfl rfl rfl rfl rfl rfl (by omega)
    va vb (extends_allocate h _) (Nat.le_refl _) (by simp [Config.heap])
  simpa [Config.heap, rowHeap] using run stack

theorem rowHeap_extends (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    Extends h (rowHeap h av bv n row) :=
  (fill_extends (extends_allocate h _) h.nextRef (Nat.le_refl _) _ 0 n).trans
    (extends_tick _ "multiply_add" (n * n))

@[simp] theorem rowHeap_nextRef (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).nextRef = h.nextRef + 1 := by simp [rowHeap]

@[simp] theorem rowHeap_nextCollection (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).nextCollection = h.nextCollection := by
  simp [rowHeap, Heap.tick, Heap.allocate]

@[simp] theorem rowHeap_collections (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).collections = h.collections := by simp [rowHeap]

@[simp] theorem rowHeap_clocks (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).clocks = (h.tick "multiply_add" (n * n)).clocks := by
  simp [rowHeap, Heap.tick]

theorem rowHeap_result (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).store h.nextRef = rowValues av bv n row := by
  funext column
  simp only [rowHeap, Heap.tick_store, rowValues]
  split
  next inside => exact fill_inside _ _ _ _ _ _ (by simpa using inside)
  next outside =>
    rw [fill_outside _ _ _ _ _ _ (by omega)]
    simp [Heap.allocate]

/-- The prefix of rows already completed by the outer loop. -/
def partialProduct (av bv : Values) (n : Nat) (limit : Int) : Values :=
  fun row column => if 0 ≤ row ∧ row < limit then rowValues av bv n row column else 0

theorem partialProduct_zero (av bv : Values) (n : Nat) :
    partialProduct av bv n 0 = fun _ _ => 0 := by
  funext row column
  simp [partialProduct, show ¬ (0 ≤ row ∧ row < 0) by omega]

theorem partialProduct_done (av bv : Values) (n : Nat) :
    partialProduct av bv n n = product av bv n := by
  funext row column
  by_cases vr : 0 ≤ row ∧ row < (n : Int) <;>
    by_cases vc : 0 ≤ column ∧ column < (n : Int) <;>
    simp [partialProduct, rowValues, product, vr, vc]

theorem partialProduct_step (av bv : Values) (n : Nat) (first : Int) (nonnegative : 0 ≤ first) :
    (fun row => if row = first then rowValues av bv n first else partialProduct av bv n first row) =
      partialProduct av bv n (first + 1) := by
  funext row column
  by_cases same : row = first
  · subst row
    simp [partialProduct, nonnegative, show first < first + 1 by omega]
  · have equivalent : (0 ≤ row ∧ row < first + 1) ↔ (0 ≤ row ∧ row < first) := by omega
    simp [same, partialProduct, equivalent]

/-- Each completed row has its own consecutive fresh identity. -/
def RowReferences (h : Heap) (result : CollectionRef) (base count : Nat) : Prop :=
  ∀ i : Nat, i < count → rows.get h result i = some (base + i)

/-- Finish the outer loop, allocating a new independent row on each iteration. -/
theorem rows_loop (count : Nat) (state : Configuration) (original : Heap)
    (a b result : CollectionRef) (av bv : Values) (n : Nat) (first : Int)
    (location : matrix_multiply.At.rows_loop state)
    (ra : matrix_multiply.Local.a state = some a)
    (rb : matrix_multiply.Local.b state = some b)
    (rn : matrix_multiply.Local.n state = some (n : Int))
    (rr : matrix_multiply.Local.result state = some result)
    (ri : matrix_multiply.Local.row state = some first)
    (bound : first + (count : Int) = n) (nonnegative : 0 ≤ first)
    (va : Stored original a av) (vb : Stored original b bv)
    (extension : Extends original state.heap) (fresh : original.nextCollection ≤ result)
    (current : Stored state.heap result (partialProduct av bv n first))
    (base : Nat) (allocated : state.heap.nextRef = base + first.toNat)
    (references : RowReferences state.heap result base first.toNat) :
    ∃ after, matrix_multiply.CallFrom state after result ∧ Extends original after ∧
      Stored after result (product av bv n) ∧
      after.clocks = (state.heap.tick "multiply_add" (count * (n * n))).clocks ∧
      after.nextRef = base + n ∧ RowReferences after result base n := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_dot => cases location
    | fn_matrix_row => cases location
    | fn_matrix_multiply pc s =>
      have atLoop : pc = 4 := by unfold matrix_multiply.At.rows_loop at location; split at location <;> simp_all
      subst pc
      simp [matrix_multiply.Local.a, matrix_multiply.Local.b, matrix_multiply.Local.n,
        matrix_multiply.Local.result, matrix_multiply.Local.row] at ra rb rn rr ri
      dsimp only [Config.heap] at extension current allocated references ⊢
      induction count generalizing h s first with
      | zero =>
        have firstEq : first = n := by omega
        refine ⟨h, ?_, extension, ?_, by simp, ?_, ?_⟩
        · intro stack
          apply Reaches.prepend (Step.matrix_multiply_pc4 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc3_false _ _ _ (by simp [rn, ri]; omega))
          apply Reaches.prepend (Step.matrix_multiply_pc2 ..)
          simpa [rr] using Reaches.single (Step.matrix_multiply_pc1 h _ stack
            (by simpa [rr, show seq_Seq_Int = rows from rfl] using current.1))
        · simpa only [firstEq, partialProduct_done] using current
        · simpa [firstEq] using allocated
        · simpa [firstEq] using references
      | succ count ih =>
        let completed := rowHeap h av bv n first
        let updated := rows.set completed result first h.nextRef
        have rowExtension := rowHeap_extends h av bv n first
        have extended : Extends original updated :=
          (extension.trans rowExtension).set result fresh first h.nextRef
        have nextStored : Stored updated result (partialProduct av bv n (first + 1)) := by
          have installed := (current.mono rowExtension).set first h.nextRef
            (rowValues av bv n first) (by simp) (rowHeap_result h av bv n first)
          simpa only [partialProduct_step av bv n first nonnegative] using installed
        have nextAllocated : updated.nextRef = base + (first + 1).toNat := by
          have nextIndex : (first + 1).toNat = first.toNat + 1 := by omega
          simp [updated, completed, SequenceType.set, nextIndex, allocated, Nat.add_assoc]
        have nextReferences : RowReferences updated result base (first + 1).toNat := by
          intro i validIndex
          by_cases currentRow : (i : Int) = first
          · have eq : i = first.toNat := by omega
            change rows.get (rows.set completed result first h.nextRef) result (i : Int) = some (base + i)
            rw [currentRow, rows.get_set_same _ _ _ _ (rowExtension.valid current.1), allocated, eq]
          · have earlier : i < first.toNat := by omega
            rw [show rows.get updated result i = rows.get completed result i from
              rows.get_set_other_index _ _ _ _ _ currentRow]
            exact (rowExtension.get current.1 i).trans (references i earlier)
        obtain ⟨after, next, preserved, finalValues, clocks, finalAllocated, finalReferences⟩ := ih (h := updated)
          (s := { s with v4 := first + 1, t6 := decide (s.v4 < s.v2), t7 := h.nextRef, t8 := first, t9 := result, t10 := a, t11 := b, t12 := n, t13 := first })
          (first := first + 1) (bound := by omega) (nonnegative := by omega)
          (location := True.intro) (extension := extended) (current := nextStored)
          (allocated := nextAllocated) (references := nextReferences)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (ri := rfl)
        refine ⟨after, ?_, preserved, finalValues, ?_, finalAllocated, finalReferences⟩
        · intro stack
          apply Reaches.prepend (Step.matrix_multiply_pc4 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc3_true _ _ _ (by simp [ri, rn]; omega))
          apply Reaches.prepend (Step.matrix_multiply_pc13 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc12 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc11 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc10 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc9 ..)
          simp only [rn]
          apply Reaches.trans ((row_summary h s.v0 s.v1 av bv n s.v4
            (by simpa [ra] using va.mono extension) (by simpa [rb] using vb.mono extension)).2 _)
          apply Reaches.prepend (Step.matrix_multiply_pc8 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc7 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc6 _ _ _ (by
            simpa [rr, ri, show seq_Seq_Int = rows from rfl] using rowExtension.valid current.1))
          apply Reaches.prepend (Step.matrix_multiply_pc5 ..)
          simpa [updated, completed, ra, rb, rn, rr, ri, show seq_Seq_Int = rows from rfl] using next stack
        · rw [clocks]
          funext clock
          by_cases same : clock = "multiply_add" <;>
            simp [updated, completed, SequenceType.set, Heap.tick, Nat.succ_mul, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm, same]

def costs (n : Nat) : Clocks := Clocks.single "multiply_add" (n ^ 3)

/-- Total correctness, input preservation, and exact cost for every natural
    dimension, including zero. Inputs and their rows may alias arbitrarily. -/
theorem summary (h : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat)
    (va : Stored h a av) (vb : Stored h b bv) :
    ∃ after, matrix_multiply.Call h (a, b, n) after h.nextCollection ∧
      Extends h after ∧ Stored after h.nextCollection (product av bv n) ∧
      Heap.cost h after = costs n ∧ after.nextRef = h.nextRef + 1 + n ∧
      RowReferences after h.nextCollection (h.nextRef + 1) n := by
  let zero := h.allocate (fun _ => 0)
  let initial := (rows.const zero h.nextRef).1
  have extension : Extends h initial :=
    (extends_allocate h _).trans (extends_const zero h.nextRef)
  have initialValues : Stored initial h.nextCollection (partialProduct av bv n 0) := by
    have stored := stored_const zero h.nextRef (fun _ => 0)
      (by simp [zero]) (by funext i; simp [zero, Heap.allocate])
    simpa [initial, zero, SequenceType.const, SequenceType.create, Heap.createSequence,
      partialProduct_zero] using stored
  obtain ⟨after, finish, preserved, values, clocks, allocated, references⟩ := rows_loop n
    (.active initial (.fn_matrix_multiply 4
      { v0 := a, v1 := b, v2 := n, v3 := h.nextCollection, t14 := h.nextCollection, t15 := h.nextRef }) [])
    h a b h.nextCollection av bv n 0 True.intro rfl rfl rfl rfl rfl (by omega) (by omega)
    va vb extension (Nat.le_refl _) initialValues (h.nextRef + 1) rfl (by intro i impossible; omega)
  refine ⟨after, ⟨⟨va.1, vb.1⟩, ?_⟩, preserved, values, ?_, allocated, references⟩
  · intro stack
    apply Reaches.prepend (Step.matrix_multiply_pc18 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc17 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc16 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc15 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc14 ..)
    exact finish stack
  · funext clock
    by_cases same : clock = "multiply_add" <;>
      simp [same, Heap.cost, clocks, costs, Clocks.single, Config.heap, initial, zero,
      SequenceType.const, SequenceType.create, Heap.createSequence, Heap.allocateSequence,
      Heap.tick, Nat.pow_succ, Nat.mul_assoc]

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

/-- Any completed execution has the values, preservation, and cost of the
    terminating execution constructed above. -/
theorem execution_correct (h after : Heap) (a b result : CollectionRef)
    (av bv : Values) (n : Nat) (va : Stored h a av) (vb : Stored h b bv)
    (run : matrix_multiply.Run h (a, b, n) after result) :
    result = h.nextCollection ∧ Extends h after ∧ Stored after result (product av bv n) ∧
      Heap.cost h after = costs n ∧ after.nextRef = h.nextRef + 1 + n ∧
      RowReferences after result (h.nextRef + 1) n := by
  obtain ⟨final, call, extension, values, cost, allocated, references⟩ := summary h a b av bv n va vb
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
    run.2 call.2.root (by intro next impossible; cases impossible) (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, extension, values, cost, allocated, references⟩

/-- The returned heap carries a genuine nested-array result. -/
theorem output_with_cost (h : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat)
    (va : Stored h a av) (vb : Stored h b bv) :
    ∃ after, matrix_multiply.ReturnsWithCost (h, a, b, n) (after, h.nextCollection) (costs n) ∧
      Stored after h.nextCollection (product av bv n) ∧ Extends h after := by
  obtain ⟨after, call, extension, values, cost, _, _⟩ := summary h a b av bv n va vb
  exact ⟨after, ⟨call.run, cost⟩, values, extension⟩

theorem terminates (h : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat)
    (va : Stored h a av) (vb : Stored h b bv) :
    ∃ result, matrix_multiply.Returns (h, a, b, n) result := by
  obtain ⟨after, run, _, _⟩ := output_with_cost h a b av bv n va vb
  exact ⟨(after, h.nextCollection), run.returns⟩

-- Main result: Correctness
/-- Every result is the finite matrix product in arrays of row arrays, zero
    outside [0,n)×[0,n), with all original input arrays and rows unchanged. -/
theorem every_output_correct (h : Heap) (a b : CollectionRef) (av bv : Values)
    (n : Nat) (result : Heap × CollectionRef) (va : Stored h a av) (vb : Stored h b bv)
    (run : matrix_multiply.Returns (h, a, b, n) result) :
    Stored result.1 result.2 (product av bv n) ∧ Extends h result.1 := by
  have correct := execution_correct h result.1 a b result.2 av bv n va vb run
  exact ⟨correct.2.2.1, correct.2.1⟩

/-- No completed execution overwrites pre-existing inner rows, outer arrays,
    or objects. This also covers shared rows and aliased inputs. -/
theorem every_execution_preserves (h after : Heap) (a b result : CollectionRef)
    (av bv : Values) (n : Nat) (va : Stored h a av) (vb : Stored h b bv)
    (run : matrix_multiply.Run h (a, b, n) after result) : Extends h after :=
  (execution_correct h after a b result av bv n va vb run).2.1

/-- A matrix cell contains the familiar finite row-by-column sum. -/
theorem product_entry (a b : Values) (n row column : Nat)
    (validRow : row < n) (validColumn : column < n) :
    product a b n row column = dotFrom a b row column 0 n := by
  simp [product, entry, show (0 : Int) ≤ row by omega,
    show (row : Int) < n by omega, show (0 : Int) ≤ column by omega,
    show (column : Int) < n by omega]

-- Main result: Running time
/-- For every natural n, every execution charges exactly n³ multiply-add units:
    Θ(n³) counted work. Units count scalar multiplications with accumulation;
    every other named clock is unchanged. Array allocations, loop bookkeeping,
    and integer bit complexity are excluded. -/
theorem runtime_cubic (h : Heap) (a b : CollectionRef) (av bv : Values)
    (n : Nat) (result : Heap × CollectionRef) (charged : Clocks)
    (va : Stored h a av) (vb : Stored h b bv)
    (run : matrix_multiply.ReturnsWithCost (h, a, b, n) result charged) :
    charged = costs n ∧ n ^ 3 ≤ charged "multiply_add" ∧ charged "multiply_add" ≤ n ^ 3 := by
  have correct := execution_correct h result.1 a b result.2 av bv n va vb run.1
  have eq : charged = costs n := run.2.symm.trans correct.2.2.2.1
  simp [eq, costs, Clocks.single]

/-- Every finite output row has a fresh identity, and different row indices
    have different identities. Thus later writes to one row cannot alias another. -/
theorem every_execution_fresh_rows (h after : Heap) (a b result : CollectionRef)
    (av bv : Values) (n : Nat) (va : Stored h a av) (vb : Stored h b bv)
    (run : matrix_multiply.Run h (a, b, n) after result) :
    (∀ i : Nat, i < n → rows.get after result i = some (h.nextRef + 1 + i) ∧
      h.nextRef < h.nextRef + 1 + i ∧ h.nextRef + 1 + i < after.nextRef) ∧
    (∀ i j : Nat, i < n → j < n → i ≠ j →
      rows.get after result i ≠ rows.get after result j) := by
  have correct := execution_correct h after a b result av bv n va vb run
  have allocated := correct.2.2.2.2.1
  have references := correct.2.2.2.2.2
  constructor
  · intro i valid
    exact ⟨references i valid, by omega, by omega⟩
  · intro i j vi vj different
    rw [references i vi, references j vj]
    intro same
    have equal : h.nextRef + 1 + i = h.nextRef + 1 + j := Option.some.inj same
    omega


/-- One unit per scalar multiplication with accumulation. -/
def runtime (charged : Clocks) : Nat := charged "multiply_add"

-- Main result: Correctness and running time
/-- All natural dimensions, including zero, admit a finite source call returning
the matrix product. Old storage is preserved; the outer array and finite rows
are fresh. The same call charges exactly n³ multiply-adds and no other clocks.
The uniform constant may be chosen as 1. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          matrix_multiply.Call heap (a, b, (n : Int)) after result ∧
          Stored after result (product av bv n) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result n ∧
          heap.Increments after (MatrixMultiplyAnalysis.costs n) ∧
          n^3 ≤ runtime (heap.cost after) ∧ runtime (heap.cost after) ≤ C*n^3 := by
  refine ⟨1, by decide, ?_⟩
  intro heap a b av bv n sa sb
  obtain ⟨after, call, frame, stored, cost, allocated, references⟩ :=
    MatrixMultiplyAnalysis.summary heap a b av bv n sa sb
  have fresh := MatrixMultiplyAnalysis.every_execution_fresh_rows
    heap after a b heap.nextCollection av bv n sa sb call.run
  have monotone : heap.ClocksMonotone after := by
    intro clock
    have resumed : ∀ (h : Heap) (r : Algo2LeanGenerated.Result)
        (s : Algo2LeanGenerated.Stack),
        (resumeConfig h r s).heap = h := by
      intro h r s
      cases s <;> rfl
    have one : ∀ {before next : Algo2LeanGenerated.Configuration},
        Algo2LeanGenerated.Step before next →
          before.heap.clocks clock ≤ next.heap.clocks clock := by
      intro before next step
      cases step
      all_goals try simp only [resumed]
      all_goals simp only [Config.heap, Heap.write_clocks, Heap.allocate_clocks,
        SequenceType.set, SequenceType.const, SequenceType.create, Heap.createSequence,
        Heap.writeElement, Heap.allocateSequence]
      all_goals try exact Nat.le_refl _
      all_goals exact Heap.clocks_le_tick _ _ _ _
    have ordered := call.run.2.invariant
      (fun state => heap.clocks clock ≤ state.heap.clocks clock) (Nat.le_refl _)
      (fun _ _ move previous => Nat.le_trans previous (one move))
    exact ordered
  refine ⟨after, heap.nextCollection, call, ?_, frame, Nat.le_refl _, stored.1.1, ?_, ?_, ?_⟩
  · exact stored
  · constructor
    · intro i hi
      exact ⟨heap.nextRef + 1 + i, (fresh.1 i hi).1,
        Nat.le_of_lt (fresh.1 i hi).2.1, (fresh.1 i hi).2.2⟩
    · intro i j hi hj equal
      by_cases different : i = j
      · exact different
      · exact False.elim (fresh.2 i j hi hj different equal)
  · simpa only [cost] using monotone.increments
  · simp [cost, runtime, MatrixMultiplyAnalysis.costs, Clocks.single]


/-- Reusable total call contract: product, preserved caller storage, a fresh
outer array with independent finite rows, and exact increments of every clock. -/
theorem call (heap : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result,
      matrix_multiply.Call heap (a, b, (n : Int)) after result ∧
      Stored after result (product av bv n) ∧ Extends heap after ∧
      heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
      FreshRows heap after result n ∧ heap.Increments after (costs n) := by
  obtain ⟨_, _, contract⟩ := correctness_and_running_time
  obtain ⟨after, result, execution, stored, frame, lower, upper, fresh, charged, _⟩ :=
    contract heap a b av bv n sa sb
  exact ⟨after, result, execution, stored, frame, lower, upper, fresh, charged⟩

end MatrixMultiplyAnalysis
