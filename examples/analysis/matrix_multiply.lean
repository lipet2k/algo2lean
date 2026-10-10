import MatrixMultiplyGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Ordinary square-matrix multiplication, verified against the generated mutable
sequence program. `dot_loop` verifies the inner loop; `cells_loop` composes those
summaries for all n² output cells. `summary` constructs a terminating execution
for every natural dimension (including zero), and determinism gives the complete
`output_with_cost_iff` characterization.

`product_entry` expresses the familiar row-by-column finite sum. The returned
object is fresh, every input object is preserved, and the multiply-add clock is
exactly n³. This clock counts scalar multiply-add operations, with mathematical
integer arithmetic; it does not measure integer bit complexity or wall-clock time.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace MatrixMultiplyAnalysis

/-- The finite mathematical dot product, with arbitrary integer entries. -/
def dotFrom (a b : Seq) (n row column first : Int) : Nat → Int
  | 0 => 0
  | count + 1 => a (row * n + first) * b (first * n + column) +
      dotFrom a b n row column (first + 1) count

def entry (a b : Seq) (n : Nat) (cell : Int) : Int :=
  dotFrom a b n (Int.fdiv cell n) (Int.fmod cell n) 0 n

/-- The matrix occupies [0,n²); the fresh output is zero everywhere else. -/
def product (a b : Seq) (n : Nat) : Seq :=
  fun cell => if 0 ≤ cell ∧ cell < (n * n : Nat) then entry a b n cell else 0

/-- Consecutive writes of a mathematical sequence to one output object. -/
def fill (h : Heap) (r : SeqRef) (values : Seq) (first : Int) : Nat → Heap
  | 0 => h
  | count + 1 => fill (h.write r first (values first)) r values (first + 1) count

@[simp] theorem fill_nextRef (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).nextRef = h.nextRef := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih, Heap.write]

@[simp] theorem fill_clocks (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).clocks = h.clocks := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih, Heap.write]

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

/-- Finishing the dot-product loop adds the remaining summands and charges once
    for each scalar multiply-add, for any initial heap and caller. -/
theorem dot_loop (count : Nat) (state : Configuration)
    (a b : SeqRef) (n row column first total : Int)
    (location : matrix_dot.At.dot_loop state)
    (ra : matrix_dot.Local.a state = some a)
    (rb : matrix_dot.Local.b state = some b)
    (rn : matrix_dot.Local.n state = some n)
    (rr : matrix_dot.Local.row state = some row)
    (rc : matrix_dot.Local.column state = some column)
    (rk : matrix_dot.Local.k state = some first)
    (rt : matrix_dot.Local.total state = some total)
    (bound : n = first + (count : Int))
    (va : a < state.heap.nextRef) (vb : b < state.heap.nextRef) :
    matrix_dot.CallFrom state (state.heap.tick "multiply_add" count)
      (total + dotFrom (state.heap.store a) (state.heap.store b) n row column first count) := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_multiply => cases location
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
        have next := ih (h := h.tick "multiply_add")
          (s := { s with v5 := first + 1, v6 := total + h.read a (row * n + first) * h.read b (first * n + column), t8 := decide (s.v5 < s.v2) }) (first := first + 1)
          (total := total + h.read a (row * n + first) * h.read b (first * n + column))
          (bound := by omega) (location := True.intro) (va := va) (vb := vb)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (rc := rc) (rk := rfl) (rt := rfl)
        intro stack
        apply Reaches.prepend (Step.matrix_dot_pc4 ..)
        apply Reaches.prepend (Step.matrix_dot_pc3_true _ _ _ (by simp; omega))
        apply Reaches.prepend (Step.matrix_dot_pc7 ..)
        apply Reaches.prepend (Step.matrix_dot_pc6 _ _ _ ⟨by simpa [ra] using va, by simpa [rb] using vb⟩)
        apply Reaches.prepend (Step.matrix_dot_pc5 ..)
        simpa [dotFrom, ra, rb, rn, rr, rc, rk, rt, Heap.read, Heap.tick_add,
          Nat.add_comm 1, Int.add_assoc] using next stack

/-- Full dot-product summary, including its exact number of multiply-adds. -/
theorem dot_summary (h : Heap) (a b : SeqRef) (n : Nat) (row column : Int)
    (va : a < h.nextRef) (vb : b < h.nextRef) :
    matrix_dot.Call h (a, b, n, row, column) (h.tick "multiply_add" n)
      (dotFrom (h.store a) (h.store b) n row column 0 n) := by
  refine ⟨⟨va, vb⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.matrix_dot_pc9 ..)
  apply Reaches.prepend (Step.matrix_dot_pc8 ..)
  have run := dot_loop n (.active h (.fn_matrix_dot 4
    { v0 := a, v1 := b, v2 := n, v3 := row, v4 := column }) stack)
    a b n row column 0 0 True.intro rfl rfl rfl rfl rfl rfl rfl (by omega) va vb
  simpa [Config.heap] using run stack

/-- Finish the consecutive output cells. Input references can alias each other;
    only the fresh result must be distinct from them. -/
theorem cells_loop (count : Nat) (state : Configuration) (a b result : SeqRef)
    (n : Nat) (first : Int)
    (location : matrix_multiply.At.cells_loop state)
    (ra : matrix_multiply.Local.a state = some a)
    (rb : matrix_multiply.Local.b state = some b)
    (rn : matrix_multiply.Local.n state = some (n : Int))
    (rr : matrix_multiply.Local.result state = some result)
    (ri : matrix_multiply.Local.cell state = some first)
    (bound : first + (count : Int) = (n * n : Nat)) (nonnegative : 0 ≤ first)
    (va : a < state.heap.nextRef) (vb : b < state.heap.nextRef)
    (vr : result < state.heap.nextRef) (da : a ≠ result) (db : b ≠ result) :
    matrix_multiply.CallFrom state
      ((fill state.heap result (entry (state.heap.store a) (state.heap.store b) n) first count).tick
        "multiply_add" (count * n)) result := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_dot => cases location
    | fn_matrix_multiply pc s =>
      have atLoop : pc = 4 := by unfold matrix_multiply.At.cells_loop at location; split at location <;> simp_all
      subst pc
      simp [matrix_multiply.Local.a, matrix_multiply.Local.b, matrix_multiply.Local.n,
        matrix_multiply.Local.result, matrix_multiply.Local.cell] at ra rb rn rr ri
      dsimp only [Config.heap] at va vb vr ⊢
      induction count generalizing h s first with
      | zero =>
        intro stack
        apply Reaches.prepend (Step.matrix_multiply_pc4 ..)
        apply Reaches.prepend (Step.matrix_multiply_pc3_false _ _ _ (by simp [rn, ri]; omega))
        apply Reaches.prepend (Step.matrix_multiply_pc2 ..)
        simpa [fill, rr] using Reaches.single (Step.matrix_multiply_pc1 h _ stack (by simpa [rr] using vr))
      | succ count ih =>
        have positive : n ≠ 0 := by intro zero; simp [zero] at bound; omega
        let value := entry (h.store a) (h.store b) n first
        let updated := (h.tick "multiply_add" n).write result first value
        have sameA : updated.store a = h.store a := by funext i; simp [updated, Heap.write, da]
        have sameB : updated.store b = h.store b := by funext i; simp [updated, Heap.write, db]
        have next := ih (h := updated)
          (s := { s with v4 := first + 1, v5 := value, t7 := decide (s.v4 < s.v2 * s.v2), t8 := value, t9 := a, t10 := b, t11 := n, t12 := Int.fdiv first n, t13 := Int.fmod first n })
          (first := first + 1) (bound := by omega) (nonnegative := by omega)
          (location := True.intro) (va := va) (vb := vb) (vr := vr)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (ri := rfl)
        intro stack
        apply Reaches.prepend (Step.matrix_multiply_pc4 ..)
        apply Reaches.prepend (Step.matrix_multiply_pc3_true _ _ _ (by simp [ri, rn]; omega))
        apply Reaches.prepend (Step.matrix_multiply_pc13 ..)
        apply Reaches.prepend (Step.matrix_multiply_pc12 ..)
        apply Reaches.prepend (Step.matrix_multiply_pc11 ..)
        apply Reaches.prepend (Step.matrix_multiply_pc10 _ _ _ (by simp [rn, positive]))
        apply Reaches.prepend (Step.matrix_multiply_pc9 _ _ _ (by simp [rn, positive]))
        apply Reaches.prepend (Step.matrix_multiply_pc8 ..)
        simp only [rn]
        apply Reaches.trans ((dot_summary h s.v0 s.v1 n (Int.fdiv s.v4 n) (Int.fmod s.v4 n)
          (by simpa [ra] using va) (by simpa [rb] using vb)).2 _)
        apply Reaches.prepend (Step.matrix_multiply_pc7 ..)
        apply Reaches.prepend (Step.matrix_multiply_pc6 _ _ _ (by simpa [rr] using vr))
        apply Reaches.prepend (Step.matrix_multiply_pc5 ..)
        have nextRun := next stack
        simp only [sameA, sameB] at nextRun
        simpa [value, updated, entry, ra, rb, rn, rr, ri,
          fill, fill_tick, Heap.tick_add, Nat.succ_mul, Nat.add_comm] using nextRun

/-- A fresh result is filled with n² dot products. -/
def finalHeap (h : Heap) (a b : SeqRef) (n : Nat) : Heap :=
  (fill (h.allocate (fun _ => 0)) h.nextRef (entry (h.store a) (h.store b) n)
    0 (n * n)).tick "multiply_add" (n * n * n)

/-- Termination, returned reference, heap effects and exact operation count. -/
theorem summary (h : Heap) (a b : SeqRef) (n : Nat)
    (va : a < h.nextRef) (vb : b < h.nextRef) :
    matrix_multiply.Call h (a, b, n) (finalHeap h a b n) h.nextRef := by
  refine ⟨⟨va, vb⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.matrix_multiply_pc17 ..)
  apply Reaches.prepend (Step.matrix_multiply_pc16 ..)
  apply Reaches.prepend (Step.matrix_multiply_pc15 ..)
  apply Reaches.prepend (Step.matrix_multiply_pc14 ..)
  have run := cells_loop (n * n) (.active (h.allocate (fun _ => 0))
    (.fn_matrix_multiply 4 { v0 := a, v1 := b, v2 := n, v3 := h.nextRef, t14 := h.nextRef }) stack)
    a b h.nextRef n 0 True.intro rfl rfl rfl rfl rfl (by omega) (by omega)
    (Nat.lt_succ_of_lt va) (Nat.lt_succ_of_lt vb)
    (by simp [Config.heap, Heap.allocate]) (Nat.ne_of_lt va) (Nat.ne_of_lt vb)
  have sameA : (h.allocate (fun _ => 0)).store a = h.store a := by simp [Heap.allocate, Nat.ne_of_lt va]
  have sameB : (h.allocate (fun _ => 0)).store b = h.store b := by simp [Heap.allocate, Nat.ne_of_lt vb]
  simpa [Config.heap, finalHeap, sameA, sameB] using run stack

/-- The result has the usual matrix-product entries, and is zero outside its
    finite matrix footprint. -/
theorem finalHeap_result (h : Heap) (a b : SeqRef) (n : Nat) :
    (finalHeap h a b n).store h.nextRef = product (h.store a) (h.store b) n := by
  funext cell
  simp only [finalHeap, Heap.tick_store, product]
  split
  next inside =>
    exact fill_inside _ _ _ _ _ _ (by simpa using inside)
  next outside =>
    rw [fill_outside _ _ _ _ _ _ (by omega)]
    simp [Heap.allocate]

/-- All pre-existing sequence objects survive unchanged, including aliased
    inputs. The allocation is fresh and valid. -/
theorem finalHeap_preserves (h : Heap) (a b : SeqRef) (n : Nat) :
    (finalHeap h a b n).nextRef = h.nextRef + 1 ∧
    ∀ object, object < h.nextRef → (finalHeap h a b n).store object = h.store object := by
  refine ⟨by simp [finalHeap, Heap.allocate], ?_⟩
  intro object valid
  simp only [finalHeap, Heap.tick_store]
  rw [fill_other _ _ _ _ _ _ (Nat.ne_of_lt valid)]
  simp [Heap.allocate, Nat.ne_of_lt valid]

def costs (n : Nat) : Clocks := Clocks.single "multiply_add" (n ^ 3)

/-- Exactly n³ multiply-adds; every other counter is unchanged. -/
theorem finalHeap_cost (h : Heap) (a b : SeqRef) (n : Nat) :
    Heap.cost h (finalHeap h a b n) = costs n := by
  funext name
  by_cases same : name = "multiply_add" <;>
    simp [same, Heap.cost, finalHeap, Heap.tick, Heap.allocate, costs, Clocks.single,
    Nat.pow_succ]

/-- A reusable contract exposes the product, fresh allocation, preservation of
    old sequences, and the exact clock increments in one generated call. -/
theorem call (heap : Heap) (a b : SeqRef) (n : Nat)
    (left : a < heap.nextRef) (right : b < heap.nextRef) :
    ∃ after, matrix_multiply.Call heap (a, b, n) after heap.nextRef ∧
      after.store heap.nextRef = product (heap.store a) (heap.store b) n ∧
      after.nextRef = heap.nextRef + 1 ∧
      (∀ old, old < heap.nextRef → after.store old = heap.store old) ∧
      Heap.cost heap after = costs n :=
  ⟨finalHeap heap a b n, summary heap a b n left right,
    finalHeap_result heap a b n, (finalHeap_preserves heap a b n).1,
    (finalHeap_preserves heap a b n).2, finalHeap_cost heap a b n⟩

/-- Total correctness and exact cost for every natural dimension, including the
    empty matrix, with unrestricted integer input entries. -/
theorem output_with_cost (a b : Seq) (n : Nat) :
    matrix_multiply.ReturnsWithCost (a, b, n) (product a b n) (costs n) := by
  let h := (matrix_multiply.load (a, b, (n : Int))).1
  obtain ⟨after, execution, productValue, allocated, preserved, cost⟩ :=
    call h 0 1 n (by simp [h, matrix_multiply.load, Heap.allocate])
      (by simp [h, matrix_multiply.load, Heap.allocate])
  exact ⟨after, h.nextRef, execution.run, productValue, cost⟩


theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

/-- Every execution agrees with the constructed terminating execution. -/
theorem execution_correct (h after : Heap) (a b : SeqRef) (n : Nat) (result : SeqRef)
    (run : matrix_multiply.Run h (a, b, n) after result) :
    after = finalHeap h a b n ∧ result = h.nextRef := by
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
    run.2 (summary h a b n run.1.1 run.1.2).2.root
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

/-- Characterization of all completed runs: the correctness specification and
    cubic cost describe the very same execution. -/
theorem output_with_cost_iff (a b result : Seq) (n : Nat) (charged : Clocks) :
    matrix_multiply.ReturnsWithCost (a, b, n) result charged ↔
      result = product a b n ∧ charged = costs n := by
  constructor
  · rintro ⟨after, ref, run, value, cost⟩
    obtain ⟨rfl, rfl⟩ := execution_correct _ _ _ _ _ _ run
    refine ⟨?_, ?_⟩
    · rw [← value, finalHeap_result]
      rfl
    · exact cost.symm.trans (finalHeap_cost _ _ _ _)
  · rintro ⟨rfl, rfl⟩
    exact output_with_cost a b n

/-- Every natural-size matrix multiplication has a completed execution. -/
theorem terminates (a b : Seq) (n : Nat) :
    ∃ result, matrix_multiply.Returns (a, b, n) result :=
  ⟨product a b n, (output_with_cost a b n).returns⟩

-- Main result: Correctness
/-- Every returned sequence has precisely the mathematical product entries. -/
theorem every_output_correct (a b result : Seq) (n : Nat)
    (run : matrix_multiply.Returns (a, b, n) result) : result = product a b n := by
  obtain ⟨charged, execution⟩ := run.withCost
  exact ((output_with_cost_iff a b result n charged).mp execution).1

/-- No completed execution can overwrite an input or an earlier heap object. -/
theorem every_execution_preserves (h after : Heap) (a b result : SeqRef) (n : Nat)
    (run : matrix_multiply.Run h (a, b, n) after result) :
    result = h.nextRef ∧ result < after.nextRef ∧
      ∀ object, object < h.nextRef → after.store object = h.store object := by
  obtain ⟨rfl, rfl⟩ := execution_correct _ _ _ _ _ _ run
  have preservation := finalHeap_preserves h a b n
  refine ⟨rfl, ?_, preservation.2⟩
  rw [preservation.1]
  exact Nat.lt_succ_self h.nextRef

/-- A matrix cell (row,column) contains the finite sum of the row-column
    products. This spells out the usual two-index matrix specification. -/
theorem product_entry (a b : Seq) (n row column : Nat)
    (validRow : row < n) (validColumn : column < n) :
    product a b n (row * n + column : Nat) = dotFrom a b n row column 0 n := by
  have positive : 0 < n := by omega
  have inside : row * n + column < n * n :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left validColumn (row * n))
      (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right n validRow)
  have div : (row * n + column) / n = row := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ positive]
    simp [Nat.div_eq_of_lt validColumn]
  have mod : (row * n + column) % n = column := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt validColumn]
  simp only [product, entry]
  rw [if_pos ⟨by omega, by exact_mod_cast inside⟩]
  rw [← Int.ofNat_fdiv, ← Int.ofNat_fmod, div, mod]

-- Main result: Running time
/-- Exact cost supplies matching cubic upper and lower bounds with constant 1. -/
theorem runtime_cubic (a b result : Seq) (n : Nat) (charged : Clocks)
    (run : matrix_multiply.ReturnsWithCost (a, b, n) result charged) :
    n ^ 3 ≤ charged "multiply_add" ∧ charged "multiply_add" ≤ n ^ 3 := by
  obtain ⟨_, rfl⟩ := (output_with_cost_iff a b result n charged).mp run
  simp [costs, Clocks.single]

end MatrixMultiplyAnalysis
