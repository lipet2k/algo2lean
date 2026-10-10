import MatrixRecursiveGenerated

open Algo2LeanCore Algo2LeanGenerated
namespace MatrixRecursiveAnalysis

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- A complete eight-way block multiplication, modeled by its heap effect. -/
def blockEffect (a b c : SeqRef) (stride : Int) : Nat → Heap → Int → Int → Int → Heap
  | 0, heap, row, col, inner =>
    ((heap.tick "calls").tick "multiplications").write c (row * stride + col)
      (heap.read c (row * stride + col) + heap.read a (row * stride + inner) *
        heap.read b (inner * stride + col))
  | depth + 1, heap, row, col, inner =>
    let heap := heap.tick "calls"
    let half : Int := (2 ^ depth : Nat)
    let h1 := blockEffect a b c stride depth heap (row) (col) (inner)
    let h2 := blockEffect a b c stride depth h1 (row) (col) (inner + half)
    let h3 := blockEffect a b c stride depth h2 (row) (col + half) (inner)
    let h4 := blockEffect a b c stride depth h3 (row) (col + half) (inner + half)
    let h5 := blockEffect a b c stride depth h4 (row + half) (col) (inner)
    let h6 := blockEffect a b c stride depth h5 (row + half) (col) (inner + half)
    let h7 := blockEffect a b c stride depth h6 (row + half) (col + half) (inner)
    let h8 := blockEffect a b c stride depth h7 (row + half) (col + half) (inner + half)
    h8

@[simp] theorem blockEffect_nextRef (depth : Nat) (heap : Heap)
    (a b c : SeqRef) (stride row col inner : Int) :
    (blockEffect a b c stride depth heap row col inner).nextRef = heap.nextRef := by
  induction depth generalizing heap row col inner with
  | zero => rfl
  | succ depth ih => simp only [blockEffect, ih, Heap.tick_nextRef]

/-- Finite terminating execution of all eight calls, for every power-of-two size. -/
theorem block_summary (depth : Nat) (heap : Heap) (a b c : SeqRef)
    (stride row col inner : Int)
    (ha : a < heap.nextRef) (hb : b < heap.nextRef) (hc : c < heap.nextRef) :
    matrix_block.Call heap (a, b, c, stride, row, col, inner, (2 ^ depth : Nat))
      (blockEffect a b c stride depth heap row col inner) 0 := by
  induction depth generalizing heap row col inner with
  | zero =>
    refine ⟨⟨ha, hb, hc⟩, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_block_pc82 ..)
    apply Reaches.prepend (Step.matrix_block_pc81 ..)
    apply Reaches.prepend (Step.matrix_block_pc80_true _ _ _ (by simp))
    apply Reaches.prepend (Step.matrix_block_pc79 ..)
    apply Reaches.prepend (Step.matrix_block_pc78 _ _ _ ⟨⟨hc, ha, hb⟩, hc⟩)
    apply Reaches.prepend (Step.matrix_block_pc77 ..)
    exact Reaches.single (Step.matrix_block_pc76 ..)
  | succ depth ih =>
    have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
    have half_eq : Int.fdiv ((2 ^ (depth + 1) : Nat) : Int) 2 = ((2 ^ depth : Nat) : Int) := by
      simp [Nat.pow_succ, Int.fdiv_eq_ediv, Int.mul_ediv_cancel]
    refine ⟨⟨ha, hb, hc⟩, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_block_pc82 ..)
    apply Reaches.prepend (Step.matrix_block_pc81 ..)
    apply Reaches.prepend (Step.matrix_block_pc80_false _ _ _ (by
      simp only [decide_eq_false_iff_not, Nat.pow_succ, Int.natCast_mul]
      omega))
    apply Reaches.prepend (Step.matrix_block_pc75 _ _ _ (by decide))
    simp only [half_eq]
    apply Reaches.prepend (Step.matrix_block_pc74 ..)
    apply Reaches.prepend (Step.matrix_block_pc73 ..)
    apply Reaches.prepend (Step.matrix_block_pc72 ..)
    apply Reaches.prepend (Step.matrix_block_pc71 ..)
    apply Reaches.prepend (Step.matrix_block_pc70 ..)
    apply Reaches.prepend (Step.matrix_block_pc69 ..)
    apply Reaches.prepend (Step.matrix_block_pc68 ..)
    apply Reaches.prepend (Step.matrix_block_pc67 ..)
    apply Reaches.prepend (Step.matrix_block_pc66 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc65 ..)
    apply Reaches.prepend (Step.matrix_block_pc64 ..)
    apply Reaches.prepend (Step.matrix_block_pc63 ..)
    apply Reaches.prepend (Step.matrix_block_pc62 ..)
    apply Reaches.prepend (Step.matrix_block_pc61 ..)
    apply Reaches.prepend (Step.matrix_block_pc60 ..)
    apply Reaches.prepend (Step.matrix_block_pc59 ..)
    apply Reaches.prepend (Step.matrix_block_pc58 ..)
    apply Reaches.prepend (Step.matrix_block_pc57 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc56 ..)
    apply Reaches.prepend (Step.matrix_block_pc55 ..)
    apply Reaches.prepend (Step.matrix_block_pc54 ..)
    apply Reaches.prepend (Step.matrix_block_pc53 ..)
    apply Reaches.prepend (Step.matrix_block_pc52 ..)
    apply Reaches.prepend (Step.matrix_block_pc51 ..)
    apply Reaches.prepend (Step.matrix_block_pc50 ..)
    apply Reaches.prepend (Step.matrix_block_pc49 ..)
    apply Reaches.prepend (Step.matrix_block_pc48 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc47 ..)
    apply Reaches.prepend (Step.matrix_block_pc46 ..)
    apply Reaches.prepend (Step.matrix_block_pc45 ..)
    apply Reaches.prepend (Step.matrix_block_pc44 ..)
    apply Reaches.prepend (Step.matrix_block_pc43 ..)
    apply Reaches.prepend (Step.matrix_block_pc42 ..)
    apply Reaches.prepend (Step.matrix_block_pc41 ..)
    apply Reaches.prepend (Step.matrix_block_pc40 ..)
    apply Reaches.prepend (Step.matrix_block_pc39 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc38 ..)
    apply Reaches.prepend (Step.matrix_block_pc37 ..)
    apply Reaches.prepend (Step.matrix_block_pc36 ..)
    apply Reaches.prepend (Step.matrix_block_pc35 ..)
    apply Reaches.prepend (Step.matrix_block_pc34 ..)
    apply Reaches.prepend (Step.matrix_block_pc33 ..)
    apply Reaches.prepend (Step.matrix_block_pc32 ..)
    apply Reaches.prepend (Step.matrix_block_pc31 ..)
    apply Reaches.prepend (Step.matrix_block_pc30 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc29 ..)
    apply Reaches.prepend (Step.matrix_block_pc28 ..)
    apply Reaches.prepend (Step.matrix_block_pc27 ..)
    apply Reaches.prepend (Step.matrix_block_pc26 ..)
    apply Reaches.prepend (Step.matrix_block_pc25 ..)
    apply Reaches.prepend (Step.matrix_block_pc24 ..)
    apply Reaches.prepend (Step.matrix_block_pc23 ..)
    apply Reaches.prepend (Step.matrix_block_pc22 ..)
    apply Reaches.prepend (Step.matrix_block_pc21 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc20 ..)
    apply Reaches.prepend (Step.matrix_block_pc19 ..)
    apply Reaches.prepend (Step.matrix_block_pc18 ..)
    apply Reaches.prepend (Step.matrix_block_pc17 ..)
    apply Reaches.prepend (Step.matrix_block_pc16 ..)
    apply Reaches.prepend (Step.matrix_block_pc15 ..)
    apply Reaches.prepend (Step.matrix_block_pc14 ..)
    apply Reaches.prepend (Step.matrix_block_pc13 ..)
    apply Reaches.prepend (Step.matrix_block_pc12 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc11 ..)
    apply Reaches.prepend (Step.matrix_block_pc10 ..)
    apply Reaches.prepend (Step.matrix_block_pc9 ..)
    apply Reaches.prepend (Step.matrix_block_pc8 ..)
    apply Reaches.prepend (Step.matrix_block_pc7 ..)
    apply Reaches.prepend (Step.matrix_block_pc6 ..)
    apply Reaches.prepend (Step.matrix_block_pc5 ..)
    apply Reaches.prepend (Step.matrix_block_pc4 ..)
    apply Reaches.prepend (Step.matrix_block_pc3 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc2 ..)
    exact Reaches.single (Step.matrix_block_pc1 ..)



/-- Recursive multiplication never changes any other allocated input object. -/
@[simp] theorem blockEffect_read_other (depth : Nat) (heap : Heap)
    (a b c other : SeqRef) (stride row col inner index : Int) (hne : other ≠ c) :
    (blockEffect a b c stride depth heap row col inner).read other index = heap.read other index := by
  induction depth generalizing heap row col inner with
  | zero => simp [blockEffect, hne]
  | succ depth ih => simp only [blockEffect, ih, Heap.read_tick]

/-- Recursion includes the current call and eight children. -/
def callCount : Nat → Nat
  | 0 => 1
  | depth + 1 => 1 + 8 * callCount depth

/-- Exactly one scalar multiplication at each of the eight-way recursion leaves. -/
@[simp] theorem blockEffect_clocks (depth : Nat) (heap : Heap)
    (a b c : SeqRef) (stride row col inner : Int) (name : String) :
    (blockEffect a b c stride depth heap row col inner).clocks name =
      heap.clocks name + if name = "multiplications" then 8 ^ depth else
        if name = "calls" then callCount depth else 0 := by
  induction depth generalizing heap row col inner with
  | zero =>
    by_cases hname : name = "multiplications" <;> by_cases hcalls : name = "calls" <;>
      simp_all [blockEffect, Heap.tick, callCount]
  | succ depth ih =>
    simp only [blockEffect, ih]
    by_cases hname : name = "multiplications"
    · subst name
      simp [Nat.pow_succ, Heap.tick]
      omega
    · by_cases hcalls : name = "calls"
      · subst name
        simp [Heap.tick, callCount]
        omega
      · simp [hname, hcalls, Heap.tick]

/-- The cubic scalar count, stated without an asymptotic approximation. -/
theorem multiplications_cubic (depth : Nat) : 8 ^ depth = (2 ^ depth) ^ 3 := by
  have h := Nat.pow_mul 2 3 depth
  simpa [← Nat.pow_mul, Nat.mul_comm] using h.symm

/-- The public entry allocates a fresh zero output; its inputs remain separate. -/
theorem recursive_summary (depth : Nat) (heap : Heap) (a b : SeqRef)
    (ha : a < heap.nextRef) (hb : b < heap.nextRef) :
    matrix_recursive.Call heap (a, b, (2 ^ depth : Nat))
      (blockEffect a b heap.nextRef (2 ^ depth : Nat) depth
        (heap.allocate (fun _ => 0)) 0 0 0) heap.nextRef := by
  refine ⟨⟨ha, hb⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.matrix_recursive_pc14 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc13 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc12 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc11 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc10 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc9 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc8 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc7 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc6 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc5 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc4 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc3 ..)
  apply Reaches.trans ((block_summary depth _ _ _ _ _ _ _ _
    (by simpa using Nat.lt_succ_of_lt ha) (by simpa using Nat.lt_succ_of_lt hb)
    (by simp)).2 _)
  apply Reaches.prepend (Step.matrix_recursive_pc2 ..)
  exact Reaches.single (Step.matrix_recursive_pc1 _ _ _ (by simp))



/-- The ordinary inner-product sum, split into equal halves. -/
def innerProduct (a b : Seq) (stride queryRow queryCol : Int) : Nat → Int → Int
  | 0, first => a (queryRow * stride + first) * b (first * stride + queryCol)
  | depth + 1, first =>
    innerProduct a b stride queryRow queryCol depth first +
    innerProduct a b stride queryRow queryCol depth (first + (2 ^ depth : Nat))

/-- The contribution of one block to a fixed output entry. -/
def contribution (a b : Seq) (stride queryRow queryCol : Int)
    (depth : Nat) (row col inner : Int) : Int :=
  if row ≤ queryRow ∧ queryRow < row + (2 ^ depth : Nat) ∧
     col ≤ queryCol ∧ queryCol < col + (2 ^ depth : Nat)
  then innerProduct a b stride queryRow queryCol depth inner else 0

/-- Row-major coordinates are unique when both columns lie within the stride. -/
theorem address_injective (stride r q c d : Int)
    (hc : 0 ≤ c) (hcs : c < stride) (hd : 0 ≤ d) (hds : d < stride) :
    r * stride + c = q * stride + d ↔ r = q ∧ c = d := by
  constructor
  · intro same
    have hs : stride ≠ 0 := by omega
    have quotient := congrArg (fun x => x / stride) same
    simp only [Int.mul_add_ediv_right _ _ hs,
      Int.ediv_eq_zero_of_lt hc hcs, Int.ediv_eq_zero_of_lt hd hds, Int.add_zero] at quotient
    exact ⟨quotient, by rw [quotient] at same; omega⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The eight block contributions sum to the full block contribution. -/
theorem contribution_split (a b : Seq) (stride qr qc : Int) (depth : Nat) (r c k : Int) :
    let h : Int := (2 ^ depth : Nat)
    contribution a b stride qr qc depth r c k +
    contribution a b stride qr qc depth r c (k+h) +
    contribution a b stride qr qc depth r (c+h) k +
    contribution a b stride qr qc depth r (c+h) (k+h) +
    contribution a b stride qr qc depth (r+h) c k +
    contribution a b stride qr qc depth (r+h) c (k+h) +
    contribution a b stride qr qc depth (r+h) (c+h) k +
    contribution a b stride qr qc depth (r+h) (c+h) (k+h) =
    contribution a b stride qr qc (depth + 1) r c k := by
  have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
  simp only [contribution, Nat.pow_succ, Int.natCast_mul, innerProduct]
  split <;> split <;> split <;> split <;> split <;> simp_all <;> omega



@[simp] theorem blockEffect_store_other (depth : Nat) (heap : Heap)
    (a b c other : SeqRef) (stride row col inner : Int) (hne : other ≠ c) :
    (blockEffect a b c stride depth heap row col inner).store other = heap.store other := by
  funext index
  exact blockEffect_read_other depth heap a b c other stride row col inner index hne

/-- Every individual output cell equals its old value plus the block's dot product.
    The statement permits aliasing between the two inputs, but neither aliases c. -/
theorem blockEffect_correct (depth : Nat) (heap : Heap) (a b c : SeqRef)
    (stride row col inner qr qc : Int) (ha : a ≠ c) (hb : b ≠ c)
    (qc_nonnegative : 0 ≤ qc) (qc_bound : qc < stride)
    (col_nonnegative : 0 ≤ col) (col_bound : col + (2 ^ depth : Nat) ≤ stride) :
    (blockEffect a b c stride depth heap row col inner).read c (qr * stride + qc) =
      heap.read c (qr * stride + qc) +
        contribution (heap.store a) (heap.store b) stride qr qc depth row col inner := by
  induction depth generalizing heap row col inner with
  | zero =>
    have col_bound' : col < stride := by simpa using col_bound
    have same := address_injective stride qr row qc col qc_nonnegative qc_bound
      col_nonnegative col_bound'
    simp only [blockEffect, Heap.read, Heap.write, Heap.tick]
    simp only [contribution, innerProduct, Nat.pow_zero, Int.natCast_one]
    by_cases h : qr * stride + qc = row * stride + col
    · obtain ⟨rfl, rfl⟩ := same.mp h
      simp [show qr < qr + 1 by omega, show qc < qc + 1 by omega]
    · have outside : ¬(row ≤ qr ∧ qr < row + 1 ∧ col ≤ qc ∧ qc < col + 1) := by
        intro inside
        have rows : qr = row := by omega
        have cols : qc = col := by omega
        exact h (same.mpr ⟨rows, cols⟩)
      simp [h, outside]
  | succ depth ih =>
    have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
    have doubled : ((2 ^ (depth + 1) : Nat) : Int) = (2 ^ depth : Nat) + (2 ^ depth : Nat) := by
      simp [Nat.pow_succ, Int.natCast_mul]; omega
    rw [doubled] at col_bound
    simp only [blockEffect]
    simp (disch := omega) only [ih, blockEffect_store_other, Heap.tick_store, Heap.read_tick]
    have combined := contribution_split (heap.store a) (heap.store b) stride qr qc depth row col inner
    dsimp only at combined
    omega



/-- Conventional finite summation over indices 0, ..., n-1. -/
def finiteSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => finiteSum n f + f n

theorem finiteSum_append (n m : Nat) (f : Nat → Int) :
    finiteSum (n + m) f = finiteSum n f + finiteSum m (fun i => f (n+i)) := by
  induction m with
  | zero => simp [finiteSum]
  | succ m ih =>
    change finiteSum (n+m) f + f (n+m) = finiteSum n f +
      (finiteSum m (fun i => f (n+i)) + f (n+m))
    rw [ih]; omega

/-- The recursive specification is the usual finite dot product. -/
theorem innerProduct_eq_sum (a b : Seq) (stride qr qc : Int) (depth : Nat) (first : Int) :
    innerProduct a b stride qr qc depth first = finiteSum (2 ^ depth)
      (fun i => a (qr * stride + (first + i)) * b ((first + i) * stride + qc)) := by
  induction depth generalizing first with
  | zero => simp [innerProduct, finiteSum]
  | succ depth ih =>
    have twice : 2 ^ (depth+1) = 2 ^ depth + 2 ^ depth := by
      simp [Nat.pow_succ, Nat.mul_two]
    rw [innerProduct, ih, ih, twice, finiteSum_append]
    simp only [Int.natCast_add, Int.add_assoc]

/-- Ordinary n-by-n integer matrix multiplication, encoded in row-major order.
    Locations outside the result matrix are zero. -/
def matrixProduct (a b : Seq) (n : Nat) : Seq := fun index =>
  let row := index / (n : Int)
  let col := index % (n : Int)
  if 0 ≤ row ∧ row < (n : Int) then
    finiteSum n (fun inner => a (row * n + inner) * b (inner * n + col))
  else 0

theorem result_heap_correct (a b : Seq) (depth : Nat) :
    let initial := ((({} : Heap).allocate a).allocate b).allocate (fun _ => 0)
    (blockEffect 0 1 2 (2 ^ depth : Nat) depth initial 0 0 0).store 2 =
      matrixProduct a b (2 ^ depth) := by
  intro initial
  funext index
  have positive : 0 < ((2 ^ depth : Nat) : Int) := by
    exact_mod_cast Nat.pow_pos (show 0 < (2 : Nat) by decide)
  have col_nonnegative := Int.emod_nonneg index (Int.ne_of_gt positive)
  have col_bound := Int.emod_lt_of_pos index positive
  have correct := blockEffect_correct depth initial 0 1 2 (2 ^ depth : Nat) 0 0 0
    (index / (2 ^ depth : Nat)) (index % (2 ^ depth : Nat))
    (by decide) (by decide) col_nonnegative col_bound (by omega) (by simp)
  have address : index / (2 ^ depth : Nat) * (2 ^ depth : Nat) + index % (2 ^ depth : Nat) = index := by
    simpa [Int.mul_comm] using Int.mul_ediv_add_emod index ((2 ^ depth : Nat) : Int)
  rw [address] at correct
  simp only [contribution, Int.zero_add, col_nonnegative, col_bound, and_true] at correct
  simpa [initial, Heap.read, Heap.allocate, contribution, matrixProduct,
    col_nonnegative, col_bound, innerProduct_eq_sum] using correct

/-- Only the explicitly named multiplication and recursion counters change. -/
def costs (depth : Nat) : Clocks := fun name =>
  if name = "multiplications" then 8 ^ depth else
  if name = "calls" then callCount depth else 0

/-- Termination, full matrix correctness, and the exact scalar-multiplication
    count are certified by one execution of the generated algorithm. -/
theorem output_with_cost (a b : Seq) (depth : Nat) :
    matrix_recursive.ReturnsWithCost (a, b, (2 ^ depth : Nat))
      (matrixProduct a b (2 ^ depth)) (costs depth) := by
  let initial := (({} : Heap).allocate a).allocate b
  have execution := recursive_summary depth initial 0 1 (by simp [initial]) (by simp [initial])
  refine ⟨_, 2, ⟨execution.1, execution.2.root⟩, result_heap_correct a b depth, ?_⟩
  funext name
  simp [Heap.cost, blockEffect_clocks, costs, initial, matrix_recursive.load, Heap.allocate]



/-- Closed form for recursive-call overhead, avoiding truncated division. -/
theorem callCount_exact (depth : Nat) : 7 * callCount depth + 1 = 8 ^ (depth + 1) := by
  induction depth with
  | zero => decide
  | succ depth ih => simp only [callCount, Nat.pow_succ] at *; omega

/-- Both scalar work and recursive-call overhead are cubic in matrix dimension. -/
theorem runtime_bounds (depth : Nat) :
    costs depth "multiplications" = (2 ^ depth) ^ 3 ∧
    8 ^ depth ≤ costs depth "calls" ∧ costs depth "calls" ≤ 2 * 8 ^ depth := by
  have exactCalls := callCount_exact depth
  have positive : 0 < (8 ^ depth : Nat) := Nat.pow_pos (by decide)
  simp only [Nat.pow_succ] at exactCalls
  change 8 ^ depth = (2 ^ depth) ^ 3 ∧ 8 ^ depth ≤ callCount depth ∧ callCount depth ≤ 2 * 8 ^ depth
  exact ⟨multiplications_cubic depth, by omega, by omega⟩

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

-- Main result: Running time
/-- All completed outputs and all charged clocks have exactly this specification. -/
theorem output_with_cost_iff (a b result : Seq) (depth : Nat) (charged : Clocks) :
    matrix_recursive.ReturnsWithCost (a, b, (2 ^ depth : Nat)) result charged ↔
      result = matrixProduct a b (2 ^ depth) ∧ charged = costs depth := by
  constructor
  · rintro ⟨finalHeap, resultRef, execution, value, chargedEq⟩
    obtain ⟨correctHeap, correctRef, correctExecution, correctValue, correctCost⟩ :=
      output_with_cost a b depth
    have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
      execution.2 correctExecution.2
      (by intro next impossible; cases impossible)
      (by intro next impossible; cases impossible)
    cases same
    exact ⟨value.symm.trans correctValue, chargedEq.symm.trans correctCost⟩
  · rintro ⟨rfl, rfl⟩
    exact output_with_cost a b depth

-- Main result: Correctness
/-- Every completed execution returns the mathematical matrix product. -/
theorem every_output_correct (a b result : Seq) (depth : Nat)
    (run : matrix_recursive.Returns (a, b, (2 ^ depth : Nat)) result) :
    result = matrixProduct a b (2 ^ depth) := by
  obtain ⟨charged, completed⟩ := run.withCost
  exact ((output_with_cost_iff a b result depth charged).mp completed).1

end MatrixRecursiveAnalysis
