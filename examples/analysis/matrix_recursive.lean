import Algo2LeanLib.CallCost
import MatrixRecursiveGenerated
import Algo2LeanLib.MatrixHeap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanCore Algo2LeanGenerated
namespace MatrixRecursiveAnalysis

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- A matrix view records row identities and their validity; rows may alias. -/
def HasRows (heap : Heap) (matrix : CollectionRef) (rows : Int → SeqRef) : Prop :=
  seq_Seq_Int.valid heap matrix ∧ ∀ i,
    seq_Seq_Int.get heap matrix i = some (rows i) ∧ rows i < heap.nextRef

@[simp] theorem get_tick (heap : Heap) (m : CollectionRef) (i : Int) (clock : String) :
    seq_Seq_Int.get (heap.tick clock) m i = seq_Seq_Int.get heap m i := rfl

@[simp] theorem valid_tick (heap : Heap) (m : CollectionRef) (clock : String) :
    seq_Seq_Int.valid (heap.tick clock) m = seq_Seq_Int.valid heap m := rfl

@[simp] theorem hasRows_tick (heap : Heap) (m : CollectionRef) (rows : Int → SeqRef) (clock : String) :
    HasRows (heap.tick clock) m rows ↔ HasRows heap m rows := Iff.rfl

/-- A complete eight-way block multiplication, modeled by its heap effect. -/
def blockEffect (a b c : Int → SeqRef) (stride : Int) : Nat → Heap → Int → Int → Int → Heap
  | 0, heap, row, col, inner =>
    ((heap.tick "calls").tick "multiplications").write (c row) col
      (heap.read (c row) col + heap.read (a row) inner *
        heap.read (b inner) col)
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
    (a b c : Int → SeqRef) (stride row col inner : Int) :
    (blockEffect a b c stride depth heap row col inner).nextRef = heap.nextRef := by
  induction depth generalizing heap row col inner with
  | zero => rfl
  | succ depth ih => simp only [blockEffect, ih, Heap.tick_nextRef]

@[simp] theorem blockEffect_nextCollection (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (stride row col inner : Int) :
    (blockEffect a b c stride depth heap row col inner).nextCollection = heap.nextCollection := by
  induction depth generalizing heap row col inner with
  | zero => rfl
  | succ depth ih => simp only [blockEffect, ih]; rfl

@[simp] theorem blockEffect_collections (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (stride row col inner : Int) :
    (blockEffect a b c stride depth heap row col inner).collections = heap.collections := by
  induction depth generalizing heap row col inner with
  | zero => rfl
  | succ depth ih => simp only [blockEffect, ih]; rfl

@[simp] theorem hasRows_effect (depth : Nat) (heap : Heap)
    (a b c rows : Int → SeqRef) (stride row col inner : Int) (m : CollectionRef) :
    HasRows (blockEffect a b c stride depth heap row col inner) m rows ↔ HasRows heap m rows := by
  simp only [HasRows, SequenceType.get, SequenceType.valid, Heap.validSequence,
    Heap.sequenceType, Heap.readElement, blockEffect_collections, blockEffect_nextCollection,
    blockEffect_nextRef]

/-- Finite terminating execution of all eight calls, for every power-of-two size. -/
theorem block_summary (depth : Nat) (heap : Heap) (a b c : CollectionRef)
    (ar br cr : Int → SeqRef)
    (stride row col inner : Int)
    (ha : HasRows heap a ar) (hb : HasRows heap b br) (hc : HasRows heap c cr) :
    matrix_block.Call heap (a, b, c, stride, row, col, inner, (2 ^ depth : Nat))
      (blockEffect ar br cr stride depth heap row col inner) 0 := by
  induction depth generalizing heap row col inner with
  | zero =>
    refine ⟨⟨ha.1, hb.1, hc.1⟩, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_block_pc82 ..)
    apply Reaches.prepend (Step.matrix_block_pc81 ..)
    apply Reaches.prepend (Step.matrix_block_pc80_true _ _ _ (by simp))
    apply Reaches.prepend (Step.matrix_block_pc79 ..)
    apply Reaches.prepend (Step.matrix_block_pc78 _ _ _ (by simpa [hc.2 row |>.1, ha.2 row |>.1, hb.2 inner |>.1] using And.intro (And.intro (hc.2 row |>.2) (And.intro (ha.2 row |>.2) (hb.2 inner |>.2))) (hc.2 row |>.2)))
    apply Reaches.prepend (Step.matrix_block_pc77 ..)
    simpa only [blockEffect, get_tick, hc.2 row |>.1, ha.2 row |>.1, hb.2 inner |>.1,
      Option.getD_some, Heap.read_tick] using Reaches.single (Step.matrix_block_pc76 _ _ _)
  | succ depth ih =>
    have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
    have half_eq : Int.fdiv ((2 ^ (depth + 1) : Nat) : Int) 2 = ((2 ^ depth : Nat) : Int) := by
      simp [Nat.pow_succ, Int.fdiv_eq_ediv, Int.mul_ediv_cancel]
    refine ⟨⟨ha.1, hb.1, hc.1⟩, ?_⟩
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
    (a b c : Int → SeqRef) (other : SeqRef) (stride row col inner index : Int) (hne : ∀ r, other ≠ c r) :
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
    (a b c : Int → SeqRef) (stride row col inner : Int) (name : String) :
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


/-- The ordinary inner-product sum, split into equal halves. -/
def innerProduct (a b : Int → Seq) (stride queryRow queryCol : Int) : Nat → Int → Int
  | 0, first => a queryRow first * b first queryCol
  | depth + 1, first =>
    innerProduct a b stride queryRow queryCol depth first +
    innerProduct a b stride queryRow queryCol depth (first + (2 ^ depth : Nat))

/-- The contribution of one block to a fixed output entry. -/
def contribution (a b : Int → Seq) (stride queryRow queryCol : Int)
    (depth : Nat) (row col inner : Int) : Int :=
  if row ≤ queryRow ∧ queryRow < row + (2 ^ depth : Nat) ∧
     col ≤ queryCol ∧ queryCol < col + (2 ^ depth : Nat)
  then innerProduct a b stride queryRow queryCol depth inner else 0

/-- The eight block contributions sum to the full block contribution. -/
theorem contribution_split (a b : Int → Seq) (stride qr qc : Int) (depth : Nat) (r c k : Int) :
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
    (a b c : Int → SeqRef) (other : SeqRef) (stride row col inner : Int) (hne : ∀ r, other ≠ c r) :
    (blockEffect a b c stride depth heap row col inner).store other = heap.store other := by
  funext index
  exact blockEffect_read_other depth heap a b c other stride row col inner index hne

/-- Every individual output cell equals its old value plus the block's dot product.
    The statement permits aliasing between the two inputs, but neither aliases c. -/
theorem blockEffect_correct (depth : Nat) (heap : Heap) (a b c : Int → SeqRef)
    (stride row col inner qr qc : Int) (ha : ∀ i j, a i ≠ c j) (hb : ∀ i j, b i ≠ c j)
    (distinct : ∀ i j, 0 ≤ j → j < stride → (c i = c j ↔ i = j))
    (row_nonnegative : 0 ≤ row) (row_bound : row + (2 ^ depth : Nat) ≤ stride) :
    (blockEffect a b c stride depth heap row col inner).read (c qr) qc =
      heap.read (c qr) qc +
        contribution (fun i => heap.store (a i)) (fun i => heap.store (b i)) stride qr qc depth row col inner := by
  induction depth generalizing heap row col inner with
  | zero =>
    have row_bound' : row < stride := by
      simp only [Nat.pow_zero, Int.natCast_one] at row_bound
      omega
    have same := distinct qr row row_nonnegative row_bound'
    simp only [blockEffect, Heap.read, Heap.write, Heap.tick]
    simp only [contribution, innerProduct, Nat.pow_zero, Int.natCast_one]
    by_cases hr : qr = row <;> by_cases hc : qc = col
    · subst qr; subst qc
      simp [show row < row + 1 by omega, show col < col + 1 by omega]
    · subst qr
      simp [hc, show ¬(col ≤ qc ∧ qc < col + 1) by omega]
    · have refs : c qr ≠ c row := fun eq => hr (same.mp eq)
      simp [refs, show ¬(row ≤ qr ∧ qr < row + 1 ∧ col ≤ qc ∧ qc < col + 1) by omega]
    · have refs : c qr ≠ c row := fun eq => hr (same.mp eq)
      simp [refs, show ¬(row ≤ qr ∧ qr < row + 1 ∧ col ≤ qc ∧ qc < col + 1) by omega]
  | succ depth ih =>
    have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
    have doubled : ((2 ^ (depth + 1) : Nat) : Int) = (2 ^ depth : Nat) + (2 ^ depth : Nat) := by
      simp [Nat.pow_succ, Int.natCast_mul]; omega
    rw [doubled] at row_bound
    simp only [blockEffect]
    simp (disch := first | exact ha _ | exact hb _ | omega) only [ih, blockEffect_store_other, Heap.tick_store, Heap.read_tick]
    have combined := contribution_split (fun i => heap.store (a i)) (fun i => heap.store (b i)) stride qr qc depth row col inner
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
theorem innerProduct_eq_sum (a b : Int → Seq) (stride qr qc : Int) (depth : Nat) (first : Int) :
    innerProduct a b stride qr qc depth first = finiteSum (2 ^ depth)
      (fun i => a qr (first + i) * b (first + i) qc) := by
  induction depth generalizing first with
  | zero => simp [innerProduct, finiteSum]
  | succ depth ih =>
    have twice : 2 ^ (depth+1) = 2 ^ depth + 2 ^ depth := by
      simp [Nat.pow_succ, Nat.mul_two]
    rw [innerProduct, ih, ih, twice, finiteSum_append]
    simp only [Int.natCast_add, Int.add_assoc]


open Algo2LeanCore.MatrixHeap

/-- Allocate a separate zero row for each matrix index in the interval. -/
def initializeRows (heap : Heap) (c : CollectionRef) (first : Int) : Nat → Heap
  | 0 => heap
  | count + 1 => initializeRows
      (seq_Seq_Int.set (heap.allocate (fun _ => 0)) c first heap.nextRef) c (first + 1) count

@[simp] theorem initializeRows_nextRef (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat) :
    (initializeRows heap c first count).nextRef = heap.nextRef + count := by
  induction count generalizing heap first with
  | zero => simp [initializeRows]
  | succ count ih => simp only [initializeRows, ih, SequenceType.set, Heap.writeElement, Heap.allocate]; omega

@[simp] theorem initializeRows_nextCollection (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat) :
    (initializeRows heap c first count).nextCollection = heap.nextCollection := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeRows, ih, SequenceType.set, Heap.writeElement, Heap.allocate]

@[simp] theorem initializeRows_valid (heap : Heap) (c m : CollectionRef) (first : Int) (count : Nat) :
    seq_Seq_Int.valid (initializeRows heap c first count) m ↔ seq_Seq_Int.valid heap m := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp only [initializeRows, ih, SequenceType.valid_set]; rfl

 theorem initializeRows_store_old (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat)
    (r : SeqRef) (valid : r < heap.nextRef) :
    (initializeRows heap c first count).store r = heap.store r := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeRows, ih]
    · simp [SequenceType.set, Heap.writeElement, Heap.allocate, Nat.ne_of_lt valid]
    · simpa [SequenceType.set, Heap.writeElement] using Nat.lt_succ_of_lt valid

 theorem initializeRows_store_new (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat)
    (r : SeqRef) (lower : heap.nextRef ≤ r) (upper : r < heap.nextRef + count) :
    (initializeRows heap c first count).store r = fun _ => 0 := by
  induction count generalizing heap first with
  | zero => exact False.elim ((Nat.not_lt_of_ge lower) (by simpa using upper))
  | succ count ih =>
    rw [initializeRows]
    by_cases equal : r = heap.nextRef
    · rw [initializeRows_store_old]
      · simp [equal, SequenceType.set, Heap.writeElement, Heap.allocate]
      · simp [equal, SequenceType.set, Heap.writeElement]
    · exact ih _ _ (Nat.lt_of_le_of_ne lower (Ne.symm equal)) (by simpa [SequenceType.set, Heap.writeElement, Nat.add_assoc, Nat.add_comm count 1] using upper)

 theorem initializeRows_get_outside (heap : Heap) (c : CollectionRef) (first i : Int) (count : Nat)
    (outside : i < first ∨ first + count ≤ i) :
    seq_Seq_Int.get (initializeRows heap c first count) c i = seq_Seq_Int.get heap c i := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeRows, ih _ _ (by omega), SequenceType.get_set_other_index _ _ _ _ _ _ (by omega)]
    rfl

 theorem initializeRows_get_inside (heap : Heap) (c : CollectionRef) (first i : Int) (count : Nat)
    (valid : seq_Seq_Int.valid heap c) (lower : first ≤ i) (upper : i < first + count) :
    seq_Seq_Int.get (initializeRows heap c first count) c i = some (heap.nextRef + (i - first).toNat) := by
  induction count generalizing heap first with
  | zero => omega
  | succ count ih =>
    rw [initializeRows]
    by_cases equal : i = first
    · subst i
      rw [initializeRows_get_outside _ _ _ _ _ (Or.inl (by omega)), SequenceType.get_set_same _ _ _ _ _ (show seq_Seq_Int.valid (heap.allocate (fun _ => 0)) c from valid)]
      simp
    · rw [ih _ _ (by apply (seq_Seq_Int.valid_set _ _ _ _ _).mpr; exact valid)
        (by omega) (by omega)]
      congr 1
      simp only [SequenceType.set, Heap.writeElement, Heap.allocate]
      omega


theorem initializeRows_extends (before heap : Heap) (c : CollectionRef) (first : Int) (count : Nat)
    (extension : Extends before heap) (fresh : before.nextCollection ≤ c) :
    Extends before (initializeRows heap c first count) := by
  induction count generalizing heap first with
  | zero => exact extension
  | succ count ih =>
    exact ih _ _ ((extension.trans (extends_allocate heap _)).set c fresh first heap.nextRef)

@[simp] theorem initializeRows_clocks (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat) :
    (initializeRows heap c first count).clocks = heap.clocks := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp only [initializeRows, ih]; rfl

/-- The actual heap after allocating the default row and all n independent rows. -/
def zeroHeap (heap : Heap) (n : Nat) : Heap :=
  initializeRows (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 heap.nextCollection 0 n

def outputRows (heap : Heap) (n : Nat) (i : Int) : SeqRef :=
  if 0 ≤ i ∧ i < n then heap.nextRef + 1 + i.toNat else heap.nextRef

@[simp] theorem zeroHeap_clocks (heap : Heap) (n : Nat) : (zeroHeap heap n).clocks = heap.clocks := by
  simp only [zeroHeap, initializeRows_clocks]; rfl

theorem zeroHeap_extends (heap : Heap) (n : Nat) : Extends heap (zeroHeap heap n) := by
  apply initializeRows_extends
  · exact (extends_allocate heap _).trans (extends_const _ _)
  · exact Nat.le_refl _

theorem zeroHeap_rows (heap : Heap) (n : Nat) :
    HasRows (zeroHeap heap n) heap.nextCollection (outputRows heap n) := by
  refine ⟨?_, ?_⟩
  · simp only [zeroHeap, initializeRows_valid]
    exact seq_Seq_Int.valid_const _ _
  · intro i
    by_cases inside : 0 ≤ i ∧ i < n
    · constructor
      · rw [zeroHeap, initializeRows_get_inside (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 heap.nextCollection 0 i n (show seq_Seq_Int.valid _ heap.nextCollection from seq_Seq_Int.valid_const (heap.allocate (fun _ => 0)) heap.nextRef) inside.1 (by omega)]
        simp [outputRows, inside, SequenceType.const, SequenceType.create, Heap.createSequence, Heap.allocate]
      · simp only [outputRows, if_pos inside, zeroHeap, initializeRows_nextRef]
        change heap.nextRef + 1 + i.toNat < heap.nextRef + 1 + n
        omega
    · constructor
      · rw [zeroHeap, initializeRows_get_outside _ _ _ _ _ (by omega)]
        simp only [outputRows, if_neg inside]
        exact seq_Seq_Int.get_const (heap.allocate (fun _ => 0)) heap.nextRef i
      · simp only [outputRows, if_neg inside, zeroHeap, initializeRows_nextRef]
        change heap.nextRef < heap.nextRef + 1 + n
        omega

theorem zeroHeap_zero (heap : Heap) (n : Nat) (i : Int) :
    (zeroHeap heap n).store (outputRows heap n i) = fun _ => 0 := by
  by_cases inside : 0 ≤ i ∧ i < n
  · apply initializeRows_store_new
    · simp only [outputRows, if_pos inside]
      change heap.nextRef + 1 ≤ heap.nextRef + 1 + i.toNat
      omega
    · simp only [outputRows, if_pos inside]
      change heap.nextRef + 1 + i.toNat < heap.nextRef + 1 + n
      omega
  · simp only [zeroHeap, outputRows, if_neg inside]
    rw [initializeRows_store_old]
    · simp [SequenceType.const, SequenceType.create, Heap.createSequence, Heap.allocate]
    · change heap.nextRef < heap.nextRef + 1
      omega

theorem outputRows_distinct (heap : Heap) (n : Nat) (i j : Int) (low : 0 ≤ j) (high : j < n) :
    outputRows heap n i = outputRows heap n j ↔ i = j := by
  by_cases inside : 0 ≤ i ∧ i < n
  · simp only [outputRows, if_pos inside, if_pos (show 0 ≤ j ∧ j < (n : Int) from ⟨low, high⟩)]
    change (heap.nextRef + 1 + i.toNat = heap.nextRef + 1 + j.toNat ↔ i = j)
    omega
  · simp only [outputRows, if_neg inside, if_pos (show 0 ≤ j ∧ j < (n : Int) from ⟨low, high⟩)]
    change (heap.nextRef = heap.nextRef + 1 + j.toNat ↔ i = j)
    omega

theorem outputRows_fresh (heap : Heap) (n : Nat) (i : Int) : heap.nextRef ≤ outputRows heap n i := by
  unfold outputRows
  split <;> omega

def inputRows (heap : Heap) (matrix : CollectionRef) (i : Int) : SeqRef :=
  (seq_Seq_Int.get heap matrix i).getD 0

theorem stored_hasRows (heap : Heap) (matrix : CollectionRef) (values : Values)
    (stored : Stored heap matrix values) : HasRows heap matrix (inputRows heap matrix) := by
  refine ⟨stored.1, fun i => ?_⟩
  obtain ⟨row, read, valid, _⟩ := stored.2 i
  change seq_Seq_Int.get heap matrix i = some ((seq_Seq_Int.get heap matrix i).getD 0) ∧ _
  change seq_Seq_Int.get heap matrix i = some row at read
  simp [inputRows, read, valid]

theorem hasRows_mono (before after : Heap) (matrix : CollectionRef) (rs : Int → SeqRef)
    (view : HasRows before matrix rs) (extension : Extends before after) : HasRows after matrix rs := by
  refine ⟨extension.valid view.1, fun i => ?_⟩
  exact ⟨(extension.get view.1 i).trans (view.2 i).1, Nat.lt_of_lt_of_le (view.2 i).2 extension.nextRef⟩

theorem blockEffect_extends (depth : Nat) (before heap : Heap) (a b c : Int → SeqRef)
    (stride row col inner : Int) (extension : Extends before heap)
    (fresh : ∀ i, before.nextRef ≤ c i) :
    Extends before (blockEffect a b c stride depth heap row col inner) := by
  induction depth generalizing heap row col inner with
  | zero =>
    exact ((extension.trans (extends_tick heap "calls" 1)).trans
      (extends_tick (heap.tick "calls") "multiplications" 1)).write (c row) (fresh row) _ _
  | succ depth ih =>
    simp only [blockEffect]
    repeat apply ih
    exact extension.trans (extends_tick heap "calls" 1)

/-- Deterministic resulting heap, including the independent output rows. -/
def resultHeap (heap : Heap) (a b : CollectionRef) (depth : Nat) : Heap :=
  blockEffect (inputRows heap a) (inputRows heap b) (outputRows heap (2 ^ depth))
    (2 ^ depth : Nat) depth (zeroHeap heap (2 ^ depth)) 0 0 0


private def initializationState (heap : Heap) (a b : CollectionRef) (n : Int) : State_matrix_recursive :=
  { v0 := a, v1 := b, v2 := n, v3 := heap.nextCollection,
    t20 := heap.nextCollection, t21 := heap.nextRef }


/-- The public function allocates independent output rows and finishes all calls.
    Input matrices and arbitrary sharing among their rows are permitted. -/
theorem recursive_summary (depth : Nat) (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    matrix_recursive.Call heap (a, b, (2 ^ depth : Nat))
      (resultHeap heap a b depth) heap.nextCollection := by
  -- Internal loop derivations are local to this source-facing contract.
  /- The allocation loop terminates after exactly the remaining number of rows. -/
  have initializeRows_execution (count : Nat) (heap : Heap) (state : State_matrix_recursive)
      (stack : Stack) (valid : seq_Seq_Int.valid heap state.v3)
      (size : state.v2 = state.v4 + count) :
      ∃ finalState : State_matrix_recursive,
        Reaches Step (.active heap (.fn_matrix_recursive 13 state) stack)
          (.active (initializeRows heap state.v3 state.v4 count) (.fn_matrix_recursive 11 finalState) stack) ∧
        finalState.v0 = state.v0 ∧ finalState.v1 = state.v1 ∧ finalState.v2 = state.v2 ∧
        finalState.v3 = state.v3 := by
    induction count generalizing heap state with
    | zero =>
      refine ⟨{ state with t15 := decide (state.v4 < state.v2) }, ?_, rfl, rfl, rfl, rfl⟩
      apply Reaches.prepend (Step.matrix_recursive_pc13 ..)
      exact Reaches.single (Step.matrix_recursive_pc12_false _ _ _ (by change decide (state.v4 < state.v2) = false; simp only [decide_eq_false_iff_not]; omega))
    | succ count ih =>
      have tail := ih (seq_Seq_Int.set (heap.allocate (fun _ => 0)) state.v3 state.v4 heap.nextRef)
        { state with v4 := state.v4 + 1, t15 := true, t19 := 0, t16 := heap.nextRef, t18 := state.v3, t17 := state.v4 }
        (by apply (seq_Seq_Int.valid_set _ _ _ _ _).mpr; exact valid) (by dsimp only; omega)
      obtain ⟨finalState, execution, a, b, n, c⟩ := tail
      refine ⟨finalState, ?_, a, b, n, c⟩
      apply Reaches.prepend (Step.matrix_recursive_pc13 ..)
      apply Reaches.prepend (Step.matrix_recursive_pc12_true _ _ _ (by simp only [decide_eq_true_eq]; omega))
      apply Reaches.prepend (Step.matrix_recursive_pc19 ..)
      apply Reaches.prepend (Step.matrix_recursive_pc18 ..)
      apply Reaches.prepend (Step.matrix_recursive_pc17 ..)
      apply Reaches.prepend (Step.matrix_recursive_pc16 ..)
      apply Reaches.prepend (Step.matrix_recursive_pc15 _ _ _ valid)
      apply Reaches.prepend (Step.matrix_recursive_pc14 ..)
      simpa only [initializeRows, show decide (state.v4 < state.v2) = true by simp only [decide_eq_true_eq]; omega] using execution
  /- Complete the multiplication once the independent output rows exist. -/
  have recursive_finish (depth : Nat) (heap : Heap) (state : State_matrix_recursive)
      (ar br cr : Int → SeqRef) (stack : Stack)
      (ha : HasRows heap state.v0 ar) (hb : HasRows heap state.v1 br) (hc : HasRows heap state.v3 cr)
      (size : state.v2 = (2 ^ depth : Nat)) :
      Reaches Step (.active heap (.fn_matrix_recursive 11 state) stack)
        (resumeConfig (blockEffect ar br cr (2 ^ depth : Nat) depth heap 0 0 0)
          (.fn_matrix_recursive state.v3) stack) := by
    apply Reaches.prepend (Step.matrix_recursive_pc11 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc10 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc9 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc8 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc7 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc6 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc5 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc4 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc3 ..)
    simp only [size]
    apply Reaches.trans ((block_summary depth heap state.v0 state.v1 state.v3 ar br cr
      (2 ^ depth : Nat) 0 0 0 ha hb hc).2 _)
    apply Reaches.prepend (Step.matrix_recursive_pc2 ..)
    exact Reaches.single (Step.matrix_recursive_pc1 _ _ _ ((hasRows_effect _ _ _ _ _ _ _ _ _ _ _).mpr hc).1)
  have recursive_start (heap : Heap) (a b : CollectionRef) (n : Int) (stack : Stack) :
      Reaches Step (.active heap (.fn_matrix_recursive 24 { v0 := a, v1 := b, v2 := n }) stack)
        (.active (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1
          (.fn_matrix_recursive 13 (initializationState heap a b n)) stack) := by
    apply Reaches.prepend (Step.matrix_recursive_pc24 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc23 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc22 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc21 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc20 ..)
    exact Reaches.refl _
  have ext := zeroHeap_extends heap (2 ^ depth)
  have ar := hasRows_mono _ _ _ _ (stored_hasRows _ _ _ ha) ext
  have br := hasRows_mono _ _ _ _ (stored_hasRows _ _ _ hb) ext
  have cr := zeroHeap_rows heap (2 ^ depth)
  refine ⟨⟨ha.1, hb.1⟩, ?_⟩
  intro stack
  let state := initializationState heap a b (2 ^ depth : Nat)
  obtain ⟨finalState, allocationRun, h0, h1, h2, h3⟩ := initializeRows_execution (2 ^ depth)
    (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 state stack
    (show seq_Seq_Int.valid (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 state.v3 from
      by simpa only [state, initializationState, SequenceType.const, SequenceType.create,
        Heap.createSequence, Heap.allocate] using seq_Seq_Int.valid_const (heap.allocate (fun _ => 0)) heap.nextRef)
    (by simp [state, initializationState])
  dsimp only [state, initializationState] at h0 h1 h2 h3
  have completed := recursive_finish depth (zeroHeap heap (2 ^ depth)) finalState
    (inputRows heap a) (inputRows heap b) (outputRows heap (2 ^ depth)) stack
    (by simpa only [h0] using ar) (by simpa only [h1] using br) (by simpa only [h3] using cr) h2
  apply Reaches.trans (recursive_start heap a b (2 ^ depth : Nat) stack)
  apply Reaches.trans allocationRun
  simpa only [h3, resultHeap, state, initializationState, zeroHeap] using completed

/-- Conventional matrix product; cells outside its n-by-n extent are zero. -/
def matrixProduct (a b : Values) (n : Nat) : Values := fun row col =>
  if 0 ≤ row ∧ row < n ∧ 0 ≤ col ∧ col < n then
    finiteSum n (fun inner => a row inner * b inner col)
  else 0

theorem result_heap_correct (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    Stored (resultHeap heap a b depth) heap.nextCollection (matrixProduct av bv (2 ^ depth)) := by
  have old := zeroHeap_extends heap (2 ^ depth)
  have inputA := stored_hasRows heap a av ha
  have inputB := stored_hasRows heap b bv hb
  have sepA : ∀ i j, inputRows heap a i ≠ outputRows heap (2 ^ depth) j := by
    intro i j
    have lower := outputRows_fresh heap (2 ^ depth) j
    have upper := (inputA.2 i).2
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le upper lower)
  have sepB : ∀ i j, inputRows heap b i ≠ outputRows heap (2 ^ depth) j := by
    intro i j
    have lower := outputRows_fresh heap (2 ^ depth) j
    have upper := (inputB.2 i).2
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le upper lower)
  have inputsA : (fun i => (zeroHeap heap (2 ^ depth)).store (inputRows heap a i)) = av := by
    funext i j
    rw [old.store _ (inputA.2 i).2]
    exact ha.read i j
  have inputsB : (fun i => (zeroHeap heap (2 ^ depth)).store (inputRows heap b i)) = bv := by
    funext i j
    rw [old.store _ (inputB.2 i).2]
    exact hb.read i j
  have view := (hasRows_effect depth (zeroHeap heap (2 ^ depth)) (inputRows heap a) (inputRows heap b)
    (outputRows heap (2 ^ depth)) (outputRows heap (2 ^ depth)) (2 ^ depth : Nat) 0 0 0 heap.nextCollection).mpr
      (zeroHeap_rows heap (2 ^ depth))
  refine ⟨view.1, fun row => ⟨outputRows heap (2 ^ depth) row, (view.2 row).1, (view.2 row).2, ?_⟩⟩
  funext col
  have correct := blockEffect_correct depth (zeroHeap heap (2 ^ depth)) (inputRows heap a) (inputRows heap b)
    (outputRows heap (2 ^ depth)) (2 ^ depth : Nat) 0 0 0 row col sepA sepB
    (outputRows_distinct heap (2 ^ depth)) (by omega) (by simp)
  rw [inputsA, inputsB] at correct
  simpa only [resultHeap, Heap.read, zeroHeap_zero, contribution, Int.zero_add,
    matrixProduct, innerProduct_eq_sum] using correct

/-- All preexisting rows, outer arrays and objects are unchanged. -/
theorem result_heap_preserves (heap : Heap) (a b : CollectionRef) (depth : Nat) :
    Extends heap (resultHeap heap a b depth) :=
  blockEffect_extends depth heap _ _ _ _ _ _ _ _ (zeroHeap_extends heap (2 ^ depth))
    (outputRows_fresh heap (2 ^ depth))

/-- Only the named multiplication and recursion counters change. -/
def costs (depth : Nat) : Clocks := fun name =>
  if name = "multiplications" then 8 ^ depth else
  if name = "calls" then callCount depth else 0

/-- Termination, full matrix correctness, preservation, and exact costs. -/
theorem output_with_cost (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    matrix_recursive.ReturnsWithCost (heap, a, b, (2 ^ depth : Nat))
      (resultHeap heap a b depth, heap.nextCollection) (costs depth) := by
  refine ⟨(recursive_summary depth heap a b av bv ha hb).run, ?_⟩
  funext clock
  simp [Heap.cost, resultHeap, costs, matrix_recursive.load]

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
/-- For n = 2^depth, every execution charges n³ scalar multiplications and between
    n³ and 2n³ recursive calls: at most 3n³ total units, hence Θ(n³) counted work.
    This theorem fixes the output heap and exact clocks; `runtime_bounds` bounds
    those clocks. Array allocations, loop bookkeeping, and integer bit complexity
    are excluded. -/
theorem output_with_cost_iff (heap finalHeap : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (charged : Clocks)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    matrix_recursive.ReturnsWithCost (heap, a, b, (2 ^ depth : Nat)) (finalHeap, result) charged ↔
      finalHeap = resultHeap heap a b depth ∧ result = heap.nextCollection ∧ charged = costs depth := by
  have canonical := output_with_cost heap a b av bv depth ha hb
  constructor
  · intro completed
    have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
      completed.1.2 canonical.1.2
      (by intro next impossible; cases impossible)
      (by intro next impossible; cases impossible)
    have heaps : finalHeap = resultHeap heap a b depth := by cases same; rfl
    have refs : result = heap.nextCollection := by cases same; rfl
    refine ⟨heaps, refs, ?_⟩
    exact completed.2.symm.trans (heaps ▸ canonical.2)
  · rintro ⟨rfl, rfl, rfl⟩
    exact canonical

-- Main result: Correctness
/-- The returned array of rows contains the usual matrix product. All preexisting
    input rows and outer arrays survive unchanged, including any shared rows. -/
theorem every_output_correct (heap finalHeap : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (ha : Stored heap a av) (hb : Stored heap b bv)
    (run : matrix_recursive.Returns (heap, a, b, (2 ^ depth : Nat)) (finalHeap, result)) :
    Stored finalHeap result (matrixProduct av bv (2 ^ depth)) ∧ Extends heap finalHeap := by
  obtain ⟨charged, completed⟩ := run.withCost
  obtain ⟨rfl, rfl, _⟩ := (output_with_cost_iff heap finalHeap a b result av bv depth charged ha hb).mp completed
  exact ⟨result_heap_correct heap a b av bv depth ha hb, result_heap_preserves heap a b depth⟩

/-- Well-formed matrices always terminate for positive power-of-two dimensions. -/
theorem terminates (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    ∃ finalHeap result, matrix_recursive.Returns (heap, a, b, (2 ^ depth : Nat)) (finalHeap, result) :=
  ⟨_, _, (output_with_cost heap a b av bv depth ha hb).returns⟩

/-- Completed outputs have fresh, valid, pairwise distinct rows in the finite
    square. Shared input rows impose no separation requirement on the inputs. -/
theorem every_execution_fresh_rows (heap finalHeap : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (ha : Stored heap a av) (hb : Stored heap b bv)
    (run : matrix_recursive.Returns (heap, a, b, (2 ^ depth : Nat)) (finalHeap, result)) :
    result = heap.nextCollection ∧
    (∀ i : Int, 0 ≤ i → i < (2 ^ depth : Nat) →
      seq_Seq_Int.get finalHeap result i = some (heap.nextRef + 1 + i.toNat) ∧
      heap.nextRef < heap.nextRef + 1 + i.toNat ∧ heap.nextRef + 1 + i.toNat < finalHeap.nextRef) ∧
    (∀ i j : Int, 0 ≤ i → i < (2 ^ depth : Nat) → 0 ≤ j → j < (2 ^ depth : Nat) →
      (seq_Seq_Int.get finalHeap result i = seq_Seq_Int.get finalHeap result j ↔ i = j)) := by
  obtain ⟨charged, completed⟩ := run.withCost
  obtain ⟨rfl, rfl, _⟩ := (output_with_cost_iff heap finalHeap a b result av bv depth charged ha hb).mp completed
  have view : HasRows (resultHeap heap a b depth) heap.nextCollection (outputRows heap (2 ^ depth)) :=
    (hasRows_effect _ _ _ _ _ _ _ _ _ _ _).mpr (zeroHeap_rows heap (2 ^ depth))
  refine ⟨rfl, ?_, ?_⟩
  · intro i nonneg bound
    have found := view.2 i
    simp only [outputRows, if_pos (show 0 ≤ i ∧ i < ((2 ^ depth : Nat) : Int) from ⟨nonneg, bound⟩)] at found
    exact ⟨found.1, by omega, found.2⟩
  · intro i j ni bi nj bj
    rw [(view.2 i).1, (view.2 j).1]
    simpa only [Option.some.injEq] using outputRows_distinct heap (2 ^ depth) i j nj bj


/-- Scalar products and every recursion node both contribute one unit. -/
def runtime (charged : Clocks) : Nat := charged "multiplications" + charged "calls"

-- Main result: Correctness and running time
/-- For n=2^depth, a finite eight-way recursive call returns the matrix product,
preserves old storage, and creates distinct fresh output rows. Its exact clocks
give matching cubic bounds for the same call, with uniform upper constant 3. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          matrix_recursive.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
          Stored after result (matrixProduct av bv (2^depth)) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result (2^depth) ∧
          heap.Increments after (MatrixRecursiveAnalysis.costs depth) ∧
          ((2^depth : Nat)^3) ≤ runtime (heap.cost after) ∧
          runtime (heap.cost after) ≤ C*((2^depth : Nat)^3) := by
  refine ⟨3, by decide, ?_⟩
  intro heap a b av bv depth sa sb
  let after := MatrixRecursiveAnalysis.resultHeap heap a b depth
  have call := MatrixRecursiveAnalysis.recursive_summary depth heap a b av bv sa sb
  have stored := MatrixRecursiveAnalysis.result_heap_correct heap a b av bv depth sa sb
  have frame := MatrixRecursiveAnalysis.result_heap_preserves heap a b depth
  have fresh := MatrixRecursiveAnalysis.every_execution_fresh_rows
    heap after a b heap.nextCollection av bv depth sa sb call.run
  have increments : heap.Increments after (MatrixRecursiveAnalysis.costs depth) := by
    intro clock
    simp [after, MatrixRecursiveAnalysis.resultHeap, MatrixRecursiveAnalysis.costs]
  refine ⟨after, heap.nextCollection, call, ?_, frame, Nat.le_refl _, stored.1.1, ?_, increments, ?_⟩
  · exact stored
  · constructor
    · intro i hi
      obtain ⟨read, lower, upper⟩ := fresh.2.1 (i : Int) (by omega) (by omega)
      exact ⟨heap.nextRef + 1 + i, read, Nat.le_of_lt lower, upper⟩
    · intro i j hi hj equal
      have same := (fresh.2.2 (i : Int) (j : Int) (by omega) (by omega) (by omega) (by omega)).mp equal
      exact_mod_cast same
  · rw [increments.cost]
    have bounds := MatrixRecursiveAnalysis.runtime_bounds depth
    have powers := MatrixRecursiveAnalysis.multiplications_cubic depth
    unfold runtime
    omega


/-- Reusable total call contract: product, preserved caller storage, a fresh
outer array with independent finite rows, and exact increments of every clock. -/
theorem call (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result,
      matrix_recursive.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
      Stored after result (matrixProduct av bv (2^depth)) ∧ Extends heap after ∧
      heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
      FreshRows heap after result (2^depth) ∧ heap.Increments after (costs depth) := by
  obtain ⟨_, _, contract⟩ := correctness_and_running_time
  obtain ⟨after, result, execution, stored, frame, lower, upper, fresh, charged, _⟩ :=
    contract heap a b av bv depth sa sb
  exact ⟨after, result, execution, stored, frame, lower, upper, fresh, charged⟩

end MatrixRecursiveAnalysis
