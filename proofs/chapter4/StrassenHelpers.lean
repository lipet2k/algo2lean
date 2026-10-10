import MatrixStrassenGeneratedPoints

open Algo2LeanCore Algo2LeanGenerated
namespace MatrixStrassenHelpers

def quadrantIndex (n h row col index : Int) : Int :=
  (row + Int.fdiv index h) * n + col + Int.fmod index h

def quadrantStep (heap : Heap) (a c : SeqRef) (n h row col index : Int) : Heap :=
  (heap.write c index (heap.read a (quadrantIndex n h row col index))).tick "copied_cells"

def quadrantRun : Nat → Heap → SeqRef → SeqRef → Int → Int → Int → Int → Int → Heap
  | 0, heap, _, _, _, _, _, _, _ => heap
  | count + 1, heap, a, c, n, h, row, col, index =>
      quadrantRun count (quadrantStep heap a c n h row col index) a c n h row col (index + 1)

@[simp] theorem quadrantRun_nextRef (count : Nat) (heap : Heap)
    (a c : SeqRef) (n h row col index : Int) :
    (quadrantRun count heap a c n h row col index).nextRef = heap.nextRef := by
  induction count generalizing heap index with
  | zero => rfl
  | succ count ih => simp [quadrantRun, ih, quadrantStep, Heap.write]

def AtQuadrant (state : Configuration) (heap : Heap) (a c : SeqRef)
    (n h row col index : Int) : Prop :=
  matrix_quadrant.At.loop state ∧ state.heap = heap ∧
  matrix_quadrant.Local.a state = some a ∧ matrix_quadrant.Local.c state = some c ∧
  matrix_quadrant.Local.n state = some n ∧ matrix_quadrant.Local.h state = some h ∧
  matrix_quadrant.Local.row state = some row ∧ matrix_quadrant.Local.column state = some col ∧
  matrix_quadrant.Local.i state = some index

theorem quadrant_exit (state : Configuration) (heap : Heap) (a c : SeqRef)
    (n h row col index : Int) (located : AtQuadrant state heap a c n h row col index)
    (allocated : c < heap.nextRef) (finished : h*h ≤ index) :
    matrix_quadrant.CallFrom state heap c := by
  obtain ⟨named, sameHeap, sameA, sameC, sameN, sameH, sameRow, sameCol, sameIndex⟩ := located
  unfold matrix_quadrant.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_quadrant.Local.a, matrix_quadrant.Local.c, matrix_quadrant.Local.n,
    matrix_quadrant.Local.h, matrix_quadrant.Local.row, matrix_quadrant.Local.column,
    matrix_quadrant.Local.i] at sameA sameC sameN sameH sameRow sameCol sameIndex
  intro caller
  apply Reaches.prepend (Step.matrix_quadrant_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_quadrant_pc3_false _ _ _
    (by simp [sameIndex, sameH]; omega))
  apply Reaches.prepend (Step.matrix_quadrant_pc2 _ _ _)
  simpa [sameC] using Reaches.single
    (Step.matrix_quadrant_pc1 heap _ caller (by simpa [sameC] using allocated))

theorem quadrant_step (state : Configuration) (heap finalHeap : Heap) (a c : SeqRef)
    (n h row col index : Int) (located : AtQuadrant state heap a c n h row col index)
    (validA : a < heap.nextRef) (validC : c < heap.nextRef) (nonzero : h ≠ 0)
    (unfinished : index < h*h)
    (continuation : ∀ next, AtQuadrant next (quadrantStep heap a c n h row col index)
      a c n h row col (index + 1) → matrix_quadrant.CallFrom next finalHeap c) :
    matrix_quadrant.CallFrom state finalHeap c := by
  obtain ⟨named, sameHeap, sameA, sameC, sameN, sameH, sameRow, sameCol, sameIndex⟩ := located
  unfold matrix_quadrant.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_quadrant.Local.a, matrix_quadrant.Local.c, matrix_quadrant.Local.n,
    matrix_quadrant.Local.h, matrix_quadrant.Local.row, matrix_quadrant.Local.column,
    matrix_quadrant.Local.i] at sameA sameC sameN sameH sameRow sameCol sameIndex
  have resume : ∀ next : State_matrix_quadrant,
      next.v0 = a → next.v5 = c → next.v1 = n → next.v2 = h →
      next.v3 = row → next.v4 = col → next.v6 = index + 1 →
      Summary Step (quadrantStep heap a c n h row col index) (.fn_matrix_quadrant 4 next)
        finalHeap (.fn_matrix_quadrant c) := by
    intro next aEq cEq nEq hEq rowEq colEq indexEq
    exact continuation (.active (quadrantStep heap a c n h row col index) (.fn_matrix_quadrant 4 next) [])
      (by simp [AtQuadrant, matrix_quadrant.At.loop, Config.heap, matrix_quadrant.Local.a,
        matrix_quadrant.Local.c, matrix_quadrant.Local.n, matrix_quadrant.Local.h,
        matrix_quadrant.Local.row, matrix_quadrant.Local.column, matrix_quadrant.Local.i,
        aEq, cEq, nEq, hEq, rowEq, colEq, indexEq])
  intro caller
  apply Reaches.prepend (Step.matrix_quadrant_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_quadrant_pc3_true _ _ _
    (by simp [sameIndex, sameH, unfinished]))
  apply Reaches.prepend (Step.matrix_quadrant_pc7 _ _ _
    (by simp [sameA, sameC, sameH, validA, validC, nonzero]))
  apply Reaches.prepend (Step.matrix_quadrant_pc6 _ _ _)
  apply Reaches.prepend (Step.matrix_quadrant_pc5 _ _ _)
  simp only [sameA, sameC, sameN, sameH, sameRow, sameCol, sameIndex]
  apply resume _ _ _ _ _ _ _ _ caller <;> rfl

theorem quadrant_remaining (count : Nat) (heap : Heap) (a c : SeqRef) (n h row col index : Int)
    (validA : a < heap.nextRef) (validC : c < heap.nextRef) (nonzero : h ≠ 0)
    (bound : index + (count : Int) = h*h) :
    ∀ state, AtQuadrant state heap a c n h row col index →
      matrix_quadrant.CallFrom state (quadrantRun count heap a c n h row col index) c := by
  induction count generalizing heap index with
  | zero =>
    intro state located
    exact quadrant_exit state heap a c n h row col index located validC (by omega)
  | succ count ih =>
    intro state located
    apply quadrant_step state heap _ a c n h row col index located validA validC nonzero (by omega)
    intro next nextLocated
    exact ih (quadrantStep heap a c n h row col index) (index + 1) validA validC
      (by omega) next nextLocated

theorem quadrant_summary (heap : Heap) (a : SeqRef) (n row col : Int) (h : Nat)
    (validA : a < heap.nextRef) (positive : 0 < h) :
    matrix_quadrant.Call heap (a, n, (h : Int), row, col)
      (quadrantRun (h*h) (heap.allocate (fun _ => 0)) a heap.nextRef n h row col 0) heap.nextRef := by
  refine ⟨validA, ?_⟩
  intro caller
  apply Reaches.prepend (Step.matrix_quadrant_pc11 _ _ _)
  apply Reaches.prepend (Step.matrix_quadrant_pc10 _ _ _)
  apply Reaches.prepend (Step.matrix_quadrant_pc9 _ _ _)
  apply Reaches.prepend (Step.matrix_quadrant_pc8 _ _ _)
  have remaining := quadrant_remaining (h*h) (heap.allocate (fun _ => 0)) a heap.nextRef n h row col 0
    (Nat.lt_trans validA (Nat.lt_succ_self _)) (Nat.lt_succ_self _) (by omega) (by simp [Int.natCast_mul])
  exact remaining (.active (heap.allocate (fun _ => 0)) (.fn_matrix_quadrant 4
      { v0 := a, v1 := n, v2 := h, v3 := row, v4 := col, v5 := heap.nextRef, t9 := heap.nextRef }) [])
    (by simp [AtQuadrant, matrix_quadrant.At.loop, Config.heap, matrix_quadrant.Local.a,
      matrix_quadrant.Local.c, matrix_quadrant.Local.n, matrix_quadrant.Local.h,
      matrix_quadrant.Local.row, matrix_quadrant.Local.column, matrix_quadrant.Local.i]) caller

@[simp] theorem quadrantRun_old (count : Nat) (heap : Heap) (a c other : SeqRef)
    (n h row col first index : Int) (different : other ≠ c) :
    (quadrantRun count heap a c n h row col first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [quadrantRun]
    rw [ih]
    simp [quadrantStep, Heap.read, Heap.write, different]

theorem quadrantRun_value (count : Nat) (heap : Heap) (a c : SeqRef)
    (n h row col first index : Int) (separate : a ≠ c) :
    (quadrantRun count heap a c n h row col first).read c index =
      if first ≤ index ∧ index < first + (count : Int)
      then heap.read a (quadrantIndex n h row col index) else heap.read c index := by
  induction count generalizing heap first with
  | zero =>
    simp only [quadrantRun, Int.natCast_zero, Int.add_zero]
    rw [if_neg (by omega)]
  | succ count ih =>
    simp only [quadrantRun]
    rw [ih]
    simp only [quadrantStep, Heap.read, Heap.write, Heap.tick,
      separate, false_and, ↓reduceIte, true_and]
    grind

theorem quadrantRun_clocks (count : Nat) (heap : Heap) (a c : SeqRef)
    (n h row col first : Int) (name : String) :
    (quadrantRun count heap a c n h row col first).clocks name =
      heap.clocks name + if name = "copied_cells" then count else 0 := by
  induction count generalizing heap first with
  | zero => simp [quadrantRun]
  | succ count ih =>
    simp only [quadrantRun, ih, quadrantStep, Heap.tick, Heap.write]
    by_cases same : name = "copied_cells" <;> simp [same, Nat.add_assoc, Nat.add_comm 1 count]

/-- A fresh quadrant has the exact copied entries, preserves every old sequence,
    and charges one copy per entry. The input stride and offsets are arbitrary. -/
theorem quadrant_correct (heap : Heap) (a : SeqRef) (n row col : Int) (h : Nat)
    (validA : a < heap.nextRef) (positive : 0 < h) :
    ∃ after result, matrix_quadrant.Call heap (a, n, (h : Int), row, col) after result ∧
      result < after.nextRef ∧ heap.nextRef ≤ after.nextRef ∧
      (∀ old index, old < heap.nextRef → after.read old index = heap.read old index) ∧
      (∀ index, after.read result index = if 0 ≤ index ∧ index < (h*h : Nat)
        then heap.read a (quadrantIndex n h row col index) else 0) ∧
      Heap.cost heap after = Clocks.single "copied_cells" (h*h) := by
  refine ⟨_, heap.nextRef, quadrant_summary heap a n row col h validA positive, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro old index valid
    rw [quadrantRun_old (h*h) _ a heap.nextRef old n h row col 0 index (Nat.ne_of_lt valid)]
    exact Heap.read_allocate_old heap _ old index valid
  · intro index
    rw [quadrantRun_value (h*h) _ a heap.nextRef n h row col 0 index (Nat.ne_of_lt validA)]
    simp [validA]
  · funext name
    simp only [Heap.cost, quadrantRun_clocks, Heap.allocate_clocks, Nat.add_sub_cancel_left,
      Clocks.single]


/-- Four writes of one source entry into the four output quadrants. -/
def joinStep (heap : Heap) (a b c d result : SeqRef) (h index : Int) : Heap :=
  let row := Int.fdiv index h
  let col := Int.fmod index h
  let first := heap.write result (row*(2*h)+col) (heap.read a index)
  let second := first.write result (row*(2*h)+col+h) (first.read b index)
  let third := second.write result ((row+h)*(2*h)+col) (second.read c index)
  (third.write result ((row+h)*(2*h)+col+h) (third.read d index)).tick "copied_cells" 4

def joinRun : Nat → Heap → SeqRef → SeqRef → SeqRef → SeqRef → SeqRef → Int → Int → Heap
  | 0, heap, _, _, _, _, _, _, _ => heap
  | count+1, heap, a, b, c, d, result, h, index =>
      joinRun count (joinStep heap a b c d result h index) a b c d result h (index+1)

@[simp] theorem joinRun_nextRef (count : Nat) (heap : Heap)
    (a b c d result : SeqRef) (h index : Int) :
    (joinRun count heap a b c d result h index).nextRef = heap.nextRef := by
  induction count generalizing heap index with
  | zero => rfl
  | succ count ih => simp [joinRun, ih, joinStep, Heap.write]

def AtJoin (state : Configuration) (heap : Heap) (a b c d result : SeqRef)
    (h index : Int) : Prop :=
  matrix_join.At.loop state ∧ state.heap = heap ∧
  matrix_join.Local.a state = some a ∧ matrix_join.Local.b state = some b ∧
  matrix_join.Local.c state = some c ∧ matrix_join.Local.d state = some d ∧
  matrix_join.Local.result state = some result ∧ matrix_join.Local.h state = some h ∧
  matrix_join.Local.i state = some index

theorem join_exit (state : Configuration) (heap : Heap) (a b c d result : SeqRef)
    (h index : Int) (located : AtJoin state heap a b c d result h index)
    (allocated : result < heap.nextRef) (finished : h*h ≤ index) :
    matrix_join.CallFrom state heap result := by
  obtain ⟨named, sameHeap, sameA, sameB, sameC, sameD, sameResult, sameH, sameIndex⟩ := located
  unfold matrix_join.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_join.Local.a, matrix_join.Local.b, matrix_join.Local.c, matrix_join.Local.d,
    matrix_join.Local.result, matrix_join.Local.h, matrix_join.Local.i]
    at sameA sameB sameC sameD sameResult sameH sameIndex
  intro caller
  apply Reaches.prepend (Step.matrix_join_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_join_pc3_false _ _ _
    (by simp [sameIndex, sameH]; omega))
  apply Reaches.prepend (Step.matrix_join_pc2 _ _ _)
  simpa [sameResult] using Reaches.single
    (Step.matrix_join_pc1 heap _ caller (by simpa [sameResult] using allocated))

theorem join_step (state : Configuration) (heap finalHeap : Heap) (a b c d result : SeqRef)
    (h index : Int) (located : AtJoin state heap a b c d result h index)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (validD : d < heap.nextRef) (validResult : result < heap.nextRef) (nonzero : h ≠ 0)
    (unfinished : index < h*h)
    (continuation : ∀ next, AtJoin next (joinStep heap a b c d result h index)
      a b c d result h (index+1) → matrix_join.CallFrom next finalHeap result) :
    matrix_join.CallFrom state finalHeap result := by
  obtain ⟨named, sameHeap, sameA, sameB, sameC, sameD, sameResult, sameH, sameIndex⟩ := located
  unfold matrix_join.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_join.Local.a, matrix_join.Local.b, matrix_join.Local.c, matrix_join.Local.d,
    matrix_join.Local.result, matrix_join.Local.h, matrix_join.Local.i]
    at sameA sameB sameC sameD sameResult sameH sameIndex
  have resume : ∀ next : State_matrix_join,
      next.v0 = a → next.v1 = b → next.v2 = c → next.v3 = d → next.v5 = result →
      next.v4 = h → next.v6 = index+1 →
      Summary Step (joinStep heap a b c d result h index) (.fn_matrix_join 4 next)
        finalHeap (.fn_matrix_join result) := by
    intro next aEq bEq cEq dEq resultEq hEq indexEq
    exact continuation (.active (joinStep heap a b c d result h index) (.fn_matrix_join 4 next) [])
      (by simp [AtJoin, matrix_join.At.loop, Config.heap, matrix_join.Local.a,
        matrix_join.Local.b, matrix_join.Local.c, matrix_join.Local.d,
        matrix_join.Local.result, matrix_join.Local.h, matrix_join.Local.i,
        aEq, bEq, cEq, dEq, resultEq, hEq, indexEq])
  intro caller
  apply Reaches.prepend (Step.matrix_join_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_join_pc3_true _ _ _
    (by simp [sameIndex, sameH, unfinished]))
  apply Reaches.prepend (Step.matrix_join_pc12 _ _ _ (by simpa [sameH] using nonzero))
  apply Reaches.prepend (Step.matrix_join_pc11 _ _ _ (by simpa [sameH] using nonzero))
  apply Reaches.prepend (Step.matrix_join_pc10 _ _ _
    (by simp [sameA, sameResult, validA, validResult]))
  apply Reaches.prepend (Step.matrix_join_pc9 _ _ _
    (by simp [sameB, sameResult, validB, validResult, Heap.write]))
  apply Reaches.prepend (Step.matrix_join_pc8 _ _ _
    (by simp [sameC, sameResult, validC, validResult, Heap.write]))
  apply Reaches.prepend (Step.matrix_join_pc7 _ _ _
    (by simp [sameD, sameResult, validD, validResult, Heap.write]))
  apply Reaches.prepend (Step.matrix_join_pc6 _ _ _)
  apply Reaches.prepend (Step.matrix_join_pc5 _ _ _)
  simp only [sameA, sameB, sameC, sameD, sameResult, sameH, sameIndex]
  apply resume _ _ _ _ _ _ _ _ caller <;> rfl

theorem join_remaining (count : Nat) (heap : Heap) (a b c d result : SeqRef) (h index : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (validD : d < heap.nextRef) (validResult : result < heap.nextRef) (nonzero : h ≠ 0)
    (bound : index + (count : Int) = h*h) :
    ∀ state, AtJoin state heap a b c d result h index →
      matrix_join.CallFrom state (joinRun count heap a b c d result h index) result := by
  induction count generalizing heap index with
  | zero =>
    intro state located
    exact join_exit state heap a b c d result h index located validResult (by omega)
  | succ count ih =>
    intro state located
    apply join_step state heap _ a b c d result h index located validA validB validC validD validResult nonzero (by omega)
    intro next nextLocated
    exact ih (joinStep heap a b c d result h index) (index+1) validA validB validC validD validResult
      (by omega) next nextLocated

theorem join_summary (heap : Heap) (a b c d : SeqRef) (h : Nat)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (validD : d < heap.nextRef) (positive : 0 < h) :
    matrix_join.Call heap (a,b,c,d,(h:Int))
      (joinRun (h*h) (heap.allocate (fun _ => 0)) a b c d heap.nextRef h 0) heap.nextRef := by
  refine ⟨⟨validA, validB, validC, validD⟩, ?_⟩
  intro caller
  apply Reaches.prepend (Step.matrix_join_pc16 _ _ _)
  apply Reaches.prepend (Step.matrix_join_pc15 _ _ _)
  apply Reaches.prepend (Step.matrix_join_pc14 _ _ _)
  apply Reaches.prepend (Step.matrix_join_pc13 _ _ _)
  have remaining := join_remaining (h*h) (heap.allocate (fun _ => 0)) a b c d heap.nextRef h 0
    (Nat.lt_trans validA (Nat.lt_succ_self _)) (Nat.lt_trans validB (Nat.lt_succ_self _))
    (Nat.lt_trans validC (Nat.lt_succ_self _)) (Nat.lt_trans validD (Nat.lt_succ_self _))
    (Nat.lt_succ_self _) (by omega) (by simp [Int.natCast_mul])
  exact remaining (.active (heap.allocate (fun _ => 0)) (.fn_matrix_join 4
      { v0 := a, v1 := b, v2 := c, v3 := d, v4 := h, v5 := heap.nextRef, t11 := heap.nextRef }) [])
    (by simp [AtJoin, matrix_join.At.loop, Config.heap, matrix_join.Local.a,
      matrix_join.Local.b, matrix_join.Local.c, matrix_join.Local.d,
      matrix_join.Local.result, matrix_join.Local.h, matrix_join.Local.i]) caller

@[simp] theorem joinRun_old (count : Nat) (heap : Heap) (a b c d result other : SeqRef)
    (h first index : Int) (different : other ≠ result) :
    (joinRun count heap a b c d result h first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [joinRun]
    rw [ih]
    simp [joinStep, Heap.read, Heap.write, different]

theorem joinRun_clocks (count : Nat) (heap : Heap) (a b c d result : SeqRef)
    (h first : Int) (name : String) :
    (joinRun count heap a b c d result h first).clocks name =
      heap.clocks name + if name = "copied_cells" then 4*count else 0 := by
  induction count generalizing heap first with
  | zero => simp [joinRun]
  | succ count ih =>
    simp only [joinRun, ih, joinStep, Heap.tick, Heap.write]
    by_cases same : name = "copied_cells" <;> simp [same, Nat.mul_add] <;> omega


/-- Address in one selected quadrant of the joined matrix. -/
def joinIndex (h : Int) (lower right : Bool) (index : Int) : Int :=
  (Int.fdiv index h + if lower then h else 0) * (2*h) +
    (Int.fmod index h + if right then h else 0)

theorem offset_injective (h x y : Int) (left right : Bool)
    (xLow : 0 ≤ x) (xHigh : x < h) (yLow : 0 ≤ y) (yHigh : y < h) :
    x + (if left then h else 0) = y + (if right then h else 0) ↔
      x = y ∧ left = right := by
  cases left <;> cases right <;> simp <;> omega

theorem joinIndex_injective (h i j : Int) (r c s d : Bool)
    (positive : 0 < h) (iLow : 0 ≤ i) (iHigh : i < h*h)
    (jLow : 0 ≤ j) (jHigh : j < h*h) :
    joinIndex h r c i = joinIndex h s d j ↔ i = j ∧ r = s ∧ c = d := by
  have qiLow := Int.ediv_nonneg iLow (Int.le_of_lt positive)
  have qjLow := Int.ediv_nonneg jLow (Int.le_of_lt positive)
  have qiHigh := Int.ediv_lt_of_lt_mul positive iHigh
  have qjHigh := Int.ediv_lt_of_lt_mul positive jHigh
  have riLow := Int.emod_nonneg i (Int.ne_of_gt positive)
  have rjLow := Int.emod_nonneg j (Int.ne_of_gt positive)
  have riHigh := Int.emod_lt_of_pos i positive
  have rjHigh := Int.emod_lt_of_pos j positive
  have colILow : 0 ≤ i % h + (if c then h else 0) := by cases c <;> simp <;> omega
  have colIHigh : i % h + (if c then h else 0) < 2*h := by cases c <;> simp <;> omega
  have colJLow : 0 ≤ j % h + (if d then h else 0) := by cases d <;> simp <;> omega
  have colJHigh : j % h + (if d then h else 0) < 2*h := by cases d <;> simp <;> omega
  simp only [joinIndex, Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt positive),
    Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt positive)]
  constructor
  · intro same
    have rows := congrArg (fun x => x / (2*h)) same
    simp only [Int.mul_add_ediv_right _ _ (by omega : 2*h ≠ 0),
      Int.ediv_eq_zero_of_lt colILow colIHigh, Int.ediv_eq_zero_of_lt colJLow colJHigh,
      Int.add_zero] at rows
    have cols : i % h + (if c then h else 0) = j % h + (if d then h else 0) := by
      rw [rows] at same
      omega
    obtain ⟨sameQuotient, sameR⟩ := (offset_injective h _ _ r s qiLow qiHigh qjLow qjHigh).mp rows
    obtain ⟨sameRemainder, sameC⟩ := (offset_injective h _ _ c d riLow riHigh rjLow rjHigh).mp cols
    refine ⟨?_, sameR, sameC⟩
    have reconstructI := Int.mul_ediv_add_emod i h
    have reconstructJ := Int.mul_ediv_add_emod j h
    rw [sameQuotient, sameRemainder] at reconstructI
    omega
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def selectQuadrant (a b c d : SeqRef) (lower right : Bool) : SeqRef :=
  if lower then (if right then d else c) else (if right then b else a)

theorem joinStep_value (heap : Heap) (a b c d result : SeqRef) (h first index : Int)
    (lower right : Bool) (positive : 0 < h)
    (firstLow : 0 ≤ first) (firstHigh : first < h*h)
    (indexLow : 0 ≤ index) (indexHigh : index < h*h)
    (_separateA : a ≠ result) (separateB : b ≠ result)
    (separateC : c ≠ result) (separateD : d ≠ result) :
    (joinStep heap a b c d result h first).read result (joinIndex h lower right index) =
      if index = first then heap.read (selectQuadrant a b c d lower right) index
      else heap.read result (joinIndex h lower right index) := by
  have nw := joinIndex_injective h index first lower right false false positive indexLow indexHigh firstLow firstHigh
  have ne := joinIndex_injective h index first lower right false true positive indexLow indexHigh firstLow firstHigh
  have sw := joinIndex_injective h index first lower right true false positive indexLow indexHigh firstLow firstHigh
  have se := joinIndex_injective h index first lower right true true positive indexLow indexHigh firstLow firstHigh
  simp only [joinIndex, Bool.false_eq_true, ↓reduceIte,
    Int.add_zero] at nw ne sw se
  cases lower <;> cases right <;>
    simp_all [joinStep, Heap.read, Heap.write, joinIndex, selectQuadrant, Int.add_assoc]


@[simp] theorem joinStep_old (heap : Heap) (a b c d result other : SeqRef)
    (h first index : Int) (different : other ≠ result) :
    (joinStep heap a b c d result h first).read other index = heap.read other index := by
  simp [joinStep, Heap.read, Heap.write, different]

theorem joinRun_value (count : Nat) (heap : Heap) (a b c d result : SeqRef)
    (h first index : Int) (lower right : Bool) (positive : 0 < h)
    (firstLow : 0 ≤ first) (lastBound : first + (count:Int) ≤ h*h)
    (indexLow : 0 ≤ index) (indexHigh : index < h*h)
    (separateA : a ≠ result) (separateB : b ≠ result)
    (separateC : c ≠ result) (separateD : d ≠ result) :
    (joinRun count heap a b c d result h first).read result (joinIndex h lower right index) =
      if first ≤ index ∧ index < first + (count:Int)
      then heap.read (selectQuadrant a b c d lower right) index
      else heap.read result (joinIndex h lower right index) := by
  induction count generalizing heap first with
  | zero =>
    simp only [joinRun, Int.natCast_zero, Int.add_zero]
    rw [if_neg (by omega)]
  | succ count ih =>
    simp only [joinRun]
    rw [ih _ (first+1) (by omega) (by omega)]
    have different : selectQuadrant a b c d lower right ≠ result := by
      cases lower <;> cases right <;> assumption
    rw [joinStep_old _ _ _ _ _ _ _ _ _ _ different]
    rw [joinStep_value heap a b c d result h first index lower right positive firstLow
      (by omega) indexLow indexHigh separateA separateB separateC separateD]
    grind

/-- Joining four quadrants terminates and installs each source cell at exactly
one output position. It preserves old arrays and charges four copies per cell. -/
theorem join_correct (heap : Heap) (a b c d : SeqRef) (h : Nat)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (validD : d < heap.nextRef) (positive : 0 < h) :
    ∃ after result, matrix_join.Call heap (a,b,c,d,(h:Int)) after result ∧
      result < after.nextRef ∧ heap.nextRef ≤ after.nextRef ∧
      (∀ old index, old < heap.nextRef → after.read old index = heap.read old index) ∧
      (∀ (index : Int) lower right, 0 ≤ index → index < (h*h:Nat) →
        after.read result (joinIndex h lower right index) =
          heap.read (selectQuadrant a b c d lower right) index) ∧
      Heap.cost heap after = Clocks.single "copied_cells" (4*(h*h)) := by
  refine ⟨_, heap.nextRef, join_summary heap a b c d h validA validB validC validD positive,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro old index valid
    rw [joinRun_old (h*h) _ a b c d heap.nextRef old h 0 index (Nat.ne_of_lt valid)]
    exact Heap.read_allocate_old heap _ old index valid
  · intro index lower right low high
    rw [joinRun_value (h*h) _ a b c d heap.nextRef h 0 index lower right (by omega)
      (by omega) (by simp [Int.natCast_mul]) low (by simpa only [Int.natCast_mul] using high)
      (Nat.ne_of_lt validA) (Nat.ne_of_lt validB) (Nat.ne_of_lt validC) (Nat.ne_of_lt validD)]
    simp only [Int.zero_add]
    rw [if_pos (show 0 ≤ index ∧ index < (h*h:Nat) from ⟨low, high⟩)]
    have valid : selectQuadrant a b c d lower right < heap.nextRef := by
      cases lower <;> cases right <;> assumption
    exact Heap.read_allocate_old heap _ _ index valid
  · funext name
    simp only [Heap.cost, joinRun_clocks, Heap.allocate_clocks, Nat.add_sub_cancel_left,
      Clocks.single]


/-- The elementary bound used for every row-major output address. -/
theorem rowMajor_bounds (width row col : Int) (positive : 0 < width)
    (rowLow : 0 ≤ row) (rowHigh : row < width)
    (colLow : 0 ≤ col) (colHigh : col < width) :
    0 ≤ row*width+col ∧ row*width+col < width*width := by
  have rowProductLow := Int.mul_nonneg rowLow (Int.le_of_lt positive)
  have rowProductHigh := Int.mul_le_mul_of_nonneg_right
    (show row+1 ≤ width by omega) (Int.le_of_lt positive)
  simp only [Int.add_mul, Int.one_mul] at rowProductHigh
  omega

theorem joinIndex_bounds (h index : Int) (lower right : Bool)
    (positive : 0 < h) (low : 0 ≤ index) (high : index < h*h) :
    0 ≤ joinIndex h lower right index ∧ joinIndex h lower right index < (2*h)*(2*h) := by
  have qLow := Int.ediv_nonneg low (Int.le_of_lt positive)
  have qHigh := Int.ediv_lt_of_lt_mul positive high
  have rLow := Int.emod_nonneg index (Int.ne_of_gt positive)
  have rHigh := Int.emod_lt_of_pos index positive
  simp only [joinIndex, Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt positive),
    Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt positive)]
  apply rowMajor_bounds (2*h) _ _ (by omega)
  all_goals cases lower <;> cases right <;> simp <;> omega

theorem joinStep_outside (heap : Heap) (a b c d result : SeqRef) (h first index : Int)
    (positive : 0 < h) (firstLow : 0 ≤ first) (firstHigh : first < h*h)
    (outside : index < 0 ∨ (2*h)*(2*h) ≤ index) :
    (joinStep heap a b c d result h first).read result index = heap.read result index := by
  have nwBounds := joinIndex_bounds h first false false positive firstLow firstHigh
  have neBounds := joinIndex_bounds h first false true positive firstLow firstHigh
  have swBounds := joinIndex_bounds h first true false positive firstLow firstHigh
  have seBounds := joinIndex_bounds h first true true positive firstLow firstHigh
  have nw : index ≠ joinIndex h false false first := by omega
  have ne : index ≠ joinIndex h false true first := by omega
  have sw : index ≠ joinIndex h true false first := by omega
  have se : index ≠ joinIndex h true true first := by omega
  simp only [joinIndex, Bool.false_eq_true, ↓reduceIte, Int.add_zero] at nw ne sw se
  simp [joinStep, Heap.read, Heap.write, nw, ne, sw, se, Int.add_assoc] at *

theorem joinRun_outside (count : Nat) (heap : Heap) (a b c d result : SeqRef)
    (h first index : Int) (positive : 0 < h) (firstLow : 0 ≤ first)
    (lastBound : first+(count:Int) ≤ h*h) (outside : index < 0 ∨ (2*h)*(2*h) ≤ index) :
    (joinRun count heap a b c d result h first).read result index = heap.read result index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [joinRun, ih _ (first+1) (by omega) (by omega)]
    exact joinStep_outside heap a b c d result h first index positive firstLow (by omega) outside

/-- The inverse local index and quadrant choices for a joined matrix. -/
def joinedLocal (h index : Int) : Int :=
  let row := index / (2*h)
  let col := index % (2*h)
  (row - if row < h then 0 else h)*h + col - if col < h then 0 else h

def joinedValues (h : Int) (a b c d : Seq) : Seq := fun index =>
  let row := index / (2*h)
  let col := index % (2*h)
  if 0 ≤ index ∧ index < (2*h)*(2*h) then
    if row < h then (if col < h then a (row*h+col) else b (row*h+(col-h)))
    else (if col < h then c ((row-h)*h+col) else d ((row-h)*h+(col-h)))
  else 0

theorem localCoordinate_bounds (h x : Int) (_positive : 0 < h)
    (low : 0 ≤ x) (high : x < 2*h) :
    0 ≤ x - (if x < h then 0 else h) ∧ x - (if x < h then 0 else h) < h := by
  by_cases small : x < h <;> simp [small] <;> omega

theorem joinIndex_cell (h row col : Int) (lower right : Bool)
    (positive : 0 < h) (colLow : 0 ≤ col) (colHigh : col < h) :
    joinIndex h lower right (row*h+col) =
      (row + if lower then h else 0)*(2*h) + (col + if right then h else 0) := by
  simp only [joinIndex, Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt positive),
    Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt positive),
    Int.mul_add_ediv_right _ _ (Int.ne_of_gt positive), Int.ediv_eq_zero_of_lt colLow colHigh,
    Int.add_emod, Int.mul_emod, Int.emod_self, Int.mul_zero, Int.zero_emod,
    Int.zero_add, Int.emod_eq_of_lt colLow colHigh, Int.add_zero]

theorem join_inverse (h index : Int) (positive : 0 < h)
    (low : 0 ≤ index) (high : index < (2*h)*(2*h)) :
    0 ≤ joinedLocal h index ∧ joinedLocal h index < h*h ∧
    joinIndex h (decide (h ≤ index/(2*h))) (decide (h ≤ index%(2*h))) (joinedLocal h index) = index := by
  have widthPositive : 0 < 2*h := by omega
  have qLow := Int.ediv_nonneg low (Int.le_of_lt widthPositive)
  have qHigh := Int.ediv_lt_of_lt_mul widthPositive high
  have rLow := Int.emod_nonneg index (Int.ne_of_gt widthPositive)
  have rHigh := Int.emod_lt_of_pos index widthPositive
  have rowBounds := localCoordinate_bounds h _ positive qLow qHigh
  have colBounds := localCoordinate_bounds h _ positive rLow rHigh
  have localBounds := rowMajor_bounds h _ _ positive rowBounds.1 rowBounds.2 colBounds.1 colBounds.2
  have reform : joinedLocal h index =
      (index/(2*h) - if index/(2*h)<h then 0 else h)*h +
      (index%(2*h) - if index%(2*h)<h then 0 else h) := by simp [joinedLocal]; omega
  rw [reform]
  refine ⟨localBounds.1, localBounds.2, ?_⟩
  rw [joinIndex_cell _ _ _ _ _ positive colBounds.1 colBounds.2]
  have row : (index/(2*h) - if index/(2*h)<h then 0 else h) +
      (if decide (h ≤ index/(2*h)) then h else 0) = index/(2*h) := by
    by_cases small : index/(2*h)<h
    · simp [small, show ¬h ≤ index/(2*h) from by omega]
    · simp [small, show h ≤ index/(2*h) from by omega]
  have col : (index%(2*h) - if index%(2*h)<h then 0 else h) +
      (if decide (h ≤ index%(2*h)) then h else 0) = index%(2*h) := by
    by_cases small : index%(2*h)<h
    · simp [small, show ¬h ≤ index%(2*h) from by omega]
    · simp [small, show h ≤ index%(2*h) from by omega]
  rw [row, col]
  exact Int.ediv_mul_add_emod index (2*h)


/-- Correct quadrant entries and zero outside the square characterize the
entire infinite mathematical result sequence. -/
theorem join_contents_all (h : Int) (a b c d result : Seq) (positive : 0 < h)
    (inside : ∀ index lower right, 0 ≤ index → index < h*h →
      result (joinIndex h lower right index) =
        (if lower then (if right then d else c) else (if right then b else a)) index)
    (outside : ∀ index, index < 0 ∨ (2*h)*(2*h) ≤ index → result index = 0) :
    result = joinedValues h a b c d := by
  funext index
  by_cases valid : 0 ≤ index ∧ index < (2*h)*(2*h)
  · obtain ⟨localLow, localHigh, inverse⟩ := join_inverse h index positive valid.1 valid.2
    have found := inside (joinedLocal h index) (decide (h ≤ index/(2*h)))
      (decide (h ≤ index%(2*h))) localLow localHigh
    rw [inverse] at found
    simp only [joinedValues, if_pos valid]
    by_cases row : index/(2*h)<h <;> by_cases col : index%(2*h)<h
    · have nr : ¬h ≤ index/(2*h) := by omega
      have nc : ¬h ≤ index%(2*h) := by omega
      simpa [joinedLocal, row, col, nr, nc, Int.add_sub_assoc] using found
    · have nr : ¬h ≤ index/(2*h) := by omega
      have nc : h ≤ index%(2*h) := by omega
      simpa [joinedLocal, row, col, nr, nc, Int.add_sub_assoc] using found
    · have nr : h ≤ index/(2*h) := by omega
      have nc : ¬h ≤ index%(2*h) := by omega
      simpa [joinedLocal, row, col, nr, nc, Int.add_sub_assoc] using found
    · have nr : h ≤ index/(2*h) := by omega
      have nc : h ≤ index%(2*h) := by omega
      simpa [joinedLocal, row, col, nr, nc, Int.add_sub_assoc] using found
  · have absent := outside index (by omega)
    simp [joinedValues, valid, absent]

/-- Full source contract, including the exact fresh reference and zero values
outside the finite matrix. -/
theorem join_correct_full_fresh (heap : Heap) (a b c d : SeqRef) (h : Nat)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (validD : d < heap.nextRef) (positive : 0 < h) :
    ∃ after result, matrix_join.Call heap (a,b,c,d,(h:Int)) after result ∧
      result < after.nextRef ∧ heap.nextRef ≤ after.nextRef ∧
      (∀ old index, old < heap.nextRef → after.read old index = heap.read old index) ∧
      after.read result = joinedValues h (heap.read a) (heap.read b) (heap.read c) (heap.read d) ∧
      Heap.cost heap after = Clocks.single "copied_cells" (4*(h*h)) ∧ result = heap.nextRef := by
  refine ⟨_, heap.nextRef, join_summary heap a b c d h validA validB validC validD positive,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp
  · simp
  · intro old index valid
    rw [joinRun_old (h*h) _ a b c d heap.nextRef old h 0 index (Nat.ne_of_lt valid)]
    exact Heap.read_allocate_old heap _ old index valid
  · apply join_contents_all _ _ _ _ _ _ (by omega)
    · intro index lower right low high
      rw [joinRun_value (h*h) _ a b c d heap.nextRef h 0 index lower right (by omega)
        (by omega) (by simp [Int.natCast_mul]) low high
        (Nat.ne_of_lt validA) (Nat.ne_of_lt validB) (Nat.ne_of_lt validC) (Nat.ne_of_lt validD)]
      simp only [Int.zero_add]
      rw [if_pos (show 0 ≤ index ∧ index < (h*h:Nat) from ⟨low, by simpa only [Int.natCast_mul] using high⟩)]
      have valid : selectQuadrant a b c d lower right < heap.nextRef := by
        cases lower <;> cases right <;> assumption
      rw [Heap.read_allocate_old _ _ _ _ valid]
      cases lower <;> cases right <;> rfl
    · intro index outside
      rw [joinRun_outside (h*h) _ a b c d heap.nextRef h 0 index (by omega)
        (by omega) (by simp [Int.natCast_mul]) outside]
      simp
  · funext name
    simp only [Heap.cost, joinRun_clocks, Heap.allocate_clocks, Nat.add_sub_cancel_left,
      Clocks.single]

/-- Full source contract, including the zero values outside the finite matrix. -/
theorem join_correct_full (heap : Heap) (a b c d : SeqRef) (h : Nat)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (validD : d < heap.nextRef) (positive : 0 < h) :
    ∃ after result, matrix_join.Call heap (a,b,c,d,(h:Int)) after result ∧
      result < after.nextRef ∧ heap.nextRef ≤ after.nextRef ∧
      (∀ old index, old < heap.nextRef → after.read old index = heap.read old index) ∧
      after.read result = joinedValues h (heap.read a) (heap.read b) (heap.read c) (heap.read d) ∧
      Heap.cost heap after = Clocks.single "copied_cells" (4*(h*h)) := by
  obtain ⟨after, result, run, allocated, monotone, frame, contents, cost, _⟩ :=
    join_correct_full_fresh heap a b c d h validA validB validC validD positive
  exact ⟨after, result, run, allocated, monotone, frame, contents, cost⟩

end MatrixStrassenHelpers
