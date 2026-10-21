import MatrixStrassenGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanCore Algo2LeanGenerated

namespace MatrixStrassenAnalysis

/- The source loops first receive reusable heap summaries. Matrix algebra and
   the recursive correctness argument then use these summaries as interfaces. -/

def linearStep (heap : Heap) (a b c : SeqRef) (sign index : Int) : Heap :=
  (heap.write c index (heap.read a index + sign * heap.read b index)).tick "linear_cells"

def linearRun : Nat → Heap → SeqRef → SeqRef → SeqRef → Int → Int → Heap
  | 0, heap, _, _, _, _, _ => heap
  | count + 1, heap, a, b, c, sign, index =>
      linearRun count (linearStep heap a b c sign index) a b c sign (index + 1)

@[simp] theorem linearRun_nextRef (count : Nat) (heap : Heap)
    (a b c : SeqRef) (sign index : Int) :
    (linearRun count heap a b c sign index).nextRef = heap.nextRef := by
  induction count generalizing heap index with
  | zero => rfl
  | succ count ih => simp [linearRun, ih, linearStep, Heap.write]

def AtLinear (state : Configuration) (heap : Heap) (a b c : SeqRef)
    (bound sign index : Int) : Prop :=
  matrix_linear_row.At.loop state ∧ state.heap = heap ∧
  matrix_linear_row.Local.a state = some a ∧ matrix_linear_row.Local.b state = some b ∧
  matrix_linear_row.Local.c state = some c ∧ matrix_linear_row.Local.count state = some bound ∧
  matrix_linear_row.Local.sign state = some sign ∧ matrix_linear_row.Local.i state = some index

theorem linear_exit (state : Configuration) (heap : Heap) (a b c : SeqRef)
    (bound sign index : Int) (located : AtLinear state heap a b c bound sign index)
    (allocated : c < heap.nextRef) (finished : bound ≤ index) :
    matrix_linear_row.CallFrom state heap c := by
  obtain ⟨named, sameHeap, sameA, sameB, sameC, sameBound, sameSign, sameIndex⟩ := located
  unfold matrix_linear_row.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_linear_row.Local.a, matrix_linear_row.Local.b, matrix_linear_row.Local.c,
    matrix_linear_row.Local.count, matrix_linear_row.Local.sign, matrix_linear_row.Local.i]
    at sameA sameB sameC sameBound sameSign sameIndex
  intro caller
  apply Reaches.prepend (Step.matrix_linear_row_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc3_false _ _ _
    (by simp [sameIndex, sameBound]; omega))
  apply Reaches.prepend (Step.matrix_linear_row_pc2 _ _ _)
  simpa [sameC] using Reaches.single
    (Step.matrix_linear_row_pc1 heap _ caller (by simpa [sameC] using allocated))

theorem linear_step (state : Configuration) (heap finalHeap : Heap) (a b c : SeqRef)
    (bound sign index : Int) (located : AtLinear state heap a b c bound sign index)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (unfinished : index < bound)
    (continuation : ∀ next, AtLinear next (linearStep heap a b c sign index)
      a b c bound sign (index + 1) → matrix_linear_row.CallFrom next finalHeap c) :
    matrix_linear_row.CallFrom state finalHeap c := by
  obtain ⟨named, sameHeap, sameA, sameB, sameC, sameBound, sameSign, sameIndex⟩ := located
  unfold matrix_linear_row.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_linear_row.Local.a, matrix_linear_row.Local.b, matrix_linear_row.Local.c,
    matrix_linear_row.Local.count, matrix_linear_row.Local.sign, matrix_linear_row.Local.i]
    at sameA sameB sameC sameBound sameSign sameIndex
  have resume : ∀ next : State_matrix_linear_row,
      next.v0 = a → next.v1 = b → next.v4 = c → next.v2 = bound →
      next.v3 = sign → next.v5 = index + 1 →
      Summary Step (linearStep heap a b c sign index) (.fn_matrix_linear_row 4 next)
        finalHeap (.fn_matrix_linear_row c) := by
    intro next aEq bEq cEq boundEq signEq indexEq
    exact continuation (.active (linearStep heap a b c sign index) (.fn_matrix_linear_row 4 next) [])
      (by simp [AtLinear, matrix_linear_row.At.loop, Config.heap, matrix_linear_row.Local.a,
        matrix_linear_row.Local.b, matrix_linear_row.Local.c, matrix_linear_row.Local.count,
        matrix_linear_row.Local.sign, matrix_linear_row.Local.i, aEq, bEq, cEq, boundEq, signEq, indexEq])
  intro caller
  apply Reaches.prepend (Step.matrix_linear_row_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc3_true _ _ _
    (by simp [sameIndex, sameBound, unfinished]))
  apply Reaches.prepend (Step.matrix_linear_row_pc7 _ _ _
    (by simp [sameA, sameB, sameC, validA, validB, validC]))
  apply Reaches.prepend (Step.matrix_linear_row_pc6 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc5 _ _ _)
  simp only [sameA, sameB, sameC, sameSign, sameIndex]
  apply resume _ _ _ _ _ _ _ caller <;> simp [sameBound]

theorem linear_remaining (count : Nat) (heap : Heap) (a b c : SeqRef) (sign index : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef) :
    ∀ state, AtLinear state heap a b c (index + (count : Int)) sign index →
      matrix_linear_row.CallFrom state (linearRun count heap a b c sign index) c := by
  induction count generalizing heap index with
  | zero =>
    intro state located
    exact linear_exit state heap a b c _ sign index located validC (by simp)
  | succ count ih =>
    intro state located
    apply linear_step state heap _ a b c _ sign index located validA validB validC (by omega)
    intro next nextLocated
    have equalBound : index + ((count + 1 : Nat) : Int) = index + 1 + (count : Int) := by omega
    rw [equalBound] at nextLocated
    exact ih (linearStep heap a b c sign index) (index + 1) validA validB validC next nextLocated

theorem linear_summary (heap : Heap) (a b : SeqRef) (count : Nat) (sign : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) :
    matrix_linear_row.Call heap (a, b, (count : Int), sign)
      (linearRun count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0) heap.nextRef := by
  refine ⟨⟨validA, validB⟩, ?_⟩
  intro caller
  apply Reaches.prepend (Step.matrix_linear_row_pc11 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc10 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc9 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc8 _ _ _)
  have remaining := linear_remaining count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0
    (Nat.lt_trans validA (Nat.lt_succ_self _)) (Nat.lt_trans validB (Nat.lt_succ_self _)) (Nat.lt_succ_self _)
  exact remaining (.active (heap.allocate (fun _ => 0)) (.fn_matrix_linear_row 4
      { v0 := a, v1 := b, v2 := count, v3 := sign, v4 := heap.nextRef, t8 := heap.nextRef }) [])
    (by simp [AtLinear, matrix_linear_row.At.loop, Config.heap, matrix_linear_row.Local.a,
      matrix_linear_row.Local.b, matrix_linear_row.Local.c, matrix_linear_row.Local.count,
      matrix_linear_row.Local.sign, matrix_linear_row.Local.i]) caller

@[simp] theorem linearRun_old (count : Nat) (heap : Heap) (a b c other : SeqRef)
    (sign first index : Int) (different : other ≠ c) :
    (linearRun count heap a b c sign first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [linearRun]
    rw [ih]
    simp [linearStep, Heap.read, Heap.write, different]

theorem linearRun_value (count : Nat) (heap : Heap) (a b c : SeqRef)
    (sign first index : Int) (separateA : a ≠ c) (separateB : b ≠ c) :
    (linearRun count heap a b c sign first).read c index =
      if first ≤ index ∧ index < first + (count : Int)
      then heap.read a index + sign * heap.read b index else heap.read c index := by
  induction count generalizing heap first with
  | zero =>
    simp only [linearRun, Int.natCast_zero, Int.add_zero]
    rw [if_neg (by omega)]
  | succ count ih =>
    simp only [linearRun]
    rw [ih]
    simp only [linearStep, Heap.read, Heap.write, Heap.tick,
      separateA, separateB, false_and, ↓reduceIte, true_and]
    grind

theorem linearRun_clocks (count : Nat) (heap : Heap) (a b c : SeqRef)
    (sign first : Int) (name : String) :
    (linearRun count heap a b c sign first).clocks name =
      heap.clocks name + if name = "linear_cells" then count else 0 := by
  induction count generalizing heap first with
  | zero => simp [linearRun]
  | succ count ih =>
    simp only [linearRun, ih, linearStep, Heap.tick, Heap.write]
    by_cases same : name = "linear_cells" <;> simp [same, Nat.add_assoc, Nat.add_comm 1 count]

/-- Every finite vector addition terminates, has the expected entries, preserves
    the original arrays, and charges exactly one linear-cell unit per entry. -/
theorem linear_correct (heap : Heap) (a b : SeqRef) (count : Nat) (sign : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) :
    ∃ after result, matrix_linear_row.Call heap (a, b, (count : Int), sign) after result ∧
      result < after.nextRef ∧ heap.nextRef ≤ after.nextRef ∧
      (∀ old index, old < heap.nextRef → after.read old index = heap.read old index) ∧
      (∀ index, after.read result index = if 0 ≤ index ∧ index < (count : Int)
        then heap.read a index + sign * heap.read b index else 0) ∧
      Heap.cost heap after = Clocks.single "linear_cells" count := by
  refine ⟨_, heap.nextRef, linear_summary heap a b count sign validA validB, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro old index valid
    rw [linearRun_old count _ a b heap.nextRef old sign 0 index (Nat.ne_of_lt valid)]
    exact Heap.read_allocate_old heap _ old index valid
  · intro index
    rw [linearRun_value count _ a b heap.nextRef sign 0 index (Nat.ne_of_lt validA) (Nat.ne_of_lt validB)]
    simp [validA, validB]
  · funext name
    simp only [Heap.cost, linearRun_clocks, Heap.allocate_clocks, Nat.add_sub_cancel_left,
      Clocks.single]

@[simp] theorem resumed_heap (heap : Heap) (result : Result) (stack : Stack) :
    (resumeConfig heap result stack).heap = heap := by cases stack <;> rfl

theorem step_clock_monotone {before after : Configuration} (step : Step before after)
    (name : String) : before.heap.clocks name ≤ after.heap.clocks name := by
  cases step
  all_goals try simp only [resumed_heap]
  all_goals simp only [Config.heap, Heap.write_clocks, Heap.allocate_clocks, SequenceType.set, SequenceType.const, SequenceType.create, Heap.createSequence, Heap.writeElement, Heap.allocateSequence]
  all_goals try exact Nat.le_refl _
  all_goals exact Heap.clocks_le_tick _ _ _ _

theorem reaches_clock_monotone {before after : Configuration}
    (run : Reaches Step before after) (name : String) :
    before.heap.clocks name ≤ after.heap.clocks name := by
  apply run.invariant (fun state => before.heap.clocks name ≤ state.heap.clocks name)
    (Nat.le_refl _)
  intro first second move previous
  exact Nat.le_trans previous (step_clock_monotone move name)

/-- A finite execution adds exactly its heap cost to each initial clock. -/
theorem reaches_clocks {before after : Configuration}
    (run : Reaches Step before after) (costs : Clocks)
    (cost : Heap.cost before.heap after.heap = costs) (name : String) :
    after.heap.clocks name = before.heap.clocks name + costs name := by
  have monotone := reaches_clock_monotone run name
  have charged := congrFun cost name
  simp only [Heap.cost] at charged
  omega


end MatrixStrassenAnalysis
