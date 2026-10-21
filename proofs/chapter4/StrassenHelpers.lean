import StrassenLinear
import StrassenValue
import Algo2LeanLib.MatrixHeap

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace MatrixStrassenHelpers

open MatrixStrassenAnalysis

private theorem linearRun_data (count : Nat) (heap : Heap) (a b c : SeqRef) (sign first : Int) :
    (linearRun count heap a b c sign first).nextCollection = heap.nextCollection ∧
    (linearRun count heap a b c sign first).collections = heap.collections ∧
    (linearRun count heap a b c sign first).nextObject = heap.nextObject ∧
    (linearRun count heap a b c sign first).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ count ih => exact ih (linearStep heap a b c sign first) (first+1)

/-- One row combination allocates independent output storage and preserves all
    previously allocated rows, collections, and objects. -/
theorem linear_row_contract (heap : Heap) (a b : SeqRef) (count : Nat) (sign : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) :
    ∃ after result, matrix_linear_row.Call heap (a,b,(count:Int),sign) after result ∧
      Extends heap after ∧ result < after.nextRef ∧ heap.nextRef ≤ result ∧
      after.store result = (fun index => if 0 ≤ index ∧ index < (count:Int)
        then heap.read a index + sign * heap.read b index else 0) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "linear_cells" count name) := by
  let final := linearRun count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0
  have data := linearRun_data count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0
  refine ⟨final, heap.nextRef, linear_summary heap a b count sign validA validB, ?_, by simp [final],
    Nat.le_refl _, ?_, ?_⟩
  · refine ⟨by simp [final], by rw [data.1]; exact Nat.le_refl _, ?_, ?_, data.2.2.1, data.2.2.2⟩
    · intro old valid
      funext index
      rw [show final.store old index = final.read old index from rfl,
        linearRun_old count _ a b heap.nextRef old sign 0 index (Nat.ne_of_lt valid)]
      exact Heap.read_allocate_old heap _ old index valid
    · intro old _; exact congrFun data.2.1 old
  · funext index
    rw [show final.store heap.nextRef index = final.read heap.nextRef index from rfl,
      linearRun_value count _ a b heap.nextRef sign 0 index (Nat.ne_of_lt validA) (Nat.ne_of_lt validB)]
    simp [validA, validB]
  · intro name
    simpa only [Heap.allocate_clocks, Clocks.single] using
      linearRun_clocks count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0 name

private def copyStep (heap : Heap) (a c : SeqRef) (column index : Int) : Heap :=
  (heap.write c index (heap.read a (column+index))).tick "copied_cells"
private def copyRun : Nat → Heap → SeqRef → SeqRef → Int → Int → Heap
  | 0, heap, _, _, _, _ => heap
  | count+1, heap, a, c, column, index =>
    copyRun count (copyStep heap a c column index) a c column (index+1)


private theorem copyRun_data (count : Nat) (heap : Heap) (a c : SeqRef) (col first : Int) :
    (copyRun count heap a c col first).nextRef = heap.nextRef ∧
    (copyRun count heap a c col first).nextCollection = heap.nextCollection ∧
    (copyRun count heap a c col first).collections = heap.collections ∧
    (copyRun count heap a c col first).nextObject = heap.nextObject ∧
    (copyRun count heap a c col first).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ count ih => exact ih (copyStep heap a c col first) (first+1)

private theorem copyRun_old (count : Nat) (heap : Heap) (a c other : SeqRef)
    (col first index : Int) (different : other ≠ c) :
    (copyRun count heap a c col first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [copyRun]
    rw [ih]
    simp [copyStep, Heap.read, Heap.write, different]

private theorem copyRun_value (count : Nat) (heap : Heap) (a c : SeqRef)
    (col first index : Int) (separate : a ≠ c) :
    (copyRun count heap a c col first).read c index =
      if first ≤ index ∧ index < first+(count:Int)
      then heap.read a (col+index) else heap.read c index := by
  induction count generalizing heap first with
  | zero => simp only [copyRun, Int.natCast_zero, Int.add_zero]; rw [if_neg (by omega)]
  | succ count ih =>
    simp only [copyRun]
    rw [ih]
    simp only [copyStep, Heap.read, Heap.write, Heap.tick,
      separate, false_and, ↓reduceIte, true_and]
    grind

private theorem copyRun_clocks (count : Nat) (heap : Heap) (a c : SeqRef)
    (col first : Int) (name : String) :
    (copyRun count heap a c col first).clocks name =
      heap.clocks name + Clocks.single "copied_cells" count name := by
  induction count generalizing heap first with
  | zero => simp [copyRun, Clocks.single]
  | succ count ih =>
    simp only [copyRun, ih, copyStep, Heap.tick, Heap.write, Clocks.single]
    by_cases same : name = "copied_cells" <;> simp [same, Nat.add_assoc, Nat.add_comm 1 count]

/-- Copying a finite row segment returns fresh storage, preserves every previous
    row and outer array, and charges exactly the number of copied entries. -/
theorem quadrant_row_contract (heap : Heap) (a : SeqRef) (count : Nat) (column : Int)
    (validA : a < heap.nextRef) :
    ∃ after result, matrix_quadrant_row.Call heap (a,(count:Int),column) after result ∧
      Extends heap after ∧ result < after.nextRef ∧ heap.nextRef ≤ result ∧
      after.store result = (fun index => if 0 ≤ index ∧ index < (count:Int)
        then heap.read a (column+index) else 0) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" count name) := by
  -- Internal loop derivations are local to this source-facing contract.
  have copyLoop (count : Nat) (heap : Heap) (s : State_matrix_quadrant_row)
      (bound : s.v1 = s.v4 + (count:Int)) (validA : s.v0 < heap.nextRef)
      (validC : s.v3 < heap.nextRef) :
      Summary Step heap (.fn_matrix_quadrant_row 4 s)
        (copyRun count heap s.v0 s.v3 s.v2 s.v4) (.fn_matrix_quadrant_row s.v3) := by
    induction count generalizing heap s with
    | zero =>
      intro stack
      apply Reaches.prepend (Step.matrix_quadrant_row_pc4 ..)
      apply Reaches.prepend (Step.matrix_quadrant_row_pc3_false _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.matrix_quadrant_row_pc2 ..)
      exact Reaches.single (Step.matrix_quadrant_row_pc1 _ _ _ validC)
    | succ count ih =>
      intro stack
      apply Reaches.prepend (Step.matrix_quadrant_row_pc4 ..)
      apply Reaches.prepend (Step.matrix_quadrant_row_pc3_true _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.matrix_quadrant_row_pc7 _ _ _ (by exact ⟨validA,validC⟩))
      apply Reaches.prepend (Step.matrix_quadrant_row_pc6 ..)
      apply Reaches.prepend (Step.matrix_quadrant_row_pc5 ..)
      exact ih (copyStep heap s.v0 s.v3 s.v2 s.v4)
        {s with v4 := s.v4+1, t6 := decide (s.v4 < s.v1)} (by dsimp; omega) validA validC stack
  let final := copyRun count (heap.allocate (fun _ => 0)) a heap.nextRef column 0
  have data := copyRun_data count (heap.allocate (fun _ => 0)) a heap.nextRef column 0
  refine ⟨final, heap.nextRef, ?_, ?_, ?_, Nat.le_refl _, ?_, ?_⟩
  · refine ⟨validA, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_quadrant_row_pc11 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc10 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc9 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc8 ..)
    apply copyLoop count _ _ (by simp) (by simpa using Nat.lt_trans validA (Nat.lt_succ_self _))
      (Nat.lt_succ_self _) stack
  · refine ⟨by simp [final, data.1], by rw [data.2.1]; exact Nat.le_refl _, ?_, ?_, data.2.2.2.1, data.2.2.2.2⟩
    · intro old valid
      funext index
      rw [show final.store old index = final.read old index from rfl,
        copyRun_old count _ a heap.nextRef old column 0 index (Nat.ne_of_lt valid)]
      exact Heap.read_allocate_old heap _ old index valid
    · intro old _; exact congrFun data.2.2.1 old
  · simp [final, data.1]
  · funext index
    rw [show final.store heap.nextRef index = final.read heap.nextRef index from rfl,
      copyRun_value count _ a heap.nextRef column 0 index (Nat.ne_of_lt validA)]
    simp [validA]
  · exact copyRun_clocks count _ a heap.nextRef column 0


private def joinStep (heap : Heap) (a b c : SeqRef) (h index : Int) : Heap :=
  ((heap.write c index (heap.read a index)).write c (index+h) (heap.read b index)).tick "copied_cells" 2
private def joinRun : Nat → Heap → SeqRef → SeqRef → SeqRef → Int → Int → Heap
  | 0, heap, _, _, _, _, _ => heap
  | count+1, heap, a, b, c, h, index =>
    joinRun count (joinStep heap a b c h index) a b c h (index+1)


private theorem joinRun_data (count : Nat) (heap : Heap) (a b c : SeqRef) (h first : Int) :
    (joinRun count heap a b c h first).nextRef = heap.nextRef ∧
    (joinRun count heap a b c h first).nextCollection = heap.nextCollection ∧
    (joinRun count heap a b c h first).collections = heap.collections ∧
    (joinRun count heap a b c h first).nextObject = heap.nextObject ∧
    (joinRun count heap a b c h first).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ count ih => exact ih (joinStep heap a b c h first) (first+1)

private theorem joinRun_old (count : Nat) (heap : Heap) (a b c other : SeqRef)
    (h first index : Int) (different : other ≠ c) :
    (joinRun count heap a b c h first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [joinRun]
    rw [ih]
    simp [joinStep, Heap.read, Heap.write, different]

private theorem joinRun_value (count : Nat) (heap : Heap) (a b c : SeqRef)
    (h first index : Int) (nonneg : 0 ≤ first) (bound : first+(count:Int) ≤ h)
    (separateA : a ≠ c) (separateB : b ≠ c) :
    (joinRun count heap a b c h first).read c index =
      if first ≤ index ∧ index < first+(count:Int) then heap.read a index
      else if first+h ≤ index ∧ index < first+h+(count:Int)
      then heap.read b (index-h) else heap.read c index := by
  induction count generalizing heap first with
  | zero => simp only [joinRun, Int.natCast_zero, Int.add_zero]; rw [if_neg (by omega), if_neg (by omega)]
  | succ count ih =>
    simp only [joinRun]
    rw [ih _ (first+1) (by omega) (by omega)]
    simp only [joinStep, Heap.read, Heap.write, Heap.tick,
      separateA, separateB, false_and, ↓reduceIte, true_and]
    grind

private theorem joinRun_clocks (count : Nat) (heap : Heap) (a b c : SeqRef)
    (h first : Int) (name : String) :
    (joinRun count heap a b c h first).clocks name =
      heap.clocks name + Clocks.single "copied_cells" (2*count) name := by
  induction count generalizing heap first with
  | zero => simp [joinRun, Clocks.single]
  | succ count ih =>
    simp only [joinRun, ih, joinStep, Heap.tick, Heap.write, Clocks.single]
    by_cases same : name = "copied_cells" <;> simp [same] <;> omega

/-- Joining two row segments copies their entries into one fresh row. -/
theorem join_row_contract (heap : Heap) (a b : SeqRef) (count : Nat)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) :
    ∃ after result, matrix_join_row.Call heap (a,b,(count:Int)) after result ∧
      Extends heap after ∧ result < after.nextRef ∧ heap.nextRef ≤ result ∧
      after.store result = (fun index => if 0 ≤ index ∧ index < 2*(count:Int)
        then if index < (count:Int) then heap.read a index else heap.read b (index-count) else 0) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (2*count) name) := by
  -- Internal loop derivations are local to this source-facing contract.
  have joinLoop (count : Nat) (heap : Heap) (s : State_matrix_join_row)
      (bound : s.v2 = s.v4 + (count:Int)) (validA : s.v0 < heap.nextRef)
      (validB : s.v1 < heap.nextRef) (validC : s.v3 < heap.nextRef)
      (separateB : s.v1 ≠ s.v3) :
      Summary Step heap (.fn_matrix_join_row 4 s)
        (joinRun count heap s.v0 s.v1 s.v3 s.v2 s.v4) (.fn_matrix_join_row s.v3) := by
    induction count generalizing heap s with
    | zero =>
      intro stack
      apply Reaches.prepend (Step.matrix_join_row_pc4 ..)
      apply Reaches.prepend (Step.matrix_join_row_pc3_false _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.matrix_join_row_pc2 ..)
      exact Reaches.single (Step.matrix_join_row_pc1 _ _ _ validC)
    | succ count ih =>
      intro stack
      apply Reaches.prepend (Step.matrix_join_row_pc4 ..)
      apply Reaches.prepend (Step.matrix_join_row_pc3_true _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.matrix_join_row_pc8 _ _ _ (by exact ⟨validA,validC⟩))
      apply Reaches.prepend (Step.matrix_join_row_pc7 _ _ _ (by exact ⟨validB,validC⟩))
      apply Reaches.prepend (Step.matrix_join_row_pc6 ..)
      apply Reaches.prepend (Step.matrix_join_row_pc5 ..)
      have readB : (heap.write s.v3 s.v4 (heap.read s.v0 s.v4)).read s.v1 s.v4 = heap.read s.v1 s.v4 := by
        simp [Heap.read, Heap.write, separateB]
      simp only [readB]
      exact ih (joinStep heap s.v0 s.v1 s.v3 s.v2 s.v4)
        {s with v4 := s.v4+1, t6 := decide (s.v4 < s.v2)} (by dsimp; omega) validA validB validC separateB stack
  let final := joinRun count (heap.allocate (fun _ => 0)) a b heap.nextRef count 0
  have data := joinRun_data count (heap.allocate (fun _ => 0)) a b heap.nextRef count 0
  refine ⟨final, heap.nextRef, ?_, ?_, ?_, Nat.le_refl _, ?_, ?_⟩
  · refine ⟨⟨validA,validB⟩, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_join_row_pc12 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc11 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc10 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc9 ..)
    apply joinLoop count _ _ (by simp) (by simpa using Nat.lt_trans validA (Nat.lt_succ_self _))
      (by simpa using Nat.lt_trans validB (Nat.lt_succ_self _)) (Nat.lt_succ_self _) (Nat.ne_of_lt validB) stack
  · refine ⟨by simp [final, data.1], by rw [data.2.1]; exact Nat.le_refl _, ?_, ?_, data.2.2.2.1, data.2.2.2.2⟩
    · intro old valid
      funext index
      rw [show final.store old index = final.read old index from rfl,
        joinRun_old count _ a b heap.nextRef old count 0 index (Nat.ne_of_lt valid)]
      exact Heap.read_allocate_old heap _ old index valid
    · intro old _; exact congrFun data.2.2.1 old
  · simp [final, data.1]
  · funext index
    rw [show final.store heap.nextRef index = final.read heap.nextRef index from rfl,
      joinRun_value count _ a b heap.nextRef count 0 index (by omega) (by omega) (Nat.ne_of_lt validA) (Nat.ne_of_lt validB)]
    simp only [Heap.read_allocate_old _ _ _ _ validA, Heap.read_allocate_old _ _ _ _ validB,
      Heap.read_allocate_new, Int.zero_add]
    split <;> split <;> (try split) <;> simp_all <;> omega
  · exact joinRun_clocks count _ a b heap.nextRef count 0


private def rowPrefix (values : Values) (count : Nat) : Values := fun i j =>
  if 0 ≤ i ∧ i < (count:Int) then values i j else 0

private theorem prefix_next (values : Values) (i : Nat) :
    (fun j => if j = (i:Int) then values i else rowPrefix values i j) = rowPrefix values (i+1) := by
  funext j k
  by_cases same : j = (i:Int)
  · subst j
    simp only
    change values i k = if 0 ≤ (i:Int) ∧ (i:Int) < ((i+1:Nat):Int) then values i k else 0
    rw [if_pos (by omega)]
  · simp only [if_neg same]
    have eqRange : (0 ≤ j ∧ j < (i:Int)) ↔ (0 ≤ j ∧ j < ((i+1:Nat):Int)) := by omega
    simp only [rowPrefix, eqRange]

private theorem prefix_zero (values : Values) : rowPrefix values 0 = fun _ _ => 0 := by
  funext i j
  simp only [rowPrefix, Int.natCast_zero]
  rw [if_neg (by omega)]


/-- A matrix linear combination fills fresh independent rows and preserves
    every preexisting heap object. -/
theorem linear_contract (heap : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat) (sign : Int)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, matrix_linear.Call heap (a,b,(n:Int),sign) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.linearValues n sign av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "linear_cells" (n*n) name) := by
  -- Internal loop derivations are local to this source-facing contract.
  have linearMatrixLoop (remaining : Nat) (base heap : Heap) (s : State_matrix_linear)
      (n i : Nat) (av bv : Values) (bound : s.v2 = (n:Int)) (index : s.v5 = (i:Int))
      (finish : i+remaining = n) (sa : Stored base s.v0 av) (sb : Stored base s.v1 bv)
      (frame : Extends base heap) (fresh : base.nextCollection ≤ s.v4)
      (stored : Stored heap s.v4 (rowPrefix (fun r c =>
        if 0 ≤ c ∧ c < (n:Int) then av r c + s.v3*bv r c else 0) i)) :
      ∃ after, Summary Step heap (.fn_matrix_linear 4 s) after (.fn_matrix_linear s.v4) ∧
        Extends base after ∧ Stored after s.v4 (StrassenValues.linearValues n s.v3 av bv) ∧
        (∀ name, after.clocks name = heap.clocks name + Clocks.single "linear_cells" (remaining*n) name) := by
    induction remaining generalizing heap s i with
    | zero =>
      have ieq : i = n := by omega
      subst i
      refine ⟨heap, ?_, frame, ?_, ?_⟩
      · intro stack
        apply Reaches.prepend (Step.matrix_linear_pc4 ..)
        apply Reaches.prepend (Step.matrix_linear_pc3_false _ _ _ (by simp [bound,index]))
        apply Reaches.prepend (Step.matrix_linear_pc2 ..)
        exact Reaches.single (Step.matrix_linear_pc1 _ _ _ stored.1)
      · have eqValues : rowPrefix (fun r c => if 0 ≤ c ∧ c < (n:Int)
            then av r c + s.v3*bv r c else 0) n = StrassenValues.linearValues n s.v3 av bv := by
          funext r c
          simp only [rowPrefix, StrassenValues.linearValues]
          grind
        rw [eqValues] at stored
        exact stored
      · intro name; simp [Clocks.single]
    | succ remaining ih =>
      have ai := sa.mono frame
      have bi := sb.mono frame
      obtain ⟨one,row,rowRun,rowFrame,rowValid,rowFresh,rowValue,rowClocks⟩ :=
        linear_row_contract heap ((rows.get heap s.v0 s.v5).getD 0)
          ((rows.get heap s.v1 s.v5).getD 0) n s.v3 (ai.row_valid s.v5) (bi.row_valid s.v5)
      let nextHeap := rows.set one s.v4 s.v5 row
      let next : State_matrix_linear := { s with v5 := s.v5+1, t7 := decide (s.v5<s.v2), t8 := row, t9 := s.v5, t10 := s.v4, t11 := (rows.get heap s.v0 s.v5).getD 0, t12 := (rows.get heap s.v1 s.v5).getD 0, t13 := s.v2, t14 := s.v3 }
      have nextFrame : Extends base nextHeap := (frame.trans rowFrame).set s.v4 fresh s.v5 row
      have nextStored : Stored nextHeap next.v4 (rowPrefix (fun r c =>
          if 0 ≤ c ∧ c < (n:Int) then av r c + next.v3*bv r c else 0) (i+1)) := by
        have st := (stored.mono rowFrame).set s.v5 row _ rowValid rowValue
        have rowEq : (fun c => if 0 ≤ c ∧ c < (n:Int) then
            heap.read ((rows.get heap s.v0 s.v5).getD 0) c +
              s.v3 * heap.read ((rows.get heap s.v1 s.v5).getD 0) c else 0) =
            (fun c => if 0 ≤ c ∧ c < (n:Int) then av (i:Int) c + s.v3*bv (i:Int) c else 0) := by
          funext c; rw [ai.read,bi.read,index]
        rw [rowEq,index, prefix_next (fun r c => if 0 ≤ c ∧ c < (n:Int) then av r c + s.v3*bv r c else 0) i] at st
        simpa only [nextHeap,next,index] using st
      obtain ⟨after,completed,afterFrame,afterStored,afterClocks⟩ :=
        ih nextHeap next (i+1) bound (by dsimp [next]; omega) (by omega) sa sb nextFrame fresh nextStored
      refine ⟨after, ?_, afterFrame, afterStored, ?_⟩
      · intro stack
        apply Reaches.prepend (Step.matrix_linear_pc4 ..)
        apply Reaches.prepend (Step.matrix_linear_pc3_true _ _ _ (by simp [bound,index]; omega))
        apply Reaches.prepend (Step.matrix_linear_pc13 _ _ _ (by exact ai.row s.v5))
        apply Reaches.prepend (Step.matrix_linear_pc12 _ _ _ (by exact bi.row s.v5))
        apply Reaches.prepend (Step.matrix_linear_pc11 ..)
        apply Reaches.prepend (Step.matrix_linear_pc10 ..)
        apply Reaches.prepend (Step.matrix_linear_pc9 ..)
        simp only [bound]
        apply Reaches.trans (rowRun.2 _)
        apply Reaches.prepend (Step.matrix_linear_pc8 ..)
        apply Reaches.prepend (Step.matrix_linear_pc7 ..)
        apply Reaches.prepend (Step.matrix_linear_pc6 _ _ _ (by exact rowFrame.valid stored.1))
        apply Reaches.prepend (Step.matrix_linear_pc5 ..)
        simpa only [next,nextHeap,bound,show seq_Seq_Int = rows from rfl] using completed stack
      · intro name
        rw [afterClocks]
        change one.clocks name + _ = _
        rw [rowClocks]
        by_cases same : name = "linear_cells" <;> simp [Clocks.single,same, Nat.add_mul] <;> omega
  let initialized := (rows.const (heap.allocate (fun _ => 0)) heap.nextRef).1
  have frame : Extends heap initialized := (extends_allocate heap _).trans (extends_const _ _)
  have stored : Stored initialized heap.nextCollection (fun _ _ => 0) :=
    stored_const (heap.allocate (fun _ => 0)) heap.nextRef _ (Nat.lt_succ_self _) (by simp [Heap.allocate])
  let state : State_matrix_linear := { v0 := a, v1 := b, v2 := n, v3 := sign, v4 := heap.nextCollection, t15 := heap.nextCollection, t16 := heap.nextRef }
  obtain ⟨after,completed,afterFrame,afterStored,afterClocks⟩ :=
    linearMatrixLoop n heap initialized state n 0 av bv rfl rfl (by omega) sa sb frame (Nat.le_refl _)
      (by simpa only [state,prefix_zero] using stored)
  refine ⟨after,heap.nextCollection,⟨⟨sa.1,sb.1⟩,?_⟩,afterFrame,afterStored,afterClocks⟩
  intro stack
  apply Reaches.prepend (Step.matrix_linear_pc18 ..)
  apply Reaches.prepend (Step.matrix_linear_pc17 ..)
  apply Reaches.prepend (Step.matrix_linear_pc16 ..)
  apply Reaches.prepend (Step.matrix_linear_pc15 ..)
  apply Reaches.prepend (Step.matrix_linear_pc14 ..)
  exact completed stack


private def pairedPrefix (values : Values) (n count : Nat) : Values := fun i j =>
  if (0 ≤ i ∧ i < (count:Int)) ∨ ((n:Int) ≤ i ∧ i < (n:Int)+(count:Int)) then values i j else 0

private theorem paired_zero (values : Values) (n : Nat) : pairedPrefix values n 0 = fun _ _ => 0 := by
  funext i j
  simp only [pairedPrefix, Int.natCast_zero, Int.add_zero]
  rw [if_neg (by omega)]

private theorem paired_next (values : Values) (n i : Nat) (unfinished : i < n) :
    (fun j => if j = (i:Int)+(n:Int) then values ((i:Int)+n)
      else if j = (i:Int) then values i else pairedPrefix values n i j) = pairedPrefix values n (i+1) := by
  funext j k
  by_cases bottom : j = (i:Int)+(n:Int)
  · subst j
    simp only
    change values _ _ = if _ then values _ _ else 0
    rw [if_pos (by omega)]
  · simp only [if_neg bottom]
    by_cases top : j = (i:Int)
    · subst j
      simp only
      change values _ _ = if _ then values _ _ else 0
      rw [if_pos (by omega)]
    · simp only [if_neg top]
      have eqRange : ((0 ≤ j ∧ j < (i:Int)) ∨ ((n:Int) ≤ j ∧ j < (n:Int)+(i:Int))) ↔
          ((0 ≤ j ∧ j < ((i+1:Nat):Int)) ∨ ((n:Int) ≤ j ∧ j < (n:Int)+((i+1:Nat):Int))) := by omega
      simp only [pairedPrefix, eqRange]

private def FreshOn (before after : Heap) (matrix : CollectionRef) (domain : Nat → Prop) : Prop :=
  (∀ i : Nat, domain i → ∃ row, rows.get after matrix i = some row ∧
    before.nextRef ≤ row ∧ row < after.nextRef) ∧
  (∀ i j : Nat, domain i → domain j → rows.get after matrix i = rows.get after matrix j → i = j)

private theorem freshOn_install (before heap after : Heap) (matrix : CollectionRef)
    (domain : Nat → Prop) (ownership : FreshOn before heap matrix domain)
    (valid : rows.valid heap matrix) (extension : Extends heap after)
    (bound : before.nextRef ≤ heap.nextRef) (index row : Nat)
    (fresh : heap.nextRef ≤ row) (allocated : row < after.nextRef) :
    FreshOn before (rows.set after matrix index row) matrix (fun i => i = index ∨ domain i) := by
  have installed : rows.get (rows.set after matrix index row) matrix index = some row :=
    rows.get_set_same after matrix index row (extension.valid valid)
  have unchanged : ∀ i : Nat, i ≠ index →
      rows.get (rows.set after matrix index row) matrix i = rows.get heap matrix i := by
    intro i different
    rw [rows.get_set_other_index _ _ _ _ _ (by omega)]
    exact extension.get valid i
  constructor
  · intro i inside
    rcases inside with same | old
    · subst i
      exact ⟨row, installed, Nat.le_trans bound fresh, allocated⟩
    · by_cases same : i = index
      · subst i
        exact ⟨row, installed, Nat.le_trans bound fresh, allocated⟩
      · obtain ⟨oldRow, read, lower, upper⟩ := ownership.1 i old
        exact ⟨oldRow, (unchanged i same).trans read, lower,
          Nat.lt_of_lt_of_le upper extension.nextRef⟩
  · intro i j di dj equal
    by_cases sameI : i = index
    · subst i
      by_cases sameJ : j = index
      · exact sameJ.symm
      · have oldJ : domain j := dj.resolve_left sameJ
        obtain ⟨oldRow, read, lower, upper⟩ := ownership.1 j oldJ
        rw [installed, unchanged j sameJ, read] at equal
        have rowEq := Option.some.inj equal
        exact False.elim ((Nat.not_lt_of_ge fresh) (by simpa only [rowEq] using upper))
    · by_cases sameJ : j = index
      · subst j
        have oldI : domain i := di.resolve_left sameI
        obtain ⟨oldRow, read, lower, upper⟩ := ownership.1 i oldI
        rw [installed, unchanged i sameI, read] at equal
        have rowEq := Option.some.inj equal
        exact False.elim ((Nat.not_lt_of_ge fresh) (by simpa only [rowEq] using upper))
      · rw [unchanged i sameI, unchanged j sameJ] at equal
        exact ownership.2 i j (di.resolve_left sameI) (dj.resolve_left sameJ) equal

private def pairedDomain (n count : Nat) (i : Nat) : Prop :=
  i < count ∨ (n ≤ i ∧ i < n + count)

private theorem pairedDomain_step (n i : Nat) :
    (fun j => j = i + n ∨ j = i ∨ pairedDomain n i j) = pairedDomain n (i + 1) := by
  funext j
  apply propext
  simp only [pairedDomain]
  omega


/-- Join four nested blocks into a fresh matrix; every finite row comes from
    an independent row allocation. Input rows may alias freely. -/
theorem join_contract_rows (heap : Heap) (a b c d : CollectionRef) (av bv cv dv : Values) (h : Nat)
    (sa : Stored heap a av) (sb : Stored heap b bv) (sc : Stored heap c cv) (sd : Stored heap d dv)
    (_positive : 0 < h) :
    ∃ after result, matrix_join.Call heap (a,b,c,d,(h:Int)) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.joinValues h av bv cv dv) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (4*(h*h)) name) ∧
      heap.nextCollection ≤ result ∧ FreshRows heap after result (2*h) := by
  -- Internal loop derivations are local to this source-facing contract.
  have joinMatrixLoop (remaining : Nat) (base heap : Heap) (s : State_matrix_join)
      (n i : Nat) (av bv cv dv : Values) (bound : s.v4 = (n:Int)) (index : s.v6 = (i:Int))
      (finish : i+remaining = n) (sa : Stored base s.v0 av) (sb : Stored base s.v1 bv)
      (sc : Stored base s.v2 cv) (sd : Stored base s.v3 dv)
      (frame : Extends base heap) (fresh : base.nextCollection ≤ s.v5)
      (stored : Stored heap s.v5 (pairedPrefix (StrassenValues.joinValues n av bv cv dv) n i))
      (ownership : FreshOn base heap s.v5 (pairedDomain n i)) :
      ∃ after, Summary Step heap (.fn_matrix_join 4 s) after (.fn_matrix_join s.v5) ∧
        Extends base after ∧ Stored after s.v5 (StrassenValues.joinValues n av bv cv dv) ∧
        (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (4*(remaining*n)) name) ∧
        FreshRows base after s.v5 (2*n) := by
    induction remaining generalizing heap s i with
    | zero =>
      have ieq : i = n := by omega
      subst i
      refine ⟨heap, ?_, frame, ?_, ?_, ?_⟩
      · intro stack
        apply Reaches.prepend (Step.matrix_join_pc4 ..)
        apply Reaches.prepend (Step.matrix_join_pc3_false _ _ _ (by simp [bound,index]))
        apply Reaches.prepend (Step.matrix_join_pc2 ..)
        exact Reaches.single (Step.matrix_join_pc1 _ _ _ stored.1)
      · have eqValues : pairedPrefix (StrassenValues.joinValues n av bv cv dv) n n =
            StrassenValues.joinValues n av bv cv dv := by
          funext r c
          simp only [pairedPrefix,StrassenValues.joinValues]
          grind
        rw [eqValues] at stored
        exact stored
      · intro name; simp [Clocks.single]
      · have domainEq : pairedDomain n n = (fun j => j < 2*n) := by
          funext j
          apply propext
          unfold pairedDomain
          omega
        change FreshOn base heap s.v5 (fun j => j < 2*n)
        simpa only [domainEq] using ownership
    | succ remaining ih =>
      have unfinished : i < n := by omega
      have ai := sa.mono frame
      have bi := sb.mono frame
      obtain ⟨one,topRow,topRun,topFrame,topValid,topFresh,topValue,topClocks⟩ :=
        join_row_contract heap ((rows.get heap s.v0 s.v6).getD 0)
          ((rows.get heap s.v1 s.v6).getD 0) n (ai.row_valid s.v6) (bi.row_valid s.v6)
      let middle := rows.set one s.v5 s.v6 topRow
      have middleFrame : Extends base middle := (frame.trans topFrame).set s.v5 fresh s.v6 topRow
      have topEq : (fun c => if 0 ≤ c ∧ c < 2*(n:Int) then
          if c < (n:Int) then heap.read ((rows.get heap s.v0 s.v6).getD 0) c
          else heap.read ((rows.get heap s.v1 s.v6).getD 0) (c-n) else 0) =
          StrassenValues.joinValues n av bv cv dv i := by
        funext c
        rw [ai.read,bi.read,index]
        simp only [StrassenValues.joinValues]
        have irange : 0 ≤ (i:Int) ∧ (i:Int) < 2*n := by omega
        have ilow : (i:Int) < n := by omega
        simp only [irange.1,irange.2,ilow,true_and,if_pos]
      have topStored := (stored.mono topFrame).set s.v6 topRow _ topValid topValue
      rw [topEq] at topStored
      have topOwned : FreshOn base middle s.v5 (fun j => j = i ∨ pairedDomain n i j) := by
        simpa only [middle, index] using freshOn_install base heap one s.v5
          (pairedDomain n i) ownership stored.1 topFrame frame.nextRef i topRow topFresh topValid
      have ci := sc.mono middleFrame
      have di := sd.mono middleFrame
      obtain ⟨two,bottomRow,bottomRun,bottomFrame,bottomValid,bottomFresh,bottomValue,bottomClocks⟩ :=
        join_row_contract middle ((rows.get middle s.v2 s.v6).getD 0)
          ((rows.get middle s.v3 s.v6).getD 0) n (ci.row_valid s.v6) (di.row_valid s.v6)
      let nextHeap := rows.set two s.v5 (s.v6+s.v4) bottomRow
      let next : State_matrix_join := { s with v6 := s.v6+1, t8 := decide (s.v6<s.v4), t9 := bottomRow, t10 := s.v6+s.v4, t11 := s.v5, t12 := (rows.get middle s.v2 s.v6).getD 0, t13 := (rows.get middle s.v3 s.v6).getD 0, t14 := s.v4, t15 := topRow, t16 := s.v6, t17 := s.v5, t18 := (rows.get heap s.v0 s.v6).getD 0, t19 := (rows.get heap s.v1 s.v6).getD 0, t20 := s.v4 }
      have nextFrame : Extends base nextHeap := (middleFrame.trans bottomFrame).set s.v5 fresh _ bottomRow
      have bottomEq : (fun c => if 0 ≤ c ∧ c < 2*(n:Int) then
          if c < (n:Int) then middle.read ((rows.get middle s.v2 s.v6).getD 0) c
          else middle.read ((rows.get middle s.v3 s.v6).getD 0) (c-n) else 0) =
          StrassenValues.joinValues n av bv cv dv ((i:Int)+n) := by
        funext c
        rw [ci.read,di.read,index]
        simp only [StrassenValues.joinValues]
        have irange : 0 ≤ (i:Int)+n ∧ (i:Int)+n < 2*n := by omega
        have ilow : ¬(i:Int)+n < n := by omega
        have cancel : (i:Int)+n-n = i := by omega
        simp only [irange.1,irange.2,ilow,true_and,if_false,cancel]
      have nextStored : Stored nextHeap next.v5 (pairedPrefix (StrassenValues.joinValues n av bv cv dv) n (i+1)) := by
        have st := (topStored.mono bottomFrame).set (s.v6+s.v4) bottomRow _ bottomValid bottomValue
        rw [bottomEq,index,bound,paired_next _ n i unfinished] at st
        simpa only [nextHeap,next,index,bound] using st
      have nextOwned : FreshOn base nextHeap next.v5 (pairedDomain n (i+1)) := by
        have installed := freshOn_install base middle two s.v5
          (fun j => j = i ∨ pairedDomain n i j) topOwned topStored.1 bottomFrame
          middleFrame.nextRef (i+n) bottomRow bottomFresh bottomValid
        rw [pairedDomain_step] at installed
        simpa only [nextHeap, next, index, bound, Int.natCast_add] using installed
      obtain ⟨after,completed,afterFrame,afterStored,afterClocks,afterOwned⟩ :=
        ih nextHeap next (i+1) bound (by dsimp [next]; omega) (by omega) sa sb sc sd nextFrame fresh nextStored nextOwned
      refine ⟨after, ?_, afterFrame, afterStored, ?_, afterOwned⟩
      · intro stack
        apply Reaches.prepend (Step.matrix_join_pc4 ..)
        apply Reaches.prepend (Step.matrix_join_pc3_true _ _ _ (by simp [bound,index]; omega))
        apply Reaches.prepend (Step.matrix_join_pc19 _ _ _ (by exact ai.row s.v6))
        apply Reaches.prepend (Step.matrix_join_pc18 _ _ _ (by exact bi.row s.v6))
        apply Reaches.prepend (Step.matrix_join_pc17 ..)
        apply Reaches.prepend (Step.matrix_join_pc16 ..)
        simp only [bound]
        apply Reaches.trans (topRun.2 _)
        apply Reaches.prepend (Step.matrix_join_pc15 ..)
        apply Reaches.prepend (Step.matrix_join_pc14 ..)
        apply Reaches.prepend (Step.matrix_join_pc13 _ _ _ (by exact topFrame.valid stored.1))
        apply Reaches.prepend (Step.matrix_join_pc12 _ _ _ (by exact ci.row s.v6))
        apply Reaches.prepend (Step.matrix_join_pc11 _ _ _ (by exact di.row s.v6))
        apply Reaches.prepend (Step.matrix_join_pc10 ..)
        apply Reaches.prepend (Step.matrix_join_pc9 ..)
        apply Reaches.trans (bottomRun.2 _)
        apply Reaches.prepend (Step.matrix_join_pc8 ..)
        apply Reaches.prepend (Step.matrix_join_pc7 ..)
        apply Reaches.prepend (Step.matrix_join_pc6 _ _ _ (by exact bottomFrame.valid topStored.1))
        apply Reaches.prepend (Step.matrix_join_pc5 ..)
        simpa only [next,nextHeap,middle,bound,show seq_Seq_Int = rows from rfl] using completed stack
      · intro name
        rw [afterClocks]
        change two.clocks name + _ = _
        rw [bottomClocks]
        change one.clocks name + _ + _ = _
        rw [topClocks]
        by_cases same : name = "copied_cells" <;> simp [Clocks.single,same,Nat.add_mul] <;> omega
  let initialized := (rows.const (heap.allocate (fun _ => 0)) heap.nextRef).1
  have frame : Extends heap initialized := (extends_allocate heap _).trans (extends_const _ _)
  have stored : Stored initialized heap.nextCollection (fun _ _ => 0) :=
    stored_const (heap.allocate (fun _ => 0)) heap.nextRef _ (Nat.lt_succ_self _) (by simp [Heap.allocate])
  let state : State_matrix_join := { v0 := a, v1 := b, v2 := c, v3 := d, v4 := h, v5 := heap.nextCollection, t21 := heap.nextCollection, t22 := heap.nextRef }
  obtain ⟨after,completed,afterFrame,afterStored,afterClocks,afterOwned⟩ :=
    joinMatrixLoop h heap initialized state h 0 av bv cv dv rfl rfl (by omega) sa sb sc sd frame (Nat.le_refl _)
      (by simpa only [state,paired_zero] using stored)
      (by
        constructor
        · intro j impossible
          simp only [pairedDomain, Nat.add_zero] at impossible
          omega
        · intro j k impossible
          simp only [pairedDomain, Nat.add_zero] at impossible
          omega)
  refine ⟨after,heap.nextCollection,⟨⟨sa.1,sb.1,sc.1,sd.1⟩,?_⟩,afterFrame,afterStored,afterClocks,Nat.le_refl _,afterOwned⟩
  intro stack
  apply Reaches.prepend (Step.matrix_join_pc24 ..)
  apply Reaches.prepend (Step.matrix_join_pc23 ..)
  apply Reaches.prepend (Step.matrix_join_pc22 ..)
  apply Reaches.prepend (Step.matrix_join_pc21 ..)
  apply Reaches.prepend (Step.matrix_join_pc20 ..)
  exact completed stack

/-- The outer-freshness projection used by clients that do not mutate rows. -/
theorem join_contract_fresh (heap : Heap) (a b c d : CollectionRef) (av bv cv dv : Values) (h : Nat)
    (sa : Stored heap a av) (sb : Stored heap b bv) (sc : Stored heap c cv) (sd : Stored heap d dv)
    (positive : 0 < h) :
    ∃ after result, matrix_join.Call heap (a,b,c,d,(h:Int)) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.joinValues h av bv cv dv) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (4*(h*h)) name) ∧
      heap.nextCollection ≤ result := by
  obtain ⟨after,result,run,frame,values,clocks,fresh,_⟩ :=
    join_contract_rows heap a b c d av bv cv dv h sa sb sc sd positive
  exact ⟨after,result,run,frame,values,clocks,fresh⟩

end MatrixStrassenHelpers
