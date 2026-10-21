import rows
import allocation
import Algo2LeanLib.ParallelMatrixFresh

/-!
Complete allocating parallel matrix multiplication over arrays of integer rows.
The reusable preallocated computation has logarithmic span. This wrapper also
charges sequential creation of distinct rows, giving linear total span.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelMatrix

namespace ParallelMatrixPublic

private theorem work_wrapper (n a m : Nat) (ha : a ≤ 32*n+4) (hm : m ≤ 4096*(n+1)^3) :
    a+m+19 ≤ 4096*(n+1)^3+32*n+23 := by omega

private theorem span_wrapper (n a m : Nat) (ha : a ≤ 32*n+4) (hm : m ≤ 256*(Nat.log2 n+2)) :
    a+m+19 ≤ 256*(Nat.log2 n+2)+32*n+23 := by omega

/-- The fresh nested product, its allocated representation, and complete caller
storage preservation. One unused zero row provides the outer array's default. -/
structure Postcondition (before after : Heap) (output : CollectionRef) (n : Nat)
    (arows brows : Int → SeqRef) : Prop where
  output_ref : output = before.nextCollection
  nextRef : after.nextRef = before.nextRef+1+n
  nextCollection : after.nextCollection = before.nextCollection+1
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  clocks : after.clocks = before.clocks
  old_sequences : ∀ ref, ref < before.nextRef → after.read ref = before.read ref
  old_collections : ∀ ref, ref < before.nextCollection → after.collections ref = before.collections ref
  view : MatrixView after output 0 n (freshRows before)
  product : ∀ i j : Int, 0 ≤ i → i < n → 0 ≤ j → j < n →
    after.read (freshRows before i) j =
      dot (before.read (arows i)) (matrixValues before brows) j 0 n
  outside_columns : ∀ i : Int, 0 ≤ i → i < n → ∀ j : Int, j < 0 ∨ (n : Int) ≤ j →
    after.read (freshRows before i) j = 0
  default_zero : after.read before.nextRef = fun _ => 0
  outside_rows : ∀ i : Int, i < 0 ∨ (n : Int) ≤ i → rowType.get after output i = some before.nextRef

/-- Allocate independent rows before entering parallel computation. Correctness,
fresh storage, work, and span all refer to this same generated execution. -/
theorem call_contract (h : Heap) (a b : CollectionRef) (n : Nat) (arows brows : Int → SeqRef)
    (av : MatrixView h a 0 n arows) (bv : MatrixView h b 0 n brows) :
    ∃ final cost access,
      parallel_matrix_multiply.ParallelCall h (a,b,↑n) final h.nextCollection cost access ∧
      Postcondition h final h.nextCollection n arows brows ∧
      cost.work ≤ 4096*(n+1)^3+32*n+23 ∧
      cost.span ≤ 256*(Nat.log2 n+2)+32*n+23 := by
  have outerValid : rowType.valid (initialOuter h) h.nextCollection := by
    exact rowType.valid_const _ _
  obtain ⟨ac, aa, allocated, aw, asp⟩ :=
    ParallelMatrixAllocationAnalysis.call_contract (initialOuter h) h.nextCollection 0 n outerValid
  have av' := fresh_input_view av n
  have bv' := fresh_input_view bv n
  have ov := fresh_view h n
  have distinct : DistinctRows (freshRows h) n := by
    intro i j il ih jl jh equal
    exact fresh_rows_injective h i j il jl equal
  have separate : SeparateRows arows brows (freshRows h) n := by
    intro i j il ih jl jh
    exact ⟨fresh_rows_disjoint h (arows j) (av.allocated j jl (by simpa using jh)) i,
      fresh_rows_disjoint h (brows j) (bv.allocated j jl (by simpa using jh)) i⟩
  obtain ⟨final, measured, accesses, run, frame, result, work, span, within⟩ :=
    ParallelMatrixIntoAnalysis.call_contract (freshHeap h n) a b h.nextCollection n
      arows brows (freshRows h) av' bv' ov distinct separate
  have finalView := ov.rowsFrame frame
  refine ⟨final, _, _, ⟨⟨av.valid,bv.valid⟩, by
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.call
    · rfl
    · simpa only [initialOuter, rowType, seq_Seq_Int, Heap.allocate] using allocated.2
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.call
    · rfl
    · simpa only [freshHeap, initialOuter, rowType, seq_Seq_Int, Heap.allocate] using run.2
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.ret
    simp only [parallelNext, Heap.allocate, if_pos (show seq_Seq_Int.valid final h.nextCollection from finalView.valid)]
    rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, finalView, ?_, ?_, ?_, ?_⟩
    · rw [frame.nextRef, fresh_nextRef]
    · rw [frame.nextCollection, fresh_nextCollection]
    · rw [frame.nextObject, fresh_nextObject]
    · rw [frame.objects, fresh_objects]
    · rw [frame.clocks, fresh_clocks]
    · intro ref old
      rw [frame.read_other ref (fun i _ _ => (fresh_rows_disjoint h ref old i).symm)]
      exact fresh_read_old h n ref old
    · intro ref old
      rw [frame.collections]
      exact fresh_collection_old h n ref old
    · intro i j il ih jl jh
      rw [result i j (by simpa using il) (by simpa using ih) jl jh]
      apply dot_congr
      · intro k hk
        rw [fresh_read_old h n (arows i) (av.allocated i il (by simpa using ih))]
      · intro k hk
        simp only [matrixValues]
        rw [fresh_read_old h n (brows (0+k)) (bv.allocated (0+k) (by omega) (by omega))]
    · intro i il ih j outside
      rw [frame.outside _ j (Or.inr outside)]
      exact congrFun (fresh_read_zero h n i il ih) j
    · rw [frame.read_other h.nextRef (fun i _ _ => Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self h.nextRef) (Nat.le_add_right _ _)))]
      exact fresh_default_zero h n
    · intro i outside
      have same : rowType.get final h.nextCollection i = rowType.get (freshHeap h n) h.nextCollection i := by
        unfold SequenceType.get SequenceType.valid Heap.validSequence Heap.sequenceType Heap.readElement
        simp only [frame.nextCollection, frame.collections]
      rw [same]
      exact fresh_get_outside h n i outside
  · simpa only [Cost.work_seq, Cost.one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using work_wrapper n ac.work measured.work aw work
  · simpa only [Cost.span_seq, Cost.one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using span_wrapper n ac.span measured.span asp span

-- Main result: Correctness
/-- Every well-formed pair of n-by-n nested integer matrices has a terminating
call producing their row-by-column product in fresh storage. Inputs may alias. -/
theorem correctness (h : Heap) (a b : CollectionRef) (n : Nat) (arows brows : Int → SeqRef)
    (av : MatrixView h a 0 n arows) (bv : MatrixView h b 0 n brows) :
    ∃ final output, parallel_matrix_multiply.Call h (a,b,↑n) final output ∧
      Postcondition h final output n arows brows := by
  obtain ⟨final,cost,access,run,post,_,_⟩ := call_contract h a b n arows brows av bv
  exact ⟨final,h.nextCollection,run.call,post⟩

theorem correctness_of_parallel_call (h : Heap) (a b : CollectionRef) (n : Nat)
    (arows brows : Int → SeqRef) (av : MatrixView h a 0 n arows) (bv : MatrixView h b 0 n brows)
    {final : Heap} {output : CollectionRef} {cost : Cost} {access : Access}
    (run : parallel_matrix_multiply.ParallelCall h (a,b,↑n) final output cost access) :
    Postcondition h final output n arows brows := by
  obtain ⟨other,measured,accesses,witness,result,_,_⟩ := call_contract h a b n arows brows av bv
  have equal := witness.2.deterministic run.2
  have outputEqual := Algo2LeanGenerated.Result.fn_parallel_matrix_multiply.inj equal.2.1
  simpa only [equal.1, outputEqual] using result

/-- Explicit cubic work and linear-plus-logarithmic span include row allocation. -/
theorem running_time_explicit (h : Heap) (a b : CollectionRef) (n : Nat)
    (arows brows : Int → SeqRef) (av : MatrixView h a 0 n arows) (bv : MatrixView h b 0 n brows)
    {final : Heap} {output : CollectionRef} {cost : Cost} {access : Access}
    (run : parallel_matrix_multiply.ParallelCall h (a,b,↑n) final output cost access) :
    cost.work ≤ 4096*(n+1)^3+32*n+23 ∧
    cost.span ≤ 256*(Nat.log2 n+2)+32*n+23 := by
  obtain ⟨other,measured,accesses,witness,result,work,span⟩ := call_contract h a b n arows brows av bv
  have equal := run.2.deterministic witness.2
  rw [equal.2.2.1]
  exact ⟨work,span⟩

-- Main result: Running time
/-- One uniform positive constant bounds total work cubically and total span
linearly. The extra span is the sequential allocation of distinct output rows;
the reusable preallocated multiplication has logarithmic span. -/
theorem running_time : ∃ C : Nat, 0 < C ∧
    ∀ (h : Heap) (a b : CollectionRef) (n : Nat) (arows brows : Int → SeqRef),
    MatrixView h a 0 n arows → MatrixView h b 0 n brows →
    ∀ {final : Heap} {output : CollectionRef} {cost : Cost} {access : Access},
    parallel_matrix_multiply.ParallelCall h (a,b,↑n) final output cost access →
    cost.work ≤ C*(n+1)^3 ∧ cost.span ≤ C*(n+1) := by
  refine ⟨8192, by decide, ?_⟩
  intro h a b n arows brows av bv final output cost access run
  have bounds := running_time_explicit h a b n arows brows av bv run
  have cube : n+1 ≤ (n+1)^3 := Nat.le_pow (by decide)
  have logarithm := Nat.log2_le_self n
  constructor <;> omega

end ParallelMatrixPublic
