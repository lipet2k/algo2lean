import merge
import merge_sort

/-!
Complete CLRS parallel merge and merge-sort contracts for the allocating entry
points. Each theorem connects correctness, storage preservation, and work/span
to the same generated execution. Lengths are nonnegative; entries and starting
indices are arbitrary integers, and duplicate keys are preserved.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelMerge

namespace ParallelAllocated

/-- The output is the first newly allocated sequence; all caller-owned storage
and all existing cost counters survive the completed operation. -/
structure FreshOutput (before after : Heap) (output : SeqRef) (allocations : Nat) : Prop where
  output_ref : output = before.nextRef
  allocation : after.nextRef = before.nextRef + allocations
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  clocks : after.clocks = before.clocks
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections
  caller_sequences : ∀ ref, ref < before.nextRef → after.read ref = before.read ref

end ParallelAllocated

namespace ParallelMergePublic

/-- Sorted output at indices `[0,m+n)`, including multiplicities, together
with one fresh allocation and preservation of caller-owned storage. -/
structure Postcondition (before after : Heap) (a output : SeqRef)
    (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat) : Prop
    extends ParallelAllocated.FreshOutput before after output 1 where
  merged : MergeResult (interval (before.read a) lo1 m) (interval (before.read a) lo2 n)
    (interval (after.read output) 0 (m+n))
  outside : ∀ i : Int, i < 0 ∨ ((m+n : Nat) : Int) ≤ i → after.read output i = 0

/-- The allocating entry point reuses the merge contract unchanged. -/
theorem call_contract (h : Heap) (a : SeqRef) (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat)
    (valid : a < h.nextRef)
    (firstSorted : (interval (h.read a) lo1 m).Pairwise (· ≤ ·))
    (secondSorted : (interval (h.read a) lo2 n).Pairwise (· ≤ ·)) :
    ∃ final output cost access,
      parallel_merge.ParallelCall h (a,lo1,↑m,lo2,↑n) final output cost access ∧
      Postcondition h final a output lo1 m lo2 n ∧
      cost.work ≤ 1024*(m+n+1)+14 ∧ cost.span ≤ 4096*(Nat.log2 (m+n+1)+1)^2+14 := by
  let allocated := h.allocate (fun _ => 0)
  have aOther : a ≠ h.nextRef := Nat.ne_of_lt valid
  have source : allocated.read a = h.read a := by
    funext i
    simp [allocated, Heap.read, Heap.allocate, aOther]
  have an : a < allocated.nextRef := Nat.lt_trans valid (Nat.lt_succ_self _)
  have on : h.nextRef < allocated.nextRef := Nat.lt_succ_self _
  obtain ⟨final, measured, accesses, run, frame, result, work, span, within⟩ :=
    ParallelMergeAnalysis.merge_contract allocated a h.nextRef lo1 m lo2 n 0 an on aOther
      (by rwa [source]) (by rwa [source])
  rw [source] at result
  have finalValid : h.nextRef < final.nextRef := by rw [frame.nextRef]; exact on
  refine ⟨final, h.nextRef, _, _, ⟨valid, by
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
    apply Eval.step
    · rfl
    apply Eval.call
    · rfl
    · exact run.2
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.ret
    simp only [parallelNext]
    rw [if_pos finalValid]⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, result, ?_⟩
    · rw [frame.nextRef]; rfl
    · rw [frame.nextObject]; rfl
    · rw [frame.objects]; rfl
    · rw [frame.clocks]; rfl
    · rw [frame.nextCollection]; rfl
    · rw [frame.collections]; rfl
    · intro ref old
      rw [frame.read_other (by omega : ref ≠ h.nextRef)]
      funext i
      simp [allocated, Heap.read, Heap.allocate, show ref ≠ h.nextRef by omega]
    · intro i outside
      rw [frame.outside _ _ (Or.inr (by simpa using outside))]
      simp [allocated, Heap.read, Heap.allocate]
  · simp only [Cost.work_seq, Cost.one]
    omega
  · simp only [Cost.span_seq, Cost.one]
    omega

-- Main result: Correctness
/-- Termination, sortedness, exact input multiplicities, fresh output, and
preservation follow from the same completed ordinary source call. -/
theorem correctness (h : Heap) (a : SeqRef) (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat)
    (valid : a < h.nextRef)
    (firstSorted : (interval (h.read a) lo1 m).Pairwise (· ≤ ·))
    (secondSorted : (interval (h.read a) lo2 n).Pairwise (· ≤ ·)) :
    ∃ final output, parallel_merge.Call h (a,lo1,↑m,lo2,↑n) final output ∧
      Postcondition h final a output lo1 m lo2 n := by
  obtain ⟨final, output, cost, access, run, result, _, _⟩ :=
    call_contract h a lo1 m lo2 n valid firstSorted secondSorted
  exact ⟨final, output, run.call, result⟩

/-- Every completed parallel call has the specified result and storage effects. -/
theorem correctness_of_parallel_call (h : Heap) (a : SeqRef) (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat)
    (valid : a < h.nextRef)
    (firstSorted : (interval (h.read a) lo1 m).Pairwise (· ≤ ·))
    (secondSorted : (interval (h.read a) lo2 n).Pairwise (· ≤ ·))
    {final : Heap} {output : SeqRef} {cost : Cost} {access : Access}
    (run : parallel_merge.ParallelCall h (a,lo1,↑m,lo2,↑n) final output cost access) :
    Postcondition h final a output lo1 m lo2 n := by
  obtain ⟨other,value,measured,accesses,witness,result,_,_⟩ :=
    call_contract h a lo1 m lo2 n valid firstSorted secondSorted
  have equal := witness.2.deterministic run.2
  have outputEqual := Algo2LeanGenerated.Result.fn_parallel_merge.inj equal.2.1
  simpa only [equal.1, outputEqual] using result

/-- Concrete bounds include the allocating wrapper and its call/return steps. -/
theorem running_time_explicit (h : Heap) (a : SeqRef) (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat)
    (valid : a < h.nextRef)
    (firstSorted : (interval (h.read a) lo1 m).Pairwise (· ≤ ·))
    (secondSorted : (interval (h.read a) lo2 n).Pairwise (· ≤ ·))
    {final : Heap} {output : SeqRef} {cost : Cost} {access : Access}
    (run : parallel_merge.ParallelCall h (a,lo1,↑m,lo2,↑n) final output cost access) :
    cost.work ≤ 1024*(m+n+1)+14 ∧ cost.span ≤ 4096*(Nat.log2 (m+n+1)+1)^2+14 := by
  obtain ⟨other,value,measured,accesses,witness,result,work,span⟩ :=
    call_contract h a lo1 m lo2 n valid firstSorted secondSorted
  have equal := run.2.deterministic witness.2
  rw [equal.2.2.1]
  exact ⟨work,span⟩

-- Main result: Running time
/-- One positive constant gives linear work and quadratic-logarithmic span for
all valid sorted inputs, including an empty pair of intervals. -/
theorem running_time : ∃ C : Nat, 0 < C ∧
    ∀ (h : Heap) (a : SeqRef) (lo1 : Int) (m : Nat) (lo2 : Int) (n : Nat),
    a < h.nextRef → (interval (h.read a) lo1 m).Pairwise (· ≤ ·) →
    (interval (h.read a) lo2 n).Pairwise (· ≤ ·) →
    ∀ {final : Heap} {output : SeqRef} {cost : Cost} {access : Access},
    parallel_merge.ParallelCall h (a,lo1,↑m,lo2,↑n) final output cost access →
    cost.work ≤ C*(m+n+1) ∧ cost.span ≤ C*(Nat.log2 (m+n+1)+1)^2 := by
  refine ⟨8192, by decide, ?_⟩
  intro h a lo1 m lo2 n valid first second final output cost access run
  have bound := running_time_explicit h a lo1 m lo2 n valid first second run
  have positive : 1 ≤ (Nat.log2 (m+n+1)+1)^2 := Nat.one_le_pow _ _ (by omega)
  constructor <;> omega

end ParallelMergePublic

namespace ParallelMergeSortPublic

/-- Sorted permutation at the original interval, two fresh buffer allocations,
and preservation of all earlier sequences, objects, collections, and clocks. -/
structure Postcondition (before after : Heap) (a output : SeqRef) (lo : Int) (n : Nat) : Prop
    extends ParallelAllocated.FreshOutput before after output 2 where
  sorted : SortResult (interval (before.read a) lo n) (interval (after.read output) lo n)
  outside : ∀ i, i < lo ∨ lo + n ≤ i → after.read output i = 0

/-- Allocate both buffers before entering parallel recursion. The sort proof
reuses the already proved merge contract, without assumptions about its code. -/
theorem call_contract (h : Heap) (a : SeqRef) (lo : Int) (n : Nat) (valid : a < h.nextRef) :
    ∃ final output cost access,
      parallel_merge_sort.ParallelCall h (a,lo,↑n) final output cost access ∧
      Postcondition h final a output lo n ∧
      cost.work ≤ 4224*(n+1)*(Nat.log2 (n+1)+1)+15 ∧
      cost.span ≤ 131392*(Nat.log2 (n+1)+1)^3+15 := by
  let allocated := (h.allocate (fun _ => 0)).allocate (fun _ => 0)
  have next : allocated.nextRef = h.nextRef+2 := by rfl
  have ao : a ≠ h.nextRef := Nat.ne_of_lt valid
  have as_ : a ≠ h.nextRef+1 := Nat.ne_of_lt (Nat.lt_trans valid (Nat.lt_succ_self _))
  have source : allocated.read a = h.read a := by
    funext i
    simp [allocated, Heap.read, Heap.allocate, ao, as_]
  have an : a < allocated.nextRef := by rw [next]; exact Nat.lt_of_lt_of_le valid (by omega)
  have on : h.nextRef < allocated.nextRef := by rw [next]; omega
  have sn : h.nextRef+1 < allocated.nextRef := by rw [next]; omega
  have os : h.nextRef ≠ h.nextRef+1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  obtain ⟨final, measured, accesses, run, frame, result, work, span, within⟩ :=
    ParallelMergeSortAnalysis.sort_into_contract allocated a h.nextRef (h.nextRef+1) lo n
      an on sn ao as_ os
  rw [source] at result
  have finalValid : h.nextRef < final.nextRef := by rw [frame.nextRef, next]; omega
  refine ⟨final, h.nextRef, _, _, ⟨valid, by
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
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.call
    · rfl
    · exact run.2
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.ret
    simp only [parallelNext]
    rw [if_pos finalValid]⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, result, ?_⟩
    · rw [frame.nextRef, next]
    · rw [frame.nextObject]; rfl
    · rw [frame.objects]; rfl
    · rw [frame.clocks]; rfl
    · rw [frame.nextCollection]; rfl
    · rw [frame.collections]; rfl
    · intro ref old
      rw [frame.read_other (by omega : ref ≠ h.nextRef) (by omega : ref ≠ h.nextRef+1)]
      funext i
      simp [allocated, Heap.read, Heap.allocate, show ref ≠ h.nextRef by omega,
        show ref ≠ h.nextRef+1 by omega]
    · intro i outside
      rw [frame.outside _ _ (Or.inr outside)]
      simp [allocated, Heap.read, Heap.allocate]
  · simp only [Cost.work_seq, Cost.one]
    have bound := Nat.le_trans work (sortWork_nlog n)
    omega
  · simp only [Cost.span_seq, Cost.one]
    have bound := Nat.le_trans span (sortSpan_logcubed n)
    omega

-- Main result: Correctness
/-- The complete algorithm terminates and returns a fresh sorted permutation,
while preserving the input and every caller-owned storage object and clock. -/
theorem correctness (h : Heap) (a : SeqRef) (lo : Int) (n : Nat) (valid : a < h.nextRef) :
    ∃ final output, parallel_merge_sort.Call h (a,lo,↑n) final output ∧
      Postcondition h final a output lo n := by
  obtain ⟨final,output,cost,access,run,result,_,_⟩ := call_contract h a lo n valid
  exact ⟨final,output,run.call,result⟩

/-- Every completed parallel call satisfies the sorting and preservation contract. -/
theorem correctness_of_parallel_call (h : Heap) (a : SeqRef) (lo : Int) (n : Nat) (valid : a < h.nextRef)
    {final : Heap} {output : SeqRef} {cost : Cost} {access : Access}
    (run : parallel_merge_sort.ParallelCall h (a,lo,↑n) final output cost access) :
    Postcondition h final a output lo n := by
  obtain ⟨other,value,measured,accesses,witness,result,_,_⟩ := call_contract h a lo n valid
  have equal := witness.2.deterministic run.2
  have outputEqual := Algo2LeanGenerated.Result.fn_parallel_merge_sort.inj equal.2.1
  simpa only [equal.1, outputEqual] using result

/-- Explicit bounds retain the cost of both allocations and the wrapper call. -/
theorem running_time_explicit (h : Heap) (a : SeqRef) (lo : Int) (n : Nat) (valid : a < h.nextRef)
    {final : Heap} {output : SeqRef} {cost : Cost} {access : Access}
    (run : parallel_merge_sort.ParallelCall h (a,lo,↑n) final output cost access) :
    cost.work ≤ 4224*(n+1)*(Nat.log2 (n+1)+1)+15 ∧
    cost.span ≤ 131392*(Nat.log2 (n+1)+1)^3+15 := by
  obtain ⟨other,value,measured,accesses,witness,result,work,span⟩ := call_contract h a lo n valid
  have equal := run.2.deterministic witness.2
  rw [equal.2.2.1]
  exact ⟨work,span⟩

-- Main result: Running time
/-- A single positive constant bounds work by `(n+1) log(n+1)` and span by a
cubic logarithm, with additive ones covering the empty and singleton inputs. -/
theorem running_time : ∃ C : Nat, 0 < C ∧
    ∀ (h : Heap) (a : SeqRef) (lo : Int) (n : Nat), a < h.nextRef →
    ∀ {final : Heap} {output : SeqRef} {cost : Cost} {access : Access},
    parallel_merge_sort.ParallelCall h (a,lo,↑n) final output cost access →
    cost.work ≤ C*(n+1)*(Nat.log2 (n+1)+1) ∧
    cost.span ≤ C*(Nat.log2 (n+1)+1)^3 := by
  refine ⟨262144, by decide, ?_⟩
  intro h a lo n valid final output cost access run
  have bound := running_time_explicit h a lo n valid run
  have product : 0 < (n+1)*(Nat.log2 (n+1)+1) := Nat.mul_pos (by omega) (by omega)
  have cube : 1 ≤ (Nat.log2 (n+1)+1)^3 := Nat.one_le_pow _ _ (by omega)
  constructor
  · simp only [Nat.mul_assoc] at bound ⊢
    omega
  · omega

end ParallelMergeSortPublic
