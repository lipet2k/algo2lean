import upsweep
import prefix_sum

/-!
Exclusive prefix sums: correctness and linear-work/logarithmic-span bounds.

The complete generated source allocates separate scratch and output sequences,
reuses the two traversal contracts, and returns a fresh result. Existing
caller storage and counters survive. The bounds count generated primitive
instructions and fork/join operations under the declared abstract cost model.
They apply to every nonnegative length, including empty and odd-sized inputs.
-/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Algo2LeanGenerated Algo2LeanParallel Algo2Lean.ParallelBounds

namespace ParallelPrefix

/-- Public result and preservation contract for a complete prefix-sum call. -/
structure PrefixResult (before after : Heap) (source output : SeqRef) (lo : Int) (n : Nat) : Prop where
  output_ref : output = before.nextRef + 1
  allocation : after.nextRef = before.nextRef + 2
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  clocks : after.clocks = before.clocks
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections
  caller_sequences : ∀ ref, ref < before.nextRef → after.read ref = before.read ref
  prefixes : IsExclusivePrefixSum (before.read source) (after.read output) lo n
  outside : ∀ i, i < lo ∨ lo + ↑n ≤ i → after.read output i = 0

private theorem work_bound (n u d : Nat) (hu : u ≤ 24 * nodes n) (hd : d ≤ 24 * nodes n) :
    u + d + 21 ≤ 128 * (n + 1) := by
  have := nodes_le_linear n
  omega

private theorem span_bound (n u d : Nat) (hu : u ≤ 24 * height n) (hd : d ≤ 24 * height n) :
    u + d + 21 ≤ 128 * (Nat.log2 n + 1) := by
  have := height_le_logarithmic n
  omega

/-- Both passes compose through their public contracts. Correctness,
preservation, and work/span refer to this same completed source execution. -/
theorem call_contract (h : Heap) (a : SeqRef) (lo : Int) (n : Nat)
    (valid : a < h.nextRef) :
    ∃ final output cost access,
      prefix_sum.ParallelCall h (a, lo, ↑n) final output cost access ∧
      PrefixResult h final a output lo n ∧
      cost.work ≤ 128 * (n + 1) ∧ cost.span ≤ 128 * (Nat.log2 n + 1) := by
  let allocated := (h.allocate (fun _ => 0)).allocate (fun _ => 0)
  have allocatedNext : allocated.nextRef = h.nextRef + 2 := by rfl
  have aScratch : a ≠ h.nextRef := Nat.ne_of_lt valid
  have aOutput : a ≠ h.nextRef + 1 := Nat.ne_of_lt (Nat.lt_trans valid (Nat.lt_succ_self _))
  have sourcePreserved : allocated.read a = h.read a := by
    funext i
    simp [allocated, Heap.read, Heap.allocate, aScratch, aOutput]
  have allocatedSource : a < allocated.nextRef := by
    rw [allocatedNext]
    exact Nat.lt_of_lt_of_le valid (by omega)
  have allocatedScratch : h.nextRef < allocated.nextRef := by rw [allocatedNext]; omega
  obtain ⟨middle, uc, ua, up, uf, tree, rootTotal, uw, us, ur⟩ :=
    upsweep_contract allocated a h.nextRef lo n allocatedSource allocatedScratch aScratch
  rw [sourcePreserved] at up tree rootTotal
  have scratchValid : h.nextRef < middle.nextRef := by rw [uf.nextRef, allocatedNext]; omega
  have outputValid : h.nextRef + 1 < middle.nextRef := by rw [uf.nextRef, allocatedNext]; omega
  obtain ⟨final, dc, da, down, df, prefixes, dw, ds, dr⟩ :=
    downsweep_contract middle h.nextRef (h.nextRef + 1) (h.read a) lo n 0
      scratchValid outputValid (Nat.ne_of_lt (Nat.lt_succ_self _)) tree
  have finalNext : final.nextRef = h.nextRef + 2 := by rw [df.nextRef, uf.nextRef, allocatedNext]
  have finalValid : h.nextRef + 1 < final.nextRef := by rw [finalNext]; omega
  refine ⟨final, h.nextRef + 1, _, _, ⟨valid, by
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
    · exact up.2
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
    · exact down.2
    apply Eval.step
    · rfl
    apply Eval.step
    · rfl
    apply Eval.ret
    simp only [parallelNext, Heap.allocate]
    rw [if_pos finalValid]⟩, ?_, ?_, ?_⟩
  · refine ⟨rfl, finalNext, ?_, ?_, ?_, ?_, ?_, ?_, prefixes, ?_⟩
    · rw [df.nextObject, uf.nextObject]; rfl
    · rw [df.objects, uf.objects]; rfl
    · rw [df.clocks, uf.clocks]; rfl
    · rw [df.nextCollection, uf.nextCollection]; rfl
    · rw [df.collections, uf.collections]; rfl
    · intro ref old
      rw [df.read_other (by omega : ref ≠ h.nextRef + 1), uf.read_other (by omega : ref ≠ h.nextRef)]
      funext i
      simp [allocated, Heap.read, Heap.allocate, show ref ≠ h.nextRef by omega,
        show ref ≠ h.nextRef + 1 by omega]
    · intro i outside
      rw [df.outside _ _ (Or.inr outside), uf.outside (h.nextRef + 1) i (Or.inl (Nat.ne_of_gt (Nat.lt_succ_self _)))]
      simp [allocated, Heap.read, Heap.allocate]
  · simp only [Cost.work_seq, Cost.one]
    have bound := work_bound n uc.work dc.work uw dw
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
  · simp only [Cost.span_seq, Cost.one]
    have bound := span_bound n uc.span dc.span us ds
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

-- Main result: Correctness
/-- The generated algorithm returns exclusive prefixes in a fresh sequence,
while preserving every caller-owned sequence, object, collection, and clock. -/
theorem correctness (h : Heap) (a : SeqRef) (lo : Int) (n : Nat)
    (valid : a < h.nextRef) :
    ∃ final output, prefix_sum.Call h (a, lo, ↑n) final output ∧
      PrefixResult h final a output lo n := by
  obtain ⟨final, output, cost, access, run, result, _, _⟩ := call_contract h a lo n valid
  exact ⟨final, output, run.call, result⟩

/-- Every completed parallel execution has linear work and logarithmic span.
The explicit constants also cover the empty input; all costs use the same
execution as the returned prefixes and preservation theorem. -/
theorem running_time_explicit (h : Heap) (a : SeqRef) (lo : Int) (n : Nat)
    (valid : a < h.nextRef) {final : Heap} {output : SeqRef} {cost : Cost} {access : Access}
    (run : prefix_sum.ParallelCall h (a, lo, ↑n) final output cost access) :
    cost.work ≤ 128 * (n + 1) ∧ cost.span ≤ 128 * (Nat.log2 n + 1) := by
  obtain ⟨other, value, measured, accesses, witness, _, work, span⟩ := call_contract h a lo n valid
  have equal := run.2.deterministic witness.2
  rw [equal.2.2.1]
  exact ⟨work, span⟩

/-- The public preservation and prefix specification holds for every
completed parallel call, not merely for the constructed execution witness. -/
theorem correctness_of_parallel_call (h : Heap) (a : SeqRef) (lo : Int) (n : Nat)
    (valid : a < h.nextRef) {final : Heap} {output : SeqRef} {cost : Cost} {access : Access}
    (run : prefix_sum.ParallelCall h (a, lo, ↑n) final output cost access) :
    PrefixResult h final a output lo n := by
  obtain ⟨other, value, measured, accesses, witness, result, _, _⟩ := call_contract h a lo n valid
  have equal := witness.2.deterministic run.2
  have outputEqual := Result.fn_prefix_sum.inj equal.2.1
  simpa only [equal.1, outputEqual] using result

-- Main result: Running time
/-- One positive constant works uniformly for every input, initial heap, and
completed parallel call. Work is linear and span logarithmic in the length. -/
theorem running_time : ∃ C : Nat, 0 < C ∧
    ∀ (h : Heap) (a : SeqRef) (lo : Int) (n : Nat), a < h.nextRef →
    ∀ {final : Heap} {output : SeqRef} {cost : Cost} {access : Access},
      prefix_sum.ParallelCall h (a, lo, ↑n) final output cost access →
      cost.work ≤ C * (n + 1) ∧ cost.span ≤ C * (Nat.log2 n + 1) := by
  refine ⟨128, by decide, ?_⟩
  intro h a lo n valid final output cost access run
  exact running_time_explicit h a lo n valid run

/-- Existing clients can use integer lengths under the usual nonnegativity
precondition without converting the representation of their input sequence. -/
theorem integer_call_contract (h : Heap) (a : SeqRef) (lo n : Int)
    (valid : a < h.nextRef) (nonnegative : 0 ≤ n) :
    ∃ final output cost access,
      prefix_sum.ParallelCall h (a, lo, n) final output cost access ∧
      PrefixResult h final a output lo n.toNat ∧
      cost.work ≤ 128 * (n.toNat + 1) ∧ cost.span ≤ 128 * (Nat.log2 n.toNat + 1) := by
  simpa only [Int.toNat_of_nonneg nonnegative] using call_contract h a lo n.toNat valid

end ParallelPrefix
