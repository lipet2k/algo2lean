import MutableSequencesGenerated

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `overwrite_summary`: Reusable sequence-write contract.
- `parameter_mutation_summary`: Aliased and distinct parameter behavior.
- `ordinary_inputs_are_independent`: Independent ordinary-value inputs.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace MutableSequencesAnalysis

-- The caller receives the new heap. The object keeps its identity, and the
-- returned integer is the value just written, at any integer index.
theorem overwrite_summary (heap : Heap) (object : SeqRef) (index value : Int)
    (allocated : object < heap.nextRef) :
    overwrite.Call heap (object, index, value)
      (heap.write object index value) value := by
  refine ⟨allocated, ?_⟩
  intro stack
  apply Reaches.prepend (Step.overwrite_pc3 _ _ _ allocated)
  apply Reaches.prepend (Step.overwrite_pc2 _ _ _ allocated)
  simpa using Reaches.single (Step.overwrite_pc1 (heap.write object index value)
    { v0 := object, v1 := index, v2 := value,
      t3 := (heap.write object index value).read object index } stack)

-- Main result: Correctness
theorem overwrite_returns_value (contents : Algo2LeanGenerated.Seq) (index value : Int) :
    overwrite.Returns (contents, index, value) value := by
  let heap := ({} : Heap).allocate contents
  have summary := overwrite_summary heap 0 index value (by simp [heap, Heap.allocate])
  exact ⟨heap.write 0 index value, summary.1, summary.2.root⟩

-- A single general statement covers both shared and independent parameters:
-- b observes the write exactly when a and b denote the same object.
theorem parameter_mutation_summary (heap : Heap) (a b : SeqRef)
    (aAllocated : a < heap.nextRef) (bAllocated : b < heap.nextRef) :
    aliased_parameters.Call heap (a, b) (heap.write a 0 11)
      (if b = a then 11 else heap.read b 0) := by
  refine ⟨⟨aAllocated, bAllocated⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.aliased_parameters_pc3 _ _ _ aAllocated)
  apply Reaches.prepend (Step.aliased_parameters_pc2 _ _ _ bAllocated)
  simpa [Heap.read, Heap.write] using
    Reaches.single (Step.aliased_parameters_pc1 (heap.write a 0 11)
      { v0 := a, v1 := b, t2 := (heap.write a 0 11).read b 0 } stack)

theorem shared_parameters_observe_write (heap : Heap) (object : SeqRef)
    (allocated : object < heap.nextRef) :
    aliased_parameters.Call heap (object, object) (heap.write object 0 11) 11 := by
  have summary := parameter_mutation_summary heap object object allocated allocated
  simp only [ite_true] at summary
  exact summary

theorem separate_parameters_preserve_read (heap : Heap) (a b : SeqRef)
    (aAllocated : a < heap.nextRef) (bAllocated : b < heap.nextRef) (distinct : b ≠ a) :
    aliased_parameters.Call heap (a, b) (heap.write a 0 11) (heap.read b 0) := by
  have summary := parameter_mutation_summary heap a b aAllocated bAllocated
  simp only [if_neg distinct] at summary
  exact summary

-- Value inputs allocate separate objects, even when their contents are equal.
theorem ordinary_inputs_are_independent (xs ys : Algo2LeanGenerated.Seq) :
    aliased_parameters.Returns (xs, ys) (ys 0) := by
  let heap := (({} : Heap).allocate xs).allocate ys
  have execution := separate_parameters_preserve_read heap 0 1
    (by simp [heap, Heap.allocate]) (by simp [heap, Heap.allocate]) (by decide)
  refine ⟨heap.write 0 0 11, ?_⟩
  simpa [heap, Heap.read, Heap.allocate] using! execution.run

end MutableSequencesAnalysis
