import SequencesGenerated

/-!
Analysis outline:
- `replace_summary`: Reusable element-replacement contract.
- `replace_contents`: Returned sequence contains the update.
- `replace_preserves_other_indices`: Unchanged indices retain their values.
- `negative_index_reads_input`: Negative indices are ordinary indices.
- `distant_value_returns_argument`: Unbounded integer indexing.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace SequencesAnalysis

-- This summary keeps object identity and records the mutation of the heap.
-- It is reusable under any caller, at every integer index.
theorem replace_summary (heap : Heap) (object : SeqRef) (index value : Int)
    (allocated : object < heap.nextRef) :
    replace.Call heap (object, index, value)
      (heap.write object index value) object := by
  refine ⟨allocated, ?_⟩
  intro stack
  refine (Reaches.single (Step.replace_pc3 _ _ _ allocated)).trans ?_
  refine (Reaches.single (Step.replace_pc2 _ _ _)).trans ?_
  exact Reaches.single (Step.replace_pc1 _ _ _ allocated)

-- The ordinary value interface states the whole infinite returned sequence.
-- Main result: Correctness
theorem replace_contents (contents : Algo2LeanGenerated.Seq) (index value : Int) :
    replace.Returns (contents, index, value)
      (fun position => if position = index then value else contents position) := by
  let heap := ({} : Heap).allocate contents
  have summary := replace_summary heap 0 index value (by simp [heap, Heap.allocate])
  refine ⟨heap.write 0 index value, 0, ⟨summary.1, summary.2.root⟩, ?_⟩
  funext position
  simp [heap, Heap.allocate, Heap.write]

-- Updating one place leaves every other integer position unchanged, including
-- negative positions and positions arbitrarily far from zero.
theorem replace_preserves_other_indices (contents : Algo2LeanGenerated.Seq)
    (index value : Int) :
    ∃ result, replace.Returns (contents, index, value) result ∧
      result index = value ∧ ∀ position, position ≠ index → result position = contents position := by
  refine ⟨_, replace_contents contents index value, ?_, ?_⟩
  · simp
  · intro position different
    simp [different]

theorem negative_index_reads_input (contents : Algo2LeanGenerated.Seq) :
    negative_index.Returns contents (contents (-1)) := by
  let heap := ({} : Heap).allocate contents
  refine ⟨heap, (by simp [negative_index.ValidInput, negative_index.load, Heap.allocate]), ?_⟩
  refine (Reaches.single (Step.negative_index_pc2 _ _ _
    (by simp [negative_index.load, Heap.allocate]))).trans ?_
  simpa [heap, Heap.read, Heap.allocate] using
    Reaches.single (Step.negative_index_pc1 heap
      { v0 := 0, t1 := heap.read 0 (-1) } [])

-- A very large index introduces no machine-integer overflow or size bound.
theorem distant_value_returns_argument (value : Int) :
    distant_value.Returns value value := by
  refine ⟨(({} : Heap).allocate (fun _ => 0)).write 0
    100000000000000000000000000000000000000000000000000 value, True.intro, ?_⟩
  apply Reaches.prepend (Step.distant_value_pc6 ..)
  apply Reaches.prepend (Step.distant_value_pc5 ..)
  apply Reaches.prepend (Step.distant_value_pc4 ..)
  apply Reaches.prepend (Step.distant_value_pc3 _ _ _
    (by simp [distant_value.load, Heap.allocate]))
  apply Reaches.prepend (Step.distant_value_pc2 _ _ _
    (by simp [distant_value.load, Heap.allocate, Heap.write]))
  exact Reaches.single (Step.distant_value_pc1 _ _ [])

end SequencesAnalysis
