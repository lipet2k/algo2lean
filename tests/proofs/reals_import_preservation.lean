import Algo.realclient.Generated
import Algo.integer.Analysis

open Algo2LeanCore Algo2LeanGenerated

namespace RealPreservation
open Algo.realclient Algo.realclient.Algo2LeanGenerated

/-- Reuse the original integer contract on the actual heap containing real data. -/
theorem preserve_call (heap : Heap) (data : CollectionRef) (values : SeqRef)
    (index : Int) (output : ℝ)
    (valid : preserve.ValidInput heap (data, values, index))
    (observed : seq_Real.get heap data 0 = some output) :
    preserve.Call heap (data, values, index)
      ((heap.write values index (heap.read values index + 1)).tick "work") output := by
  have unchanged : seq_Real.get
      ((heap.write values index (heap.read values index + 1)).tick "work") data 0 =
        some output := observed
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.preserve_pc5 heap { v0 := data, v1 := values, v2 := index } caller)
  apply Reaches.prepend (Step.preserve_pc4 _ _ caller)
  apply Reaches.prepend (Step.preserve_pc3 _ _ caller)
  apply (ModuleCall.summary import_0_simulates _ caller
    (IntegerHelper.increment_call heap values index valid.2).2).trans
  apply Reaches.prepend (Step.preserve_pc2 _ _ caller (by simp [unchanged]))
  rw [unchanged]
  exact Reaches.single (Step.preserve_pc1 _ _ caller)

/-- The reused contract preserves every real element and retains the caller's counters. -/
theorem preserve_effects (heap : Heap) (data : CollectionRef) (values : SeqRef)
    (index : Int) (output : ℝ)
    (valid : preserve.ValidInput heap (data, values, index))
    (observed : seq_Real.get heap data 0 = some output) :
    ∃ after, preserve.Call heap (data, values, index) after output ∧
      (∀ position, seq_Real.get after data position = seq_Real.get heap data position) ∧
      after.clocks "work" = heap.clocks "work" + 1 := by
  refine ⟨_, preserve_call heap data values index output valid observed, ?_, ?_⟩
  · intro position
    rfl
  · simp

end RealPreservation
