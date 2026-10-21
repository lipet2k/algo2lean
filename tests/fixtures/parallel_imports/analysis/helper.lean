import Algo.helper.Parallel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ImportedWrite
open Algo2LeanGenerated Algo2LeanParallel Algo.helper Algo.helper.Algo2LeanGenerated

def updated (heap : Heap) (a : SeqRef) (index value : Int) : Heap :=
  (heap.write a index value).tick "updates"

/-- One proved call retains its mutation, counter increment, work/span and accesses. -/
theorem write_call (heap : Heap) (a : SeqRef) (index value : Int) (valid : a < heap.nextRef) :
    write.ParallelCall heap (a, index, value) (updated heap a index value) value
      ⟨4, 4⟩ (Access.writeSeq a index) := by
  have execution := Eval.step (next := parallelNext) (h := heap)
    (f := entry_write (a, index, value))
    (show parallelNext heap (entry_write (a, index, value)) =
      .step (heap.write a index value) (.fn_write 3 {v0 := a, v1 := index, v2 := value})
        (Access.writeSeq a index) by simp [parallelNext, entry_write, valid])
    (Eval.step rfl (Eval.step rfl (Eval.ret rfl)))
  exact ⟨valid, by simpa [entry_write, updated, Access.union, Access.empty, Access.writeSeq, Access.write,
    Cost.seq, Cost.one] using execution⟩

end ImportedWrite
#print axioms ImportedWrite.write_call
