import Algo.client.Parallel
import Algo.helper.Analysis

namespace ImportedPair
open Algo2LeanGenerated Algo2LeanParallel Algo.client Algo.client.Algo2LeanGenerated
open ImportedWrite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4096

/-- The imported helper proof is reused twice without unfolding its code. -/
theorem pair_call (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef) :
    ∃ cost access, pair.ParallelCall heap a (updated (updated heap a (-1) 7) a 3 9)
      (7, 9) cost access ∧ cost.work = 22 ∧ cost.span = 16 := by
  have left := write_call heap a (-1) 7 valid
  have right := write_call (updated heap a (-1) 7) a 3 9 valid
  exact ⟨_, _, ⟨valid, by
    repeat (apply Eval.step (by rfl))
    apply Eval.fork (by rfl)
    · repeat (apply Eval.step (by rfl))
      apply Eval.invoke (by rfl)
      · exact ⟨_, left.2, rfl⟩
      · exact Eval.ret rfl
    · repeat (apply Eval.step (by rfl))
      apply Eval.invoke (by rfl)
      · exact ⟨_, right.2, rfl⟩
      · exact Eval.ret rfl
    · constructor <;> simp [Access.union, Access.empty, Access.writeSeq, Access.write]
    · apply Eval.step (by rfl)
      exact Eval.ret rfl⟩, rfl, rfl⟩

/-- Named counters are increments from the caller's actual initial heap. -/
theorem updates (heap : Heap) (a : SeqRef) :
    Heap.cost heap (updated (updated heap a (-1) 7) a 3 9) "updates" = 2 := by
  simp [updated, Heap.cost, Heap.write, Heap.tick, Nat.add_assoc]

end ImportedPair
#print axioms ImportedPair.pair_call
#print axioms ImportedPair.updates
