import Algo.helper.Generated

/-! A deterministic storage/cost proof with no probability dependency. -/
namespace HelperAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo.helper Algo.helper.Algo2LeanGenerated

def updated (heap : Heap) (a : SeqRef) : Heap :=
  (heap.write a 0 (heap.read a 0 + 1)).tick "updates"

/-- One shared cell changes, all other storage remains intact, and the counter
increases from its actual initial value. The explicit final heap records all
these guarantees in the same reusable call. -/
theorem bump_call (heap : Heap) (a : SeqRef) (valid : a < heap.nextRef) :
    bump.Call heap a (updated heap a) (heap.read a 0 + 1) := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.bump_pc4 _ _ _ ⟨valid, valid⟩)
  apply Reaches.prepend (Step.bump_pc3 ..)
  apply Reaches.prepend (Step.bump_pc2 _ _ _ valid)
  simpa [updated, Heap.read, Heap.write, Heap.tick] using
    Reaches.single (Step.bump_pc1
      (updated heap a) {v0 := a, t1 := heap.read a 0 + 1} stack)

end HelperAnalysis
