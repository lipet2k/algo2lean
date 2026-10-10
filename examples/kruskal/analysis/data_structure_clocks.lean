import Algo.union_find.Generated
import Algo.sort_indices.Generated
import Algo2LeanLib.CallCost

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock monotonicity certificates for reusable union-find and sorting components.
Imported algorithms retain their own certificates; client proofs only compose them.
-/

namespace DataStructureClocks

open Algo2LeanCore Algo2LeanGenerated

@[simp] theorem resume_heap {Frame Result : Type} (heap : Heap)
    (result : Result) (caller : Stack Frame Result) :
    (resumeConfig heap result caller).heap = heap := by
  cases caller <;> rfl

/-- The binary heap's arithmetic, mutation, and explicit ticks never lower a clock. -/
theorem heap_step {before after : Algo.indexed_heap.Algo2LeanGenerated.Configuration}
    (transition : Algo.indexed_heap.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> intro clock
  all_goals try simp only [resume_heap]
  all_goals simp [Config.heap, Heap.tick,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_vertices,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_positions,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_keys,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_size] <;> split <;> omega

/-- The union-find implementation preserves clock monotonicity through recursion. -/
theorem union_find_step {before after : Algo.union_find.Algo2LeanGenerated.Configuration}
    (transition : Algo.union_find.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> intro clock
  all_goals try simp only [resume_heap]
  all_goals simp [Config.heap, Heap.tick,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_parent,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_rank,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_size] <;> split <;> omega

/-- Sorting reuses the binary heap certificate at imported transitions. -/
theorem sort_step {before after : Algo.sort_indices.Algo2LeanGenerated.Configuration}
    (transition : Algo.sort_indices.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> try solve
    | intro clock
      try simp only [resume_heap, ModuleCall.heap]
      simp [Config.heap, Heap.tick] <;> split <;> omega
  case import_0 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! heap_step delegated

end DataStructureClocks
