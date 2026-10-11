import Algo.kruskal_sorted.Generated
import Algo.data_structure_clocks.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock counters are monotone through every transition, including delegated calls.
These certificates make cost increments usable with arbitrary initial clocks.
They depend only on the compiled programs, not on graph or data-structure preconditions.
-/

namespace KruskalSortedClocks

open Algo2LeanCore Algo2LeanGenerated DataStructureClocks

/-- The post-sorting scan never decreases a clock, including within union-find calls. -/
theorem kruskal_sorted_step {before after : Algo.kruskal_sorted.Algo2LeanGenerated.Configuration}
    (transition : Algo.kruskal_sorted.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> try solve
    | intro clock
      try simp only [resume_heap, ModuleCall.heap]
      simp [Config.heap, Heap.tick] <;> split <;> omega
  case import_0 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! union_find_step delegated

/-- Every completed call has nonnegative increments, whatever counters its
    caller accumulated before invoking Kruskal. -/
theorem call_monotone {before after : Heap} {input result}
    (execution : Algo.kruskal_sorted.kruskal_sorted.Call before input after result) :
    before.ClocksMonotone after := by
  have preserved := execution.2.root.invariant (fun state => before.ClocksMonotone state.heap)
    (Heap.ClocksMonotone.refl before)
    (fun _ _ transition accumulated => accumulated.trans (kruskal_sorted_step transition))
  exact preserved

end KruskalSortedClocks
