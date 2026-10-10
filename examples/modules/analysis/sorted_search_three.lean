import Algo.sorted_search_three.Generated
import Algo.sorted_search_three.Facts
import Algo.sort_three.Analysis
import Algo.lower_bound_three.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `summary`: Reusable sort-and-search contract.
- `terminates`: Termination.
- `correct`: Sorted insertion-position correctness.
- `comparisons_le_six`: At most six comparisons.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.sorted_search_three

namespace SortedSearchThreeAnalysis

open SortThreeAnalysis LowerBoundThreeAnalysis

/-- The caller combines existing summaries. Its proof neither inspects sorting
    comparisons nor rechecks the search's branches. -/
theorem summary (heap : Heap) (ref : SeqRef) (first key : Int) (valid : ref < heap.nextRef) :
    sorted_search_three.Call heap (ref, first, key)
      ((sortedHeap heap ref first).tick "search_comparisons"
        (comparisons (sortedHeap heap ref first) ref first key))
      (position (sortedHeap heap ref first) ref first key) := by
  open Algo.sorted_search_three.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.sorted_search_three_pc8 _ _ caller)
    apply Reaches.prepend (Step.sorted_search_three_pc7 _ _ caller)
    apply Reaches.prepend (Step.sorted_search_three_pc6 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller
      (SortThreeAnalysis.summary heap ref first valid).2).trans
    apply Reaches.prepend (Step.sorted_search_three_pc5 _ _ caller)
    apply Reaches.prepend (Step.sorted_search_three_pc4 _ _ caller)
    apply Reaches.prepend (Step.sorted_search_three_pc3 _ _ caller)
    apply Reaches.prepend (Step.sorted_search_three_pc2 _ _ caller)
    apply (ModuleCall.summary import_2_simulates _ caller
      (LowerBoundThreeAnalysis.summary (sortedHeap heap ref first) ref first key
        (by simpa using valid)).2).trans
    exact Reaches.single (Step.sorted_search_three_pc1 _ _ caller)

/-- The source-facing specification explicitly concerns exactly three entries.
    All other entries, including other sequence objects, retain their contents. -/
def Correct (before after : Heap) (ref : SeqRef) (first key result : Int) : Prop :=
  Sorted after ref first ∧
  (values after ref first).Perm (values before ref first) ∧
  LowerBound after ref first key result ∧
  Heap.cost before after "sort_comparisons" = 3 ∧
  Heap.cost before after "search_comparisons" ≤ 3 ∧
  (∀ other index, other ≠ ref ∨ index < first ∨ first + 3 ≤ index →
    after.read other index = before.read other index)

/-- Termination, sorting, searching, mutation and cost refer to one execution. -/
theorem terminates (heap : Heap) (ref : SeqRef) (first key : Int) (valid : ref < heap.nextRef) :
    ∃ after result, sorted_search_three.Run heap (ref, first, key) after result :=
  ⟨_, _, (summary heap ref first key valid).run⟩

-- Main result: Correctness
/-- The imported correctness and cost facts apply to every completed execution,
    starting from any heap and any existing clock values. -/
theorem correct {heap after : Heap} {ref : SeqRef} {first key result : Int}
    (execution : sorted_search_three.Run heap (ref, first, key) after result) :
    Correct heap after ref first key result := by
  obtain ⟨sameHeap, sameResult⟩ := execution.eq_of_call (summary heap ref first key execution.1)
  subst after
  subst result
  have sorting := SortThreeAnalysis.sorted_permutation heap ref first
  have searching := LowerBoundThreeAnalysis.lower_bound (sortedHeap heap ref first) ref first key sorting.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Sorted] using sorting.1
  · simpa [values] using sorting.2
  · simpa [LowerBound] using searching
  · simp [Heap.cost, Heap.tick, SortThreeAnalysis.clocks]
  · simpa [Heap.cost, Heap.tick, SortThreeAnalysis.clocks] using
      (LowerBoundThreeAnalysis.comparison_bound (sortedHeap heap ref first) ref first key).2
  · intro other index outside
    simpa using SortThreeAnalysis.untouched heap ref other first index outside

-- Main result: Running time
/-- The two imported comparison budgets sum to at most six. -/
theorem comparisons_le_six {heap after : Heap} {ref : SeqRef} {first key result : Int}
    (execution : sorted_search_three.Run heap (ref, first, key) after result) :
    Heap.cost heap after "sort_comparisons" + Heap.cost heap after "search_comparisons" ≤ 6 := by
  have specification := correct execution
  have sorting := specification.2.2.2.1
  have searching := specification.2.2.2.2.1
  omega

/-- The component clocks compose without changing unrelated counters. -/
theorem other_clocks {heap after : Heap} {ref : SeqRef} {first key result : Int}
    (execution : sorted_search_three.Run heap (ref, first, key) after result)
    (clock : String) (notSort : clock ≠ "sort_comparisons")
    (notSearch : clock ≠ "search_comparisons") : after.clocks clock = heap.clocks clock := by
  obtain ⟨sameHeap, _⟩ := execution.eq_of_call (summary heap ref first key execution.1)
  rw [sameHeap]
  simp [Heap.tick, SortThreeAnalysis.clocks, notSort, notSearch]

end SortedSearchThreeAnalysis
