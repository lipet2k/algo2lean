import Algo.kruskal_sorted.Analysis
import Algo.kruskal_clocks.Analysis
import Algo.kruskal.Facts
import Algo.kruskal_bounds.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's complete algorithm sorts edge identifiers, then calls the independently
verified sorted-edge entry point. The two runtime results distinguish the total
work from work after sorting. Both reuse the same union-by-rank and full path
compression contracts and apply from arbitrary caller counters.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
open KruskalInput

/-- The total of the eight source-event clocks, shared by both entry points. -/
abbrev runtime := KruskalSortedAnalysis.runtime

/-- Exact sorting budget plus the independently proved post-sorting budget. -/
noncomputable def runtimeBound (vertices edges : Nat) : Nat :=
  SortIndicesAnalysis.runtimeBound edges + KruskalSortedAnalysis.runtimeBound vertices edges

/-- The sorting term absorbs the inverse-Ackermann contribution. The constant
    unit covers empty inputs, while V retains the cost of isolated vertices. -/
def runtimeScale (vertices edges : Nat) : Nat :=
  vertices + 1 + edges * (edges + 1).log2

/-- One constant controls every finite graph, with no density assumption. -/
theorem runtimeBound_le (vertices edges : Nat) :
    runtimeBound vertices edges ≤ 44 * runtimeScale vertices edges := by
  simpa only [runtimeBound, runtimeScale, SortIndicesAnalysis.runtimeBound,
    KruskalSortedAnalysis.runtimeBound, Nat.add_assoc] using
    KruskalBounds.total_budget_le vertices edges

private theorem sorting_work {before after : Heap} {count : Int}
    (budget : SortIndicesAnalysis.Budget count (2 * count.toNat) before after) :
    SortIndicesAnalysis.runtime after.clocks ≤ SortIndicesAnalysis.runtime before.clocks +
      SortIndicesAnalysis.runtimeBound count.toNat := by
  have source := budget "sort_steps"
  have comparisons := budget "heap_comparisons"
  have swaps := budget "heap_swaps"
  simp [SortIndicesAnalysis.rate] at source comparisons swaps
  simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  have rates : 3 * (count.toNat + 1).log2 + 2 =
      1 + 2 * (count.toNat + 1).log2 + ((count.toNat + 1).log2 + 1) := by omega
  unfold SortIndicesAnalysis.runtimeBound
  rw [rates]
  simp only [BinaryModuleAnalysis.depth, Nat.mul_add, Nat.mul_one] at source comparisons swaps ⊢
  omega

private theorem sorting_preserves_work {before after : Heap}
    (preserved : SortIndicesAnalysis.Preserves before after) : work after.clocks = work before.clocks := by
  simp only [work, UnionFindAnalysis.work]
  rw [preserved.clocks "uf_init" (by decide) (by decide) (by decide),
    preserved.clocks "uf_find" (by decide) (by decide) (by decide),
    preserved.clocks "uf_compress" (by decide) (by decide) (by decide),
    preserved.clocks "uf_union" (by decide) (by decide) (by decide),
    preserved.clocks "kruskal" (by decide) (by decide) (by decide)]

/-- The sorter protects every previously allocated caller location. -/
private theorem sorting_footprint {before after : Heap}
    (preserved : SortIndicesAnalysis.Preserves before after) : before.Footprint after [] [] [] := by
  refine ⟨preserved.refs, preserved.objectRefs, by simp [preserved.collectionRefs], ?_, ?_, ?_, ?_, ?_⟩
  · intro ref old
    simp only [Heap.objectClass, preserved.objects ref old]
  · intro ref old
    simp only [Heap.sequenceType, preserved.collections]
  · intro ref old _
    exact preserved.sequences ref old
  · intro ref old _
    exact preserved.objects ref old
  · intro ref old _
    rw [preserved.collections]

/-- The two source calls compose without inspecting either implementation. -/
theorem kruskal_calls (heap sorted final : Heap) (size count : Int)
    (sources targets weights order chosen : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (sorting : Algo.sort_indices.sort_indices.Call heap (weights, count) sorted order)
    (scanning : Algo.kruskal_sorted.kruskal_sorted.Call sorted
      (size, sources, targets, weights, count, order) final chosen)
    (resultAllocated : chosen < final.nextRef) :
    kruskal.Call heap (size, sources, targets, weights, count) final chosen := by
  open Algo.kruskal.Algo2LeanGenerated in
    refine ⟨allocated, ?_⟩
    intro caller
    apply Reaches.prepend (Step.kruskal_pc12 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc11 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc10 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller sorting.2).trans
    apply Reaches.prepend (Step.kruskal_pc9 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc8 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc7 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc6 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc5 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc4 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc3 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc2 _ _ caller)
    apply (ModuleCall.summary import_3_simulates _ caller scanning.2).trans
    exact Reaches.single (Step.kruskal_pc1 _ _ caller resultAllocated)

/-- Weighted runtime adds across actual caller-relative counter increments. -/
theorem runtime_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    runtime after.clocks = runtime before.clocks + runtime costs :=
  KruskalSortedAnalysis.runtime_increments effect

/-- Every valid finite graph has a returning call selecting a minimum spanning
    forest. Sorting and the sorted-edge call preserve all existing caller data. -/
theorem call_complete (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef := by
  obtain ⟨sorted, order, sortCall, sortedIds, preserved, fresh, orderAllocated, budget⟩ :=
    SortIndicesAnalysis.call heap weights count allocated.2.2 input.count_nonnegative
  have sameSources := preserved.sequences sources allocated.1
  have sameTargets := preserved.sequences targets allocated.2.1
  have sameWeights := preserved.sequences weights allocated.2.2
  have sortedInput : WellFormed size count (sorted.read sources) (sorted.read targets) := by
    simpa only [sameSources, sameTargets] using input
  have sortedValid : Algo.kruskal_sorted.kruskal_sorted.ValidInput sorted
      (size, sources, targets, weights, count, order) :=
    ⟨Nat.lt_of_lt_of_le allocated.1 preserved.refs,
      Nat.lt_of_lt_of_le allocated.2.1 preserved.refs,
      Nat.lt_of_lt_of_le allocated.2.2 preserved.refs, orderAllocated⟩
  obtain ⟨final, chosen, selected, scanCall, minimum, flags, scanBound, frame, chosenFresh,
      chosenAllocated, clocks⟩ :=
    KruskalSortedAnalysis.call_complete sorted size count sources targets weights order
      sortedValid sortedInput (by simpa only [sameWeights] using sortedIds)
  rw [sameSources, sameTargets, sameWeights] at minimum
  refine ⟨final, chosen, selected,
    kruskal_calls heap sorted final size count sources targets weights order chosen
      allocated sortCall scanCall chosenAllocated,
    minimum, flags, ?_, (sorting_footprint preserved).trans frame,
    Nat.le_trans preserved.refs chosenFresh, chosenAllocated⟩
  have sortBound := sorting_work budget
  have unchangedWork := sorting_preserves_work preserved
  simp only [runtime, KruskalSortedAnalysis.runtime] at scanBound ⊢
  unfold runtimeBound
  rw [unchangedWork] at scanBound
  omega

/-- The reusable entry-point contract includes fresh output storage, preservation
    of every existing caller location, and the actual increments of all clocks.
    It applies unchanged when called from another algorithm with nonzero clocks. -/
theorem call_contract (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      heap.Increments final (Heap.cost heap final) ∧
      runtime (Heap.cost heap final) ≤ runtimeBound size.toNat count.toNat := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, frame, fresh, allocated⟩ :=
    call_complete heap size count sources targets weights allocated input
  have increments := (KruskalClocks.call_monotone execution).increments
  refine ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, allocated, increments, ?_⟩
  rw [runtime_increments increments] at bound
  omega

/-- The complete reusable contract retains explicit coefficients for callers
    that need a numerical bound on the full algorithm. -/
theorem total_call_contract (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      heap.Increments final (Heap.cost heap final) ∧
      runtime (Heap.cost heap final) ≤ runtimeBound size.toNat count.toNat :=
  call_contract heap size count sources targets weights allocated input

-- Main result: Running time (total)
/-- The full source algorithm returns a minimum spanning forest with total
    recorded work O(V + E log(E+1) + 1). The positive constant is independent
    of every input and initial counter; no inverse-Ackermann term remains in
    this total scale. Output freshness and caller storage are also guaranteed. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
    ∀ (heap : Heap) (size count : Int) (sources targets weights : SeqRef),
      kruskal.ValidInput heap (size, sources, targets, weights, count) →
      WellFormed size count (heap.read sources) (heap.read targets) →
      ∃ final chosen selected,
        kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
        MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
        Flags (final.read chosen) selected ∧
        heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
        heap.Increments final (Heap.cost heap final) ∧
        runtime (Heap.cost heap final) ≤ C * runtimeScale size.toNat count.toNat := by
  refine ⟨44, by decide, ?_⟩
  intro heap size count sources targets weights allocated input
  obtain ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments, bound⟩ :=
    total_call_contract heap size count sources targets weights allocated input
  exact ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments,
    Nat.le_trans bound (runtimeBound_le _ _)⟩

/-- A compact value-and-work corollary of the full reusable call contract. -/
theorem call (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, _⟩ :=
    call_complete heap size count sources targets weights allocated input
  exact ⟨final, chosen, selected, execution, minimum, flags, bound⟩


/-- Input edges whose returned selection flag is one, in original input order. -/
def selectedEdges (sources targets weights flags : Seq) (count : Int) : List Edge :=
  (edges sources targets weights count).filter (fun edge => flags edge.id == 1)

@[simp] theorem load_sources (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 0 = sources := rfl
@[simp] theorem load_targets (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 1 = targets := rfl
@[simp] theorem load_weights (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 2 = weights := rfl
@[simp] theorem load_clocks (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.clocks = fun _ => 0 := rfl

theorem load_valid (size count : Int) (sources targets weights : Seq) :
    kruskal.ValidInput (kruskal.load (size, sources, targets, weights, count)).1
      (size, 0, 1, 2, count) := by
  simp [kruskal.ValidInput, kruskal.load, Heap.allocate]

/-- Every well-formed finite graph has a completed execution and cost record. -/
theorem terminates {size count : Int} {sources targets weights : Seq}
    (input : WellFormed size count sources targets) :
    ∃ chosen costs, kruskal.ReturnsWithCost (size, sources, targets, weights, count) chosen costs := by
  let loaded := kruskal.load (size, sources, targets, weights, count)
  obtain ⟨final, result, selected, execution, minimum, flags, bound⟩ :=
    call loaded.1 size count 0 1 2 (load_valid size count sources targets weights) input
  exact ⟨final.read result, Heap.cost loaded.1 final, final, result, execution.run, rfl, rfl⟩

/-- Correctness and the complete operation bound share the same execution.
    All storage allocation and data-structure invariants are internal to the proof. -/
theorem verified {size count : Int} {sources targets weights chosen : Seq} {costs : Clocks}
    (input : WellFormed size count sources targets)
    (execution : kruskal.ReturnsWithCost (size, sources, targets, weights, count) chosen costs) :
    MinimumSpanningForest (edges sources targets weights count)
      (selectedEdges sources targets weights chosen count) ∧
      runtime costs ≤ runtimeBound size.toNat count.toNat := by
  obtain ⟨final, result, run, output, cost⟩ := execution
  let loaded := kruskal.load (size, sources, targets, weights, count)
  obtain ⟨expectedHeap, expectedResult, selected, summary, minimum, flags, bound⟩ :=
    call loaded.1 size count 0 1 2 (load_valid size count sources targets weights) input
  obtain ⟨rfl, rfl⟩ := run.eq_of_call summary
  have selection : Flags chosen selected := by
    rw [← output]
    exact flags
  refine ⟨minimum_from_flags minimum selection, ?_⟩
  have baseline : runtime loaded.1.clocks = 0 := by
    simp [loaded, runtime, KruskalSortedAnalysis.runtime, SortIndicesAnalysis.runtime, Clocks.weighted, work, UnionFindAnalysis.work]
  have increments : Heap.cost loaded.1 final = final.clocks := by
    funext clock
    simp [Heap.cost, loaded]
  rw [← cost, increments]
  simpa only [baseline, Nat.zero_add] using bound

-- Main result: Correctness
/-- Every returned flag sequence selects a minimum spanning forest of the input
    graph. Disconnected graphs, negative weights, parallel edges, and self-loops
    are supported. The only preconditions are finite nonnegative counts and
    endpoints in the declared vertex range. -/
theorem correct {size count : Int} {sources targets weights chosen : Seq}
    (input : WellFormed size count sources targets)
    (execution : kruskal.Returns (size, sources, targets, weights, count) chosen) :
    MinimumSpanningForest (edges sources targets weights count)
      (selectedEdges sources targets weights chosen count) := by
  obtain ⟨costs, counted⟩ := execution.withCost
  exact (verified input counted).1

/-- The total of all eight recorded operation clocks is bounded by
    2E(3 log2(E+1)+2) + V + 2 + E(10 alpha(V)+14). This is the source-level
    unit-cost model for integer arithmetic and sequence access. -/
theorem running_time {size count : Int} {sources targets weights chosen : Seq} {costs : Clocks}
    (input : WellFormed size count sources targets)
    (execution : kruskal.ReturnsWithCost (size, sources, targets, weights, count) chosen costs) :
    runtime costs ≤ runtimeBound size.toNat count.toNat :=
  (verified input execution).2

/-- For a nonempty connected graph the selected forest is a minimum spanning tree. -/
theorem connected_correct {size count : Int} {sources targets weights chosen : Seq}
    (input : WellFormed size count sources targets) (nonempty : 0 < size)
    (connected : ConnectedOn size.toNat (edges sources targets weights count))
    (execution : kruskal.Returns (size, sources, targets, weights, count) chosen) :
    MinimumSpanningTree size.toNat (edges sources targets weights count)
      (selectedEdges sources targets weights chosen count) :=
  (correct input execution).tree (by omega) (input.valid weights) connected

-- Main result: Running time (after sorting)
/-- Re-export the sorted-entry contract beside the total bound for comparison.
    Its cost starts after the caller supplies the sorted order, and includes
    singleton initialization and the complete edge scan. -/
theorem running_time_after_sorting :
    ∃ C : Nat, 0 < C ∧
    ∀ (heap : Heap) (size count : Int) (sources targets weights order : SeqRef),
      Algo.kruskal_sorted.kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order) →
      WellFormed size count (heap.read sources) (heap.read targets) →
      SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order) →
      ∃ final chosen selected,
        Algo.kruskal_sorted.kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
        MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
        Flags (final.read chosen) selected ∧
        heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
        heap.Increments final (Heap.cost heap final) ∧
        KruskalSortedAnalysis.runtime (Heap.cost heap final) ≤ C * KruskalSortedAnalysis.runtimeScale size.toNat count.toNat ∧
        (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
          (Heap.cost heap final) clock = 0) :=
  KruskalSortedAnalysis.correctness_and_running_time

end KruskalAnalysis
