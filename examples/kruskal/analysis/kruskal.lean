import Algo.kruskal_scan.Analysis
import Algo.kruskal_input.Analysis
import Algo.kruskal_clocks.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's algorithm on finite undirected weighted graphs. The public interface
uses integer sequences for source vertices, target vertices, edge weights, and
returned selection flags. Correctness and running time reuse the independent
sorting, union-find, and graph analyses.
-/

namespace KruskalAnalysis

open Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
open KruskalInput

/-- Unit weights for sorting, heap operations, union-find operations, and edge
    scanning. Arithmetic and infinite-sequence access use the source cost model. -/
def runtime (costs : Clocks) : Nat := SortIndicesAnalysis.runtime costs + work costs

/-- Sorting costs O(E log E); the separately verified union-find contract makes
    the remaining work O(V + E alpha(V)), including initialization and scanning. -/
noncomputable def runtimeBound (vertices edges : Nat) : Nat :=
  SortIndicesAnalysis.runtimeBound edges + vertices + 2 + edges * (10 * Algo2Lean.Ackermann.alpha vertices + 14)

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

private theorem scan_preserves_sorting (heap final : Heap)
    (clocks : ∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
      final.clocks clock = (heap.tick "kruskal").clocks clock) :
    SortIndicesAnalysis.runtime final.clocks = SortIndicesAnalysis.runtime heap.clocks := by
  simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [clocks "sort_steps" (by decide), clocks "heap_comparisons" (by decide),
    clocks "heap_swaps" (by decide)]
  simp [Heap.tick]

private theorem initialization_preserves_sorting (heap : Heap) (size : Nat) :
    SortIndicesAnalysis.runtime (initialHeap heap size).clocks =
      SortIndicesAnalysis.runtime heap.clocks := by
  simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [initial_clocks _ _ _ (by decide), initial_clocks _ _ _ (by decide),
    initial_clocks _ _ _ (by decide)]

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

/-- Weighted runtime adds across exact clock increments. -/
theorem runtime_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    runtime after.clocks = runtime before.clocks + runtime costs := by
  simp only [runtime, SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, work, UnionFindAnalysis.work]
  rw [effect "sort_steps", effect "heap_comparisons", effect "heap_swaps",
    effect "uf_init", effect "uf_find", effect "uf_compress", effect "uf_union", effect "kruskal"]
  omega

/-- The algorithm terminates on every finite valid graph. Its output flags name
    a minimum spanning forest, and its clocks satisfy the explicit cost bound.
    Sequence references permit aliasing among the three input arrays. -/
theorem call_complete (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef := by
  let initialized := initialHeap heap size.toNat
  have initFrame := initial_footprint heap size.toNat
  obtain ⟨sorted, order, sortCall, sortedIds, preserved, fresh, orderAllocated, budget⟩ :=
    SortIndicesAnalysis.call initialized weights count
      (Nat.lt_of_lt_of_le allocated.2.2 initFrame.nextRef) input.count_nonnegative
  have sameWeights : initialized.read weights = heap.read weights :=
    initial_read_old heap size.toNat weights allocated.2.2
  rw [sameWeights] at sortedIds
  obtain ⟨pending, sorting⟩ := sorted_edges (heap.read sources) (heap.read targets)
    (heap.read weights) (sorted.read order) count sortedIds
  have sortFrame := sorting_footprint preserved
  have initial := initial_invariant heap sorted size.toNat sources targets order pending
    allocated.1 allocated.2.1 sortFrame fresh orderAllocated (sorting.valid input)
    sorting.source sorting.target sorting.order
  obtain ⟨final, model, selected, scanCall, finalInvariant, scan, frame, clocks, worstCase, bound⟩ :=
    scan_contract (initialLayout heap size.toNat sources targets order)
      (sorted.tick "kruskal") (Algo2Lean.UnionFind.initial size.toNat) 0 count pending []
      initial (by rw [sorting.length]; have nonnegative := input.count_nonnegative; omega)
  have composed := kruskal_calls heap initialized sorted final size count sources targets weights order
    (UnionFindAnalysis.newLayout (heap.allocate (fun _ => 0))) allocated
    (by simpa only [initialized, initialHeap, UnionFindAnalysis.newLayout,
      Int.toNat_of_nonneg input.size_nonnegative] using!
      UnionFindAnalysis.constructor_summary (heap.allocate (fun _ => 0)) size.toNat)
    sortCall scanCall
  have prefixFrame := (initFrame.trans sortFrame).tick "kruskal"
  have wholeFrame := (prefixFrame.weaken
    (moreSequences := [(initialLayout heap size.toNat sources targets order).sets.parent,
      (initialLayout heap size.toNat sources targets order).sets.rank,
      (initialLayout heap size.toNat sources targets order).chosen])
    (moreObjects := []) (moreCollections := []) (by simp) (by simp) (by simp)).trans frame
  refine ⟨final, heap.nextRef, selected, composed, sorting.minimum scan, finalInvariant.flags,
    ?_, ?_, Nat.le_refl _, finalInvariant.chosenAllocated⟩
  · have sortBound := sorting_work budget
    have unchangedWork := sorting_preserves_work preserved
    have unchangedSort := scan_preserves_sorting sorted final clocks
    have unchangedInitSort := initialization_preserves_sorting heap size.toNat
    have initialWork := initial_work heap size.toNat
    have tickWork : work (sorted.tick "kruskal").clocks = work sorted.clocks + 1 := by
      simp [work, UnionFindAnalysis.work, Heap.tick]; omega
    rw [tickWork, unchangedWork, sorting.length, Algo2Lean.UnionFind.initial_potential] at bound
    change work initialized.clocks = _ at initialWork
    change SortIndicesAnalysis.runtime initialized.clocks = _ at unchangedInitSort
    simp only [runtime, runtimeBound]
    rw [unchangedSort]
    omega
  · refine ⟨wholeFrame.nextRef, wholeFrame.nextObject, wholeFrame.nextCollection,
      wholeFrame.classes, wholeFrame.types, ?_, wholeFrame.otherObjects, wholeFrame.otherCollections⟩
    intro ref old _
    apply wholeFrame.otherSequences ref old
    simp only [initialLayout, UnionFindAnalysis.newLayout, Heap.allocate_nextRef,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
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
    simp [loaded, runtime, SortIndicesAnalysis.runtime, Clocks.weighted, work, UnionFindAnalysis.work]
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

-- Main result: Running time
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

end KruskalAnalysis
