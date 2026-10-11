import Algo.kruskal_scan.Analysis
import Algo.kruskal_input.Analysis
import Algo.kruskal_sorted_clocks.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal after sorting: a caller supplies a permutation of the original edge
identifiers in nondecreasing weight order. The source allocates singleton
components and scans that order; it performs no sorting. The reusable Call
contract combines the graph exchange argument with the independently proved
inverse-Ackermann contracts for union by rank and full path compression.
-/

namespace KruskalSortedAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal_sorted Algo.kruskal_sorted.Algo2LeanGenerated
open Algo2Lean.Kruskal KruskalInput KruskalAnalysis

/-- The same eight source-event clocks used for the complete sorting algorithm.
    Sorting clocks have zero increments in this entry point. -/
def runtime (costs : Clocks) : Nat := SortIndicesAnalysis.runtime costs + work costs

/-- Initialization, the entry tick, and the amortized edge scan. -/
noncomputable def runtimeBound (vertices edges : Nat) : Nat :=
  vertices + 2 + edges * (10 * Algo2Lean.Ackermann.alpha vertices + 14)

/-- A uniform asymptotic scale, including the constant cost of empty inputs. -/
noncomputable def runtimeScale (vertices edges : Nat) : Nat :=
  vertices + 1 + edges * Algo2Lean.Ackermann.alpha vertices

/-- The explicit bound implies O(V + E alpha(V) + 1) with one universal constant. -/
theorem runtimeBound_le (vertices edges : Nat) :
    runtimeBound vertices edges ≤ 24 * runtimeScale vertices edges := by
  have positive := Algo2Lean.Ackermann.alpha_pos vertices
  have edgeBound : 10 * Algo2Lean.Ackermann.alpha vertices + 14 ≤
      24 * Algo2Lean.Ackermann.alpha vertices := by omega
  have multiplied := Nat.mul_le_mul_left edges edgeBound
  calc
    runtimeBound vertices edges ≤ vertices + 2 + 24 * (edges * Algo2Lean.Ackermann.alpha vertices) := by
      simpa [runtimeBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Nat.add_le_add_left multiplied (vertices + 2)
    _ ≤ 24 * runtimeScale vertices edges := by
      simp only [runtimeScale, Nat.mul_add, Nat.mul_one]
      omega

/-- Weighted runtime adds across the actual caller-relative counter increments. -/
theorem runtime_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    runtime after.clocks = runtime before.clocks + runtime costs := by
  simp only [runtime, SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, work, UnionFindAnalysis.work]
  rw [effect "sort_steps", effect "heap_comparisons", effect "heap_swaps",
    effect "uf_init", effect "uf_find", effect "uf_compress", effect "uf_union", effect "kruskal"]
  omega

/-- The source constructs singleton components and enters its edge scan directly. -/
theorem sorted_calls (heap initialized final : Heap)
    (size count : Int) (sources targets weights order : SeqRef) (sets : UnionFindAnalysis.Layout)
    (valid : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (construction : Algo.union_find.UnionFind.Call (heap.allocate (fun _ => 0)) size initialized sets.object)
    (scan : ScanCall ⟨sets, sources, targets, order, heap.nextRef⟩
      (initialized.tick "kruskal") 0 count final) :
    kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final heap.nextRef := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.kruskal_sorted_pc35 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc34 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc33 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc32 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc31 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller construction.2).trans
  apply Reaches.prepend (Step.kruskal_sorted_pc30 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc29 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc28 _ _ _)
  refine scan (.active _ (.fn_kruskal_sorted 4 _) []) ?_ rfl caller
  exact ⟨True.intro, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On a supplied sorted order, initialization and the verified edge scan
    terminate with a fresh minimum spanning forest. Old caller storage remains
    unchanged, including all input arrays and their possible aliases. -/
theorem call_complete (heap : Heap) (size count : Int) (sources targets weights order : SeqRef)
    (allocated : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (input : WellFormed size count (heap.read sources) (heap.read targets))
    (ordered : SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order)) :
    ∃ final chosen selected,
      kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
        final.clocks clock = heap.clocks clock) := by
  let initialized := initialHeap heap size.toNat
  have initFrame := initial_footprint heap size.toNat
  obtain ⟨pending, sorting⟩ := sorted_edges (heap.read sources) (heap.read targets)
    (heap.read weights) (heap.read order) count ordered
  have orderPrivate : order ∉ [(initialLayout heap size.toNat sources targets order).sets.parent,
      (initialLayout heap size.toNat sources targets order).sets.rank, heap.nextRef] := by
    simp only [initialLayout, UnionFindAnalysis.newLayout, Heap.allocate_nextRef,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    have old := allocated.2.2.2
    simp only [SeqRef] at *
    omega
  have initial := initial_invariant heap initialized size.toNat sources targets order pending
    allocated.1 allocated.2.1 (Heap.Footprint.refl _ [] [] []) orderPrivate
    (Nat.lt_of_lt_of_le allocated.2.2.2 initFrame.nextRef) (sorting.valid input)
    sorting.source sorting.target (by
      intro i within
      rw [initial_read_old heap size.toNat order allocated.2.2.2]
      exact sorting.order i within)
  obtain ⟨final, model, selected, scanCall, finalInvariant, scan, frame, clocks, worstCase, bound⟩ :=
    scan_contract (initialLayout heap size.toNat sources targets order)
      (initialized.tick "kruskal") (Algo2Lean.UnionFind.initial size.toNat) 0 count pending []
      initial (by rw [sorting.length]; have nonnegative := input.count_nonnegative; omega)
  have composed := sorted_calls heap initialized final size count sources targets weights order
    (UnionFindAnalysis.newLayout (heap.allocate (fun _ => 0))) allocated
    (by simpa only [initialized, initialHeap, UnionFindAnalysis.newLayout,
      Int.toNat_of_nonneg input.size_nonnegative] using!
      UnionFindAnalysis.constructor_summary (heap.allocate (fun _ => 0)) size.toNat)
    scanCall
  have wholeFrame := ((initFrame.tick "kruskal").weaken
    (moreSequences := [(initialLayout heap size.toNat sources targets order).sets.parent,
      (initialLayout heap size.toNat sources targets order).sets.rank,
      (initialLayout heap size.toNat sources targets order).chosen])
    (moreObjects := []) (moreCollections := []) (by simp) (by simp) (by simp)).trans frame
  have preservedClocks : ∀ clock,
      clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
      final.clocks clock = heap.clocks clock := by
    intro clock outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    rw [clocks clock (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨outside.2.2.2.2, outside.2.1, outside.2.2.1, outside.2.2.2.1⟩)]
    simp only [Heap.tick, if_neg outside.2.2.2.2]
    exact initial_clocks heap size.toNat clock outside.1
  refine ⟨final, heap.nextRef, selected, composed, sorting.minimum scan, finalInvariant.flags,
    ?_, ?_, Nat.le_refl _, finalInvariant.chosenAllocated, preservedClocks⟩
  · have initialWork := initial_work heap size.toNat
    have tickWork : work (initialized.tick "kruskal").clocks = work initialized.clocks + 1 := by
      simp [work, UnionFindAnalysis.work, Heap.tick]; omega
    rw [tickWork, initialWork, sorting.length, Algo2Lean.UnionFind.initial_potential] at bound
    have sortUnchanged : SortIndicesAnalysis.runtime final.clocks = SortIndicesAnalysis.runtime heap.clocks := by
      simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      rw [preservedClocks "sort_steps" (by decide), preservedClocks "heap_comparisons" (by decide),
        preservedClocks "heap_swaps" (by decide)]
    simp only [runtime, runtimeBound]
    rw [sortUnchanged]
    omega
  · refine ⟨wholeFrame.nextRef, wholeFrame.nextObject, wholeFrame.nextCollection,
      wholeFrame.classes, wholeFrame.types, ?_, wholeFrame.otherObjects, wholeFrame.otherCollections⟩
    intro ref old _
    apply wholeFrame.otherSequences ref old
    simp only [initialLayout, UnionFindAnalysis.newLayout, Heap.allocate_nextRef,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega

/-- The reusable post-sorting contract exposes actual counter increments,
    fresh output storage, unchanged caller storage, and zero sorting increments. -/
theorem call_contract (heap : Heap) (size count : Int) (sources targets weights order : SeqRef)
    (allocated : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (input : WellFormed size count (heap.read sources) (heap.read targets))
    (ordered : SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order)) :
    ∃ final chosen selected,
      kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      heap.Increments final (Heap.cost heap final) ∧
      runtime (Heap.cost heap final) ≤ runtimeBound size.toNat count.toNat ∧
      (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
        (Heap.cost heap final) clock = 0) := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, frame, fresh, valid, clocks⟩ :=
    call_complete heap size count sources targets weights order allocated input ordered
  have increments := (KruskalSortedClocks.call_monotone execution).increments
  refine ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments, ?_, ?_⟩
  · rw [runtime_increments increments] at bound
    omega
  · intro clock outside
    simp [Heap.cost, clocks clock outside]


-- Main result: Correctness and running time
/-- With edges already ordered by weight, the actual source call returns a
    minimum spanning forest in O(V + E alpha(V) + 1) recorded work. The same
    positive constant works for every graph, supplied order, and caller heap.
    The output is fresh, caller storage is preserved, and sorting costs zero. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
    ∀ (heap : Heap) (size count : Int) (sources targets weights order : SeqRef),
      kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order) →
      WellFormed size count (heap.read sources) (heap.read targets) →
      SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order) →
      ∃ final chosen selected,
        kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
        MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
        Flags (final.read chosen) selected ∧
        heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
        heap.Increments final (Heap.cost heap final) ∧
        runtime (Heap.cost heap final) ≤ C * runtimeScale size.toNat count.toNat ∧
        (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
          (Heap.cost heap final) clock = 0) := by
  refine ⟨24, by decide, ?_⟩
  intro heap size count sources targets weights order allocated input ordered
  obtain ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments, bound, clocks⟩ :=
    call_contract heap size count sources targets weights order allocated input ordered
  exact ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments,
    Nat.le_trans bound (runtimeBound_le _ _), clocks⟩

/-- A compact value-and-work view of the same reusable call proof. -/
theorem call (heap : Heap) (size count : Int) (sources targets weights order : SeqRef)
    (allocated : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (input : WellFormed size count (heap.read sources) (heap.read targets))
    (ordered : SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order)) :
    ∃ final chosen selected,
      kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, _⟩ :=
    call_complete heap size count sources targets weights order allocated input ordered
  exact ⟨final, chosen, selected, execution, minimum, flags, bound⟩

/-- Selected original edge occurrences, listed in their original identifier order. -/
def selectedEdges (sources targets weights flags : Seq) (count : Int) : List Edge :=
  (edges sources targets weights count).filter (fun edge => flags edge.id == 1)

@[simp] theorem load_sources (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 0 = sources := rfl
@[simp] theorem load_targets (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 1 = targets := rfl
@[simp] theorem load_weights (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 2 = weights := rfl
@[simp] theorem load_order (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 3 = order := rfl
@[simp] theorem load_clocks (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.clocks = fun _ => 0 := rfl

theorem load_valid (size count : Int) (sources targets weights order : Seq) :
    kruskal_sorted.ValidInput (kruskal_sorted.load (size, sources, targets, weights, count, order)).1
      (size, 0, 1, 2, count, 3) := by
  simp [kruskal_sorted.ValidInput, kruskal_sorted.load, Heap.allocate]

/-- Every finite well-formed graph with a supplied sorted order has a completed call. -/
theorem terminates {size count : Int} {sources targets weights order : Seq}
    (input : WellFormed size count sources targets)
    (ordered : SortIndicesAnalysis.SortedPermutation weights count order) :
    ∃ chosen costs, kruskal_sorted.ReturnsWithCost (size, sources, targets, weights, count, order) chosen costs := by
  let loaded := kruskal_sorted.load (size, sources, targets, weights, count, order)
  obtain ⟨final, result, selected, execution, minimum, flags, bound⟩ :=
    call loaded.1 size count 0 1 2 3 (load_valid size count sources targets weights order) input ordered
  exact ⟨final.read result, Heap.cost loaded.1 final, final, result, execution.run, rfl, rfl⟩

/-- Every completed execution agrees with the verified call, giving correctness
    and the post-sorting bound for the same output and cost record. -/
theorem verified {size count : Int} {sources targets weights order chosen : Seq} {costs : Clocks}
    (input : WellFormed size count sources targets)
    (ordered : SortIndicesAnalysis.SortedPermutation weights count order)
    (execution : kruskal_sorted.ReturnsWithCost (size, sources, targets, weights, count, order) chosen costs) :
    MinimumSpanningForest (edges sources targets weights count)
      (selectedEdges sources targets weights chosen count) ∧
      runtime costs ≤ runtimeBound size.toNat count.toNat := by
  obtain ⟨final, result, run, output, cost⟩ := execution
  let loaded := kruskal_sorted.load (size, sources, targets, weights, count, order)
  obtain ⟨expectedHeap, expectedResult, selected, summary, minimum, flags, bound⟩ :=
    call loaded.1 size count 0 1 2 3 (load_valid size count sources targets weights order) input ordered
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

/-- The returned flags select a minimum spanning forest, including for
    disconnected graphs, signed weights, parallel edges, and self-loops. -/
theorem correct {size count : Int} {sources targets weights order chosen : Seq}
    (input : WellFormed size count sources targets)
    (ordered : SortIndicesAnalysis.SortedPermutation weights count order)
    (execution : kruskal_sorted.Returns (size, sources, targets, weights, count, order) chosen) :
    MinimumSpanningForest (edges sources targets weights count)
      (selectedEdges sources targets weights chosen count) := by
  obtain ⟨costs, counted⟩ := execution.withCost
  exact (verified input ordered counted).1

/-- The explicit post-sorting operation bound, with no sorting work included. -/
theorem running_time {size count : Int} {sources targets weights order chosen : Seq} {costs : Clocks}
    (input : WellFormed size count sources targets)
    (ordered : SortIndicesAnalysis.SortedPermutation weights count order)
    (execution : kruskal_sorted.ReturnsWithCost (size, sources, targets, weights, count, order) chosen costs) :
    runtime costs ≤ runtimeBound size.toNat count.toNat :=
  (verified input ordered execution).2

/-- A nonempty connected graph yields a minimum spanning tree. -/
theorem connected_correct {size count : Int} {sources targets weights order chosen : Seq}
    (input : WellFormed size count sources targets)
    (ordered : SortIndicesAnalysis.SortedPermutation weights count order)
    (nonempty : 0 < size) (connected : ConnectedOn size.toNat (edges sources targets weights count))
    (execution : kruskal_sorted.Returns (size, sources, targets, weights, count, order) chosen) :
    MinimumSpanningTree size.toNat (edges sources targets weights count)
      (selectedEdges sources targets weights chosen count) :=
  (correct input ordered execution).tree (by omega) (input.valid weights) connected

end KruskalSortedAnalysis
