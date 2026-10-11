import Algo.kruskal.Analysis

/-! A client reuses two complete Kruskal calls without inspecting either call's
transitions. The first output survives the second call, and actual costs add
from arbitrary initial counters. Inputs may alias. -/

open Algo2LeanGenerated Algo.kruskal KruskalAnalysis KruskalInput

theorem repeated_calls (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ middle after first second,
      kruskal.Call heap (size, sources, targets, weights, count) middle first ∧
      kruskal.Call middle (size, sources, targets, weights, count) after second ∧
      after.read first = middle.read first ∧
      runtime (Heap.cost heap after) ≤ 2 * runtimeBound size.toNat count.toNat := by
  obtain ⟨middle, first, selected, firstCall, _, _, frame, _, firstAllocated, firstCost, firstBound⟩ :=
    call_contract heap size count sources targets weights allocated input
  have allocatedAgain : kruskal.ValidInput middle (size, sources, targets, weights, count) :=
    ⟨Nat.lt_of_lt_of_le allocated.1 frame.nextRef,
      Nat.lt_of_lt_of_le allocated.2.1 frame.nextRef,
      Nat.lt_of_lt_of_le allocated.2.2 frame.nextRef⟩
  have inputAgain : WellFormed size count (middle.read sources) (middle.read targets) := by
    rw [frame.read sources allocated.1 (by simp), frame.read targets allocated.2.1 (by simp)]
    exact input
  obtain ⟨after, second, selectedAgain, secondCall, _, _, secondFrame, _, _, secondCost, secondBound⟩ :=
    call_contract middle size count sources targets weights allocatedAgain inputAgain
  refine ⟨middle, after, first, second, firstCall, secondCall,
    secondFrame.read first firstAllocated (by simp), ?_⟩
  have whole := (firstCost.monotone.trans secondCost.monotone).increments
  have firstWork := runtime_increments firstCost
  have secondWork := runtime_increments secondCost
  have wholeWork := runtime_increments whole
  omega

/-! Sorted edge orders remain valid across calls because the contract preserves
all input arrays. The second call also preserves the first result, and neither
call changes the sorting counters, regardless of their initial values. -/

open Algo.kruskal_sorted in
theorem repeated_sorted_calls (heap : Heap) (size count : Int) (sources targets weights order : SeqRef)
    (allocated : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (input : WellFormed size count (heap.read sources) (heap.read targets))
    (ordered : SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order)) :
    ∃ middle after first second,
      kruskal_sorted.Call heap (size, sources, targets, weights, count, order) middle first ∧
      kruskal_sorted.Call middle (size, sources, targets, weights, count, order) after second ∧
      after.read first = middle.read first ∧
      KruskalSortedAnalysis.runtime (Heap.cost heap after) ≤
        2 * KruskalSortedAnalysis.runtimeBound size.toNat count.toNat ∧
      (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
        after.clocks clock = heap.clocks clock) := by
  obtain ⟨middle, first, selected, firstCall, _, _, frame, _, firstAllocated,
      firstCost, firstBound, firstClocks⟩ :=
    KruskalSortedAnalysis.call_contract heap size count sources targets weights order allocated input ordered
  have allocatedAgain : kruskal_sorted.ValidInput middle (size, sources, targets, weights, count, order) :=
    ⟨Nat.lt_of_lt_of_le allocated.1 frame.nextRef,
      Nat.lt_of_lt_of_le allocated.2.1 frame.nextRef,
      Nat.lt_of_lt_of_le allocated.2.2.1 frame.nextRef,
      Nat.lt_of_lt_of_le allocated.2.2.2 frame.nextRef⟩
  have inputAgain : WellFormed size count (middle.read sources) (middle.read targets) := by
    rw [frame.read sources allocated.1 (by simp), frame.read targets allocated.2.1 (by simp)]
    exact input
  have orderAgain : SortIndicesAnalysis.SortedPermutation (middle.read weights) count (middle.read order) := by
    rw [frame.read weights allocated.2.2.1 (by simp), frame.read order allocated.2.2.2 (by simp)]
    exact ordered
  obtain ⟨after, second, selectedAgain, secondCall, _, _, secondFrame, _, _,
      secondCost, secondBound, secondClocks⟩ :=
    KruskalSortedAnalysis.call_contract middle size count sources targets weights order allocatedAgain inputAgain orderAgain
  refine ⟨middle, after, first, second, firstCall, secondCall,
    secondFrame.read first firstAllocated (by simp), ?_, ?_⟩
  · have whole := (firstCost.monotone.trans secondCost.monotone).increments
    have firstWork := KruskalSortedAnalysis.runtime_increments firstCost
    have secondWork := KruskalSortedAnalysis.runtime_increments secondCost
    have wholeWork := KruskalSortedAnalysis.runtime_increments whole
    omega
  · intro clock outside
    rw [secondCost clock, firstCost clock, firstClocks clock outside, secondClocks clock outside]
    simp
