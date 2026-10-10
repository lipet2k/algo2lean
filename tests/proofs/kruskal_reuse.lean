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
