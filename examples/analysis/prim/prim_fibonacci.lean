import Algo.prim.prim_fibonacci.Generated
import Algo.prim.prim_fibonacci.Facts
import Algo.prim.prim.Analysis
import Algo.dijkstra.support.fibonacci_queue.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Fibonacci-heap Prim constructs three private client sequences and one queue.
    The wrapper links the generic Prim call contract to the existing Fibonacci
    heap contract, preserving the original caller's storage and clock values. -/

namespace FibonacciPrimAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim_fibonacci
open PrimGraph PrimAnalysis

/-- Compiler-generated bindings connect the unchanged heap implementation to
    Prim's abstract queue interface. -/
theorem bridge : FibonacciQueueAnalysis.Bridge FibonacciHeap_as_PriorityQueue := {
  valid := by intro heap ref; simp [FibonacciHeap_as_PriorityQueue]
  is_empty := FibonacciHeap_as_PriorityQueue_summary_is_empty
  update := FibonacciHeap_as_PriorityQueue_summary_push_or_decrease
  extract := FibonacciHeap_as_PriorityQueue_summary_pop_min
}

/-- The wrapper allocates its work arrays, constructs the queue, and reuses the
    supplied generic Prim execution without inspecting any heap operation. -/
theorem call (heap queuedHeap finalHeap : Heap) (graph : Ref_Graph) (root size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (rootLower : 0 ≤ root) (rootUpper : root < size)
    (constructor : Algo.fibonacci_heap.FibonacciHeap.Call
      (((heap.allocate (fun _ => -1)).allocate (fun _ => 0)).allocate (fun _ => 0))
      () queuedHeap heap.nextObject)
    (grow : Algo.prim.prim.prim.Call use_prim_prim_0
      queuedHeap (graph,root,heap.nextObject,heap.nextRef+1,heap.nextRef,heap.nextRef+2)
      finalHeap heap.nextRef)
    (allocated : heap.nextRef < finalHeap.nextRef) :
    prim_fibonacci.Call heap (graph,root) finalHeap heap.nextRef := by
  have sizeAfter : field_Graph_size (heap.allocate (fun _ => -1)) graph = some size := readSize
  open Algo.prim.prim_fibonacci.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.prim_fibonacci_pc23 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc22 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc21 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc20 _ _ caller
      (by simp [field__a2l_import_0_Graph_size,sizeAfter]))
    apply Reaches.prepend (Step.prim_fibonacci_pc19_false _ _ caller
      (by simp [field__a2l_import_0_Graph_size,sizeAfter]; omega))
    apply Reaches.prepend (Step.prim_fibonacci_pc16 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc15 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc14 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc13 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc12 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc11 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc10 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller constructor.2).trans
    apply Reaches.prepend (Step.prim_fibonacci_pc9 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc8 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc7 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc6 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc5 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc4 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc3 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc2 _ _ caller)
    apply (ModuleCall.summary import_3_use_prim_prim_0_simulates _ caller grow.2).trans
    exact Reaches.single (Step.prim_fibonacci_pc1 _ _ caller allocated)

/-- An invalid root returns a fresh all-unassigned parent sequence and performs
    no queue construction or counted operations. -/
theorem invalid_root (heap : Heap) (graph : Ref_Graph) (root size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : root < 0 ∨ size ≤ root) :
    prim_fibonacci.Call heap (graph,root) (heap.allocate (fun _ => -1)) heap.nextRef := by
  have sizeAfter : field_Graph_size (heap.allocate (fun _ => -1)) graph = some size := readSize
  open Algo.prim.prim_fibonacci.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.prim_fibonacci_pc23 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc22 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc21 _ _ caller)
    apply Reaches.prepend (Step.prim_fibonacci_pc20 _ _ caller
      (by simp [field__a2l_import_0_Graph_size,sizeAfter]))
    apply Reaches.prepend (Step.prim_fibonacci_pc19_true _ _ caller
      (by simpa [field__a2l_import_0_Graph_size,sizeAfter] using invalid))
    apply Reaches.prepend (Step.prim_fibonacci_pc18 _ _ caller)
    exact Reaches.single (Step.prim_fibonacci_pc17 _ _ caller (by simp))

/-- Each explicit heap event and Prim bookkeeping clock is counted once. -/
def clockWork (costs : Clocks) : Nat :=
  Clocks.weighted FibonacciQueueAnalysis.metric costs + costs "queue_updates" + costs "queue_pops" +
    costs "queue_empty_checks" + costs "edges" + costs "improvements" + costs "settlements"

/-- An explicit reusable bound in directed adjacency occurrences and vertices. -/
def runtimeBound (size : Int) (adjacency : Adjacency) : Nat :=
  (20 + 3) * (edgeBudget adjacency (vertexRange size) + 1) +
    ((12 * (2 * size.toNat.log2 + 2)) + 3) * size.toNat

/-- The usual Fibonacci-heap complexity scale, retaining one logarithmic unit
    for single-vertex inputs. Edges count directed adjacency occurrences. -/
def runtimeScale (size : Int) (adjacency : Adjacency) : Nat :=
  edgeBudget adjacency (vertexRange size) + size.toNat * (size.toNat.log2 + 1)

/-- The explicit operational bound has one uniform constant in the conventional
    runtime scale whenever a valid root can exist. -/
theorem runtimeBound_le (size : Int) (adjacency : Adjacency) (positive : 0 < size) :
    runtimeBound size adjacency ≤ 50 * runtimeScale size adjacency := by
  have nonempty : 0 < size.toNat := by omega
  have constant : 23 ≤ 23 * size.toNat := Nat.le_mul_of_pos_right 23 nonempty
  have pops := Nat.mul_le_mul_right size.toNat
    (show (12 * (2 * size.toNat.log2 + 2) + 3) + 23 ≤
        50 * (size.toNat.log2 + 1) by omega)
  rw [Nat.add_mul] at pops
  have edges := Nat.mul_le_mul_right (edgeBudget adjacency (vertexRange size))
    (show 23 ≤ 50 by decide)
  calc
    runtimeBound size adjacency =
        23 * edgeBudget adjacency (vertexRange size) + 23 +
          (12 * (2 * size.toNat.log2 + 2) + 3) * size.toNat := by
      simp [runtimeBound, Nat.mul_add]
    _ ≤ 50 * edgeBudget adjacency (vertexRange size) +
        (50 * (size.toNat.log2 + 1)) * size.toNat := by omega
    _ = 50 * runtimeScale size adjacency := by
      unfold runtimeScale
      rw [Nat.mul_add 50 (edgeBudget adjacency (vertexRange size))]
      congr 1
      rw [Nat.mul_assoc, Nat.mul_comm (size.toNat.log2 + 1) size.toNat]

/-- The invalid-root output is independent of all initial clock values. -/
theorem invalid_root_output (heap : Heap) (graph : Ref_Graph) (root size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : root < 0 ∨ size ≤ root) :
    prim_fibonacci.ReturnsWithCost (heap,graph,root) (fun _ => -1) (fun _ => 0) := by
  refine ⟨heap.allocate (fun _ => -1),heap.nextRef,
    (invalid_root heap graph root size valid readSize invalid).run,?_,?_⟩
  · funext index
    simp [Heap.allocate]
  · funext name
    simp [Heap.cost,Heap.allocate,prim_fibonacci.load]

private abbrev allocatedHeap (heap : Heap) : Heap :=
  ((heap.allocate (fun _ => -1)).allocate (fun _ => 0)).allocate (fun _ => 0)

private abbrev client (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) : Client :=
  ⟨graph,size,heads,adjacency,heap.nextRef+1,heap.nextRef,root,heap.nextRef+2,heap.nextObject,heap⟩

private abbrev queueModel (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) :
    PriorityQueueAnalysis.Model use_prim_prim_0.PriorityQueue heap.nextObject
      (client heap graph size root heads adjacency).protection :=
  FibonacciQueueAnalysis.model FibonacciHeap_as_PriorityQueue bridge heap.nextObject
    (client heap graph size root heads adjacency).protection size

private abbrev initial (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) :
    QueueState (dependencies := use_prim_prim_0)
      (client := client heap graph size root heads adjacency)
      (queueModel heap graph size root heads adjacency) :=
  ⟨FibonacciModuleAnalysis.newHeap (allocatedHeap heap),
    FibonacciQueueAnalysis.initialState (allocatedHeap heap)⟩

/-- Fresh allocation separates the three client arrays from the queue while
    preserving the graph, every original caller location, and all counters. -/
private theorem initialized (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency) :
    let model := queueModel heap graph size root heads adjacency
    let state := initial heap graph size root heads adjacency
    Storage (dependencies := use_prim_prim_0)
      (client := client heap graph size root heads adjacency) model state ∧ model.entries state.queueState = [] ∧
      state.heap.read (heap.nextRef+1) = (fun _ => 0) ∧
      state.heap.read heap.nextRef = (fun _ => -1) ∧
      state.heap.read (heap.nextRef+2) = (fun _ => 0) ∧
      state.heap.clocks = heap.clocks := by
  let allocated := allocatedHeap heap
  let customer := client heap graph size root heads adjacency
  let model := queueModel heap graph size root heads adjacency
  let state := initial heap graph size root heads adjacency
  change Storage (dependencies := use_prim_prim_0)
      (client := client heap graph size root heads adjacency) model state ∧ model.entries state.queueState = [] ∧
    state.heap.read (heap.nextRef+1) = (fun _ => 0) ∧
    state.heap.read heap.nextRef = (fun _ => -1) ∧
    state.heap.read (heap.nextRef+2) = (fun _ => 0) ∧ state.heap.clocks = heap.clocks
  have allocatedGraph : GraphRep allocated graph size heads adjacency :=
    representation.preserved (((graph_frame_allocate _ _ _ (fun _ => -1)).trans
      (graph_frame_allocate _ _ _ (fun _ => 0))).trans
      (graph_frame_allocate _ _ _ (fun _ => 0)))
  have protectedFrame := FibonacciQueueAnalysis.constructor_frame allocated customer.protection
  have parentAllocated : customer.parent < allocated.nextRef := by
    change heap.nextRef < heap.nextRef + 1 + 1 + 1
    omega
  have keyAllocated : customer.key < allocated.nextRef := by
    change heap.nextRef + 1 < heap.nextRef + 1 + 1 + 1
    omega
  have selectedAllocated : customer.selected < allocated.nextRef := by
    change heap.nextRef + 2 < heap.nextRef + 1 + 1 + 1
    omega
  have queueRep := FibonacciQueueAnalysis.constructor_rep allocated customer.protection size (by
    intro ref member
    simp only [Client.protection,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact keyAllocated
    · exact parentAllocated
    · exact selectedAllocated)
    ((((Heap.Footprint.refl heap [] [] []).allocate (fun _ => -1)).allocate (fun _ => 0)).allocate (fun _ => 0)) (by
      intro ref member
      simp only [Client.protection,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [customer,Client.protection])
  have storage : Storage (dependencies := use_prim_prim_0)
      (client := client heap graph size root heads adjacency) model state := by
    refine ⟨allocatedGraph.preserved (graph_frame_of_protected allocatedGraph protectedFrame),
      queueRep,?_,?_,?_,?_,?_,?_⟩
    · exact Nat.lt_of_lt_of_le keyAllocated protectedFrame.nextRef
    · exact Nat.lt_of_lt_of_le parentAllocated protectedFrame.nextRef
    · exact Nat.lt_of_lt_of_le selectedAllocated protectedFrame.nextRef
    · simp
    · simp
    · simp
  have keys : state.heap.read customer.key = fun _ => 0 := by
    change (FibonacciModuleAnalysis.newHeap allocated).read customer.key = _
    rw [protectedFrame.sequences customer.key (by simp [Client.protection]) keyAllocated]
    funext vertex
    simp [customer,allocated,Heap.read,Heap.allocate, Nat.add_assoc]
  have parents : state.heap.read customer.parent = fun _ => -1 := by
    change (FibonacciModuleAnalysis.newHeap allocated).read customer.parent = _
    rw [protectedFrame.sequences customer.parent (by simp [Client.protection]) parentAllocated]
    funext vertex
    simp [customer,allocated,Heap.read,Heap.allocate, Nat.add_assoc]
  have flags : state.heap.read customer.selected = fun _ => 0 := by
    change (FibonacciModuleAnalysis.newHeap allocated).read customer.selected = _
    rw [protectedFrame.sequences customer.selected (by simp [Client.protection]) selectedAllocated]
    funext vertex
    simp [customer,allocated,Heap.read,Heap.allocate, Nat.add_assoc]
  exact ⟨storage,rfl,keys,parents,flags,FibonacciQueueAnalysis.constructor_clocks allocated⟩

/-- The reusable call contract returns a fresh parent array describing a minimum
    spanning tree, preserves the graph and the caller's original storage, and
    bounds counters from their actual initial values. -/
theorem summary (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (rootLower : 0 ≤ root) (rootUpper : root < size)
    (symmetric : PrimGraph.Symmetric size adjacency)
    (connected : Algo2Lean.Kruskal.ConnectedOn size.toNat (inputEdges size adjacency)) :
    ∃ after,
      prim_fibonacci.Call heap (graph,root) after heap.nextRef ∧
      GraphRep after graph size heads adjacency ∧
      MinimumSpanningParents size adjacency root (after.read heap.nextRef) ∧
      OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      clockWork (Heap.cost heap after) ≤ runtimeBound size adjacency ∧
      heap.nextRef < after.nextRef ∧ heap.Footprint after [] [] [] := by
  let customer := client heap graph size root heads adjacency
  let model := queueModel heap graph size root heads adjacency
  let state := initial heap graph size root heads adjacency
  obtain ⟨storage,empty,keys,parents,flags,sameClocks⟩ :=
    initialized heap graph size root heads adjacency representation
  have contracts : PriorityQueueAnalysis.Contracts model reservedClocks :=
    FibonacciQueueAnalysis.contracts FibonacciHeap_as_PriorityQueue bridge heap.nextObject
      customer.protection size reservedClocks
      (by simp [Client.protection])
      (by intro name member; simp [reservedClocks] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨after,grow,graphAfter,correct,counts,workBound,resultAllocated,preserved⟩ :=
    prim_complete (dependencies := use_prim_prim_0) (client := customer)
      model contracts (Int.le_refl _) state storage empty keys parents flags
      rootLower rootUpper symmetric connected
  change state.heap.clocks = heap.clocks at sameClocks
  have sameCost : Heap.cost state.heap after = Heap.cost heap after := by
    funext name
    simp only [Heap.cost,sameClocks]
  have costs : OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa only [sameCost] using counts.updates
    · simpa only [sameCost] using counts.pops
    · simpa only [sameCost] using counts.checks
    · simpa only [sameCost] using counts.visits
    · simpa only [sameCost] using counts.improvements
    · simpa only [sameCost] using counts.settlements
  refine ⟨after,call heap state.heap after graph root size representation.valid representation.readSize
    rootLower rootUpper (FibonacciModuleAnalysis.new_heap_summary (allocatedHeap heap)) grow resultAllocated,
    graphAfter,correct,costs,?_,resultAllocated,preserved⟩
  have updates := costs.updates
  have pops := costs.pops
  have checks := costs.checks
  have edges := costs.visits
  have improvements := costs.improvements
  have settlements := costs.settlements
  change Clocks.weighted model.metric (Heap.cost state.heap after) ≤ _ at workBound
  rw [sameCost] at workBound
  simp [model,customer,FibonacciQueueAnalysis.model,QueueState.potential,state,
    FibonacciQueueAnalysis.initialState,Algo2Lean.Fibonacci.scaledPotential,
    Algo2Lean.Fibonacci.potential,Algo2Lean.Fibonacci.Forest.counts,
    Algo2Lean.Fibonacci.Forest.marks] at workBound
  simp only [clockWork,runtimeBound,Nat.add_mul,Nat.mul_add,Nat.mul_one] at workBound ⊢
  omega

/-- Every completed wrapper execution has the verified tree and counter bound. -/
theorem every_execution (heap after : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (result : SeqRef)
    (representation : GraphRep heap graph size heads adjacency)
    (rootLower : 0 ≤ root) (rootUpper : root < size)
    (symmetric : PrimGraph.Symmetric size adjacency)
    (connected : Algo2Lean.Kruskal.ConnectedOn size.toNat (inputEdges size adjacency))
    (execution : prim_fibonacci.Run heap (graph,root) after result) :
    result = heap.nextRef ∧
      MinimumSpanningParents size adjacency root (after.read result) ∧
      OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      clockWork (Heap.cost heap after) ≤ runtimeBound size adjacency := by
  obtain ⟨verified,run,_,correct,counts,bound,_⟩ := summary heap graph size root heads adjacency
    representation rootLower rootUpper symmetric connected
  obtain ⟨rfl,rfl⟩ := execution.eq_of_call run
  exact ⟨rfl,correct,counts,bound⟩

/-- The ordinary-output view uses the same execution witness as the call contract. -/
theorem output_exists (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (rootLower : 0 ≤ root) (rootUpper : root < size)
    (symmetric : PrimGraph.Symmetric size adjacency)
    (connected : Algo2Lean.Kruskal.ConnectedOn size.toNat (inputEdges size adjacency)) :
    ∃ output costs, prim_fibonacci.ReturnsWithCost (heap,graph,root) output costs ∧
      MinimumSpanningParents size adjacency root output ∧
      clockWork costs ≤ runtimeBound size adjacency := by
  obtain ⟨after,run,_,correct,_,bound,_⟩ := summary heap graph size root heads adjacency
    representation rootLower rootUpper symmetric connected
  exact ⟨after.read heap.nextRef,Heap.cost heap after,
    ⟨after,heap.nextRef,run.run,rfl,rfl⟩,correct,bound⟩

/-- All ordinary outputs satisfy the mathematical tree specification and the
    explicit source-clock bound. -/
theorem output_with_cost_correct (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (output : Seq) (costs : Clocks)
    (representation : GraphRep heap graph size heads adjacency)
    (rootLower : 0 ≤ root) (rootUpper : root < size)
    (symmetric : PrimGraph.Symmetric size adjacency)
    (connected : Algo2Lean.Kruskal.ConnectedOn size.toNat (inputEdges size adjacency))
    (execution : prim_fibonacci.ReturnsWithCost (heap,graph,root) output costs) :
    MinimumSpanningParents size adjacency root output ∧
      clockWork costs ≤ runtimeBound size adjacency := by
  obtain ⟨after,result,run,value,clocks⟩ := execution
  obtain ⟨_,correct,_,bound⟩ := every_execution heap after graph size root heads adjacency result
    representation rootLower rootUpper symmetric connected run
  change after.read result = output at value
  change Heap.cost heap after = costs at clocks
  rw [←value,←clocks]
  exact ⟨correct,bound⟩

-- Main result: Correctness and running time
/-- One uniform constant bounds the measured runtime on every represented,
    connected undirected input with a valid root. The public result remains a
    reusable Call contract, including the fresh output and caller footprint. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (graph : Ref_Graph) (size root : Int)
        (heads : CollectionRef) (adjacency : Adjacency),
        GraphRep heap graph size heads adjacency → 0 ≤ root → root < size →
        PrimGraph.Symmetric size adjacency →
        Algo2Lean.Kruskal.ConnectedOn size.toNat (inputEdges size adjacency) →
        ∃ after,
          prim_fibonacci.Call heap (graph,root) after heap.nextRef ∧
          GraphRep after graph size heads adjacency ∧
          MinimumSpanningParents size adjacency root (after.read heap.nextRef) ∧
          clockWork (Heap.cost heap after) ≤ C * runtimeScale size adjacency ∧
          heap.nextRef < after.nextRef ∧ heap.Footprint after [] [] [] := by
  refine ⟨50, by decide, ?_⟩
  intro heap graph size root heads adjacency representation rootLower rootUpper symmetric connected
  obtain ⟨after,run,graphAfter,correct,_,bound,fresh,footprint⟩ :=
    summary heap graph size root heads adjacency representation rootLower rootUpper symmetric connected
  exact ⟨after,run,graphAfter,correct,
    Nat.le_trans bound (runtimeBound_le size adjacency (by omega)),fresh,footprint⟩

end FibonacciPrimAnalysis
