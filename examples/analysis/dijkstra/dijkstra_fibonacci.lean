import Algo.dijkstra.dijkstra_fibonacci.Generated
import Algo.dijkstra.dijkstra_fibonacci.Facts
import Algo.dijkstra.dijkstra.Analysis
import Algo.dijkstra.support.fibonacci_queue.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The concrete wrapper constructs a queue and client arrays, then applies the
    unchanged generic Dijkstra theorem and the independent queue contract. -/

namespace FibonacciDijkstraAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.graph.Algo2LeanGenerated
open Algo.dijkstra.dijkstra_fibonacci
open ComposableDijkstraAnalysis

/-- Generated binding theorems connect independently compiled source methods. -/
def bridge : FibonacciQueueAnalysis.Bridge FibonacciHeap_as_PriorityQueue where
  valid := by intro heap ref; simp [FibonacciHeap_as_PriorityQueue]
  is_empty := FibonacciHeap_as_PriorityQueue_summary_is_empty
  update := FibonacciHeap_as_PriorityQueue_summary_push_or_decrease
  extract := FibonacciHeap_as_PriorityQueue_summary_pop_min

/-- The wrapper's own steps only allocate its inputs and call imported code. -/
theorem call (heap queuedHeap finalHeap : Heap) (graph : Ref_Graph) (source size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (constructor : Algo.fibonacci_heap.FibonacciHeap.Call
      ((heap.allocate (fun _ => -1)).allocate (fun _ => 0)) () queuedHeap heap.nextObject)
    (search : Algo.dijkstra.dijkstra.dijkstra.Call use_dijkstra_dijkstra_0
      queuedHeap (graph,source,heap.nextObject,heap.nextRef,heap.nextRef+1) finalHeap heap.nextRef)
    (allocated : heap.nextRef < finalHeap.nextRef) :
    dijkstra_fibonacci.Call heap (graph,source) finalHeap heap.nextRef := by
  have sizeAfter : field_Graph_size (heap.allocate (fun _ => -1)) graph = some size := readSize
  open Algo.dijkstra.dijkstra_fibonacci.Algo2LeanGenerated in
    refine ⟨valid,?_⟩
    intro caller
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc19 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc18 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc17 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc16 _ _ caller (by simp [field__a2l_import_0_Graph_size,sizeAfter]))
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc15_false _ _ caller
      (by simp [field__a2l_import_0_Graph_size,sizeAfter]; omega))
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc12 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc11 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc10 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc9 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller constructor.2).trans
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc8 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc7 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc6 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc5 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc4 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc3 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc2 _ _ caller)
    apply (ModuleCall.summary import_3_use_dijkstra_dijkstra_0_simulates _ caller search.2).trans
    exact Reaches.single (Step.dijkstra_fibonacci_pc1 _ _ caller allocated)

/-- Invalid sources return a fresh all-unreachable sequence at zero clock cost. -/
theorem invalid_source (heap : Heap) (graph : Ref_Graph) (source size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source) :
    dijkstra_fibonacci.Call heap (graph,source) (heap.allocate (fun _ => -1)) heap.nextRef := by
  have sizeAfter : field_Graph_size (heap.allocate (fun _ => -1)) graph = some size := readSize
  open Algo.dijkstra.dijkstra_fibonacci.Algo2LeanGenerated in
    refine ⟨valid,?_⟩
    intro caller
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc19 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc18 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc17 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc16 _ _ caller (by simp [field__a2l_import_0_Graph_size,sizeAfter]))
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc15_true _ _ caller
      (by simpa [field__a2l_import_0_Graph_size,sizeAfter] using invalid))
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc14 _ _ caller)
    exact Reaches.single (Step.dijkstra_fibonacci_pc13 _ _ caller (by simp))

/-- Every explicit backend and client counter occurs once in this metric. -/
def clockWork (costs : Clocks) : Nat :=
  Clocks.weighted FibonacciQueueAnalysis.metric costs + costs "queue_updates" + costs "queue_pops" +
    costs "queue_empty_checks" + costs "edges" + costs "improvements" + costs "settlements"

def runtimeBound (size : Int) (adjacency : Adjacency) : Nat :=
  (20 + 3) * (edgeBudget adjacency (vertexRange size) + 1) + ((12 * (2 * size.toNat.log2 + 2)) + 3) * size.toNat

/-- A represented graph alone supplies all constructor and queue preconditions.
    The result is freshly allocated, and all pre-existing sequences, objects,
    and typed collections retain their contents. No queue-layout assumptions
    appear in this public contract. -/
theorem summary (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) :
    ∃ after,
      dijkstra_fibonacci.Call heap (graph,source) after heap.nextRef ∧
      GraphRep after graph size heads adjacency ∧
      ShortestDistances (representedEdges size adjacency) source (after.read heap.nextRef) ∧
      OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      clockWork (Heap.cost heap after) ≤ runtimeBound size adjacency ∧ heap.nextRef < after.nextRef ∧
      heap.Footprint after [] [] [] := by
  let allocated := (heap.allocate (fun _ => -1)).allocate (fun _ => 0)
  let client : Client := ⟨graph,size,heads,adjacency,heap.nextRef,heap.nextRef+1,heap.nextObject,heap⟩
  let model : PriorityQueueAnalysis.Model use_dijkstra_dijkstra_0.PriorityQueue client.queue client.protection := FibonacciQueueAnalysis.model FibonacciHeap_as_PriorityQueue bridge heap.nextObject client.protection size
  let initial : QueueState (dependencies := use_dijkstra_dijkstra_0) (client := client) model := ⟨FibonacciModuleAnalysis.newHeap allocated,FibonacciQueueAnalysis.initialState allocated⟩
  have allocatedGraph : GraphRep allocated graph size heads adjacency :=
    representation.preserved ((graph_frame_allocate _ _ _ (fun _ => -1)).trans
      (graph_frame_allocate _ _ _ (fun _ => 0)))
  have protectedFrame := FibonacciQueueAnalysis.constructor_frame allocated client.protection
  have distanceAllocated : client.distance < allocated.nextRef := by
    change heap.nextRef < heap.nextRef + 1 + 1
    omega
  have settledAllocated : client.settled < allocated.nextRef := by
    change heap.nextRef + 1 < heap.nextRef + 1 + 1
    omega
  have queueRep := FibonacciQueueAnalysis.constructor_rep allocated client.protection size (by
    intro ref member
    simp only [Client.protection,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact distanceAllocated
    · exact settledAllocated)
    (((Heap.Footprint.refl heap [] [] []).allocate (fun _ => -1)).allocate (fun _ => 0)) (by
      intro ref member
      simp only [Client.protection, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [client, Client.protection])
  have storage : Storage (dependencies := use_dijkstra_dijkstra_0) (client := client) model initial := by
    refine ⟨allocatedGraph.preserved (graph_frame_of_protected allocatedGraph protectedFrame),queueRep,?_,?_,?_⟩
    · exact Nat.lt_of_lt_of_le distanceAllocated protectedFrame.nextRef
    · exact Nat.lt_of_lt_of_le settledAllocated protectedFrame.nextRef
    · simp [client]
  have distances : initial.heap.read client.distance = fun _ => -1 := by
    rw [protectedFrame.sequences client.distance (by simp [Client.protection]) distanceAllocated]
    funext vertex
    simp [client,allocated,Heap.read,Heap.allocate]
  have flags : initial.heap.read client.settled = fun _ => 0 := by
    rw [protectedFrame.sequences client.settled (by simp [Client.protection]) settledAllocated]
    funext vertex
    simp [client,allocated,Heap.read,Heap.allocate]
  have sameClocks : initial.heap.clocks = heap.clocks :=
    FibonacciQueueAnalysis.constructor_clocks allocated
  have contracts : PriorityQueueAnalysis.Contracts model reservedClocks :=
    FibonacciQueueAnalysis.contracts FibonacciHeap_as_PriorityQueue bridge heap.nextObject client.protection size reservedClocks
      (by simp [Client.protection]) (by intro name member; simp [reservedClocks] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨after,search,graphAfter,correct,counts,workBound,resultAllocated,preserved⟩ :=
    dijkstra_complete model contracts (Int.le_refl _) initial source storage (by rfl) distances flags sourceLower sourceUpper
  have sameCost : Heap.cost initial.heap after = Heap.cost heap after := by
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
  refine ⟨after,call heap initial.heap after graph source size representation.valid representation.readSize
    sourceLower sourceUpper (FibonacciModuleAnalysis.new_heap_summary allocated) search resultAllocated,
    graphAfter,correct,costs,?_,resultAllocated,preserved⟩
  have updates := costs.updates
  have pops := costs.pops
  have checks := costs.checks
  have edges := costs.visits
  have improvements := costs.improvements
  have settlements := costs.settlements
  change Clocks.weighted model.metric (Heap.cost initial.heap after) ≤ _ at workBound
  rw [sameCost] at workBound
  simp [client,model,FibonacciQueueAnalysis.model,QueueState.potential,initial,FibonacciQueueAnalysis.initialState,Algo2Lean.Fibonacci.scaledPotential,Algo2Lean.Fibonacci.potential,Algo2Lean.Fibonacci.Forest.counts,Algo2Lean.Fibonacci.Forest.marks] at workBound
  simp only [clockWork,runtimeBound,Nat.add_mul,Nat.mul_add,Nat.mul_one] at workBound ⊢
  omega

/-- Every completed wrapper execution has the proved result, counts, and total runtime. -/
theorem every_execution (heap after : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (result : SeqRef)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (execution : dijkstra_fibonacci.Run heap (graph,source) after result) :
    result = heap.nextRef ∧
      ShortestDistances (representedEdges size adjacency) source (after.read result) ∧
      OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      clockWork (Heap.cost heap after) ≤ runtimeBound size adjacency := by
  obtain ⟨verified,run,_,correct,counts,bound,_⟩ := summary heap graph size source heads adjacency
    representation sourceLower sourceUpper
  obtain ⟨rfl,rfl⟩ := execution.eq_of_call run
  exact ⟨rfl,correct,counts,bound⟩

/-- Existence and runtime use the same ordinary-output execution witness. -/
theorem output_exists (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) :
    ∃ output costs, dijkstra_fibonacci.ReturnsWithCost (heap,graph,source) output costs ∧
      ShortestDistances (representedEdges size adjacency) source output ∧
      clockWork costs ≤ runtimeBound size adjacency := by
  obtain ⟨after,run,_,correct,_,bound,_⟩ := summary heap graph size source heads adjacency
    representation sourceLower sourceUpper
  exact ⟨after.read heap.nextRef,Heap.cost heap after,
    ⟨after,heap.nextRef,run.run,rfl,rfl⟩,correct,bound⟩

-- Main result: Correctness and running time
/-- Every ordinary output has shortest distances and the total source-clock bound. -/
theorem output_with_cost_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (output : Seq) (costs : Clocks)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (execution : dijkstra_fibonacci.ReturnsWithCost (heap,graph,source) output costs) :
    ShortestDistances (representedEdges size adjacency) source output ∧
      clockWork costs ≤ runtimeBound size adjacency := by
  obtain ⟨after,result,run,value,clocks⟩ := execution
  obtain ⟨_,correct,_,bound⟩ := every_execution heap after graph size source heads adjacency result
    representation sourceLower sourceUpper run
  change after.read result = output at value
  change Heap.cost heap after = costs at clocks
  rw [←value,←clocks]
  exact ⟨correct,bound⟩

/-- The invalid-source branch has no queue construction or operation charges. -/
theorem invalid_source_output (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source) :
    dijkstra_fibonacci.ReturnsWithCost (heap,graph,source) (fun _ => -1) (fun _ => 0) := by
  refine ⟨heap.allocate (fun _ => -1),heap.nextRef,
    (invalid_source heap graph source size valid readSize invalid).run,?_,?_⟩
  · funext index
    simp [Heap.allocate]
  · funext name
    simp [Heap.cost,Heap.allocate,dijkstra_fibonacci.load]

/-- Every source integer terminates on a represented graph; invalid sources return all -1. -/
theorem terminates (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency) :
    ∃ output costs, dijkstra_fibonacci.ReturnsWithCost (heap,graph,source) output costs := by
  by_cases valid : 0 ≤ source ∧ source < size
  · obtain ⟨output,costs,run,_,_⟩ := output_exists heap graph size source heads adjacency
      representation valid.1 valid.2
    exact ⟨output,costs,run⟩
  · exact ⟨(fun _ => -1),(fun _ => 0),invalid_source_output heap graph size source
      representation.valid representation.readSize (by omega)⟩

end FibonacciDijkstraAnalysis
