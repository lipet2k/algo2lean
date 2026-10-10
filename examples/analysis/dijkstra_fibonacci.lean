import DijkstraFibonacciGeneratedPoints
import DijkstraFibonacciDeterminism
import Algo2LeanLib.Dijkstra
import Algo2LeanLib.DijkstraExecution
import Algo2LeanLib.HeapFrame
import Algo2LeanExamples.FibonacciHeap
import FibonacciHeapIntoDijkstra
import Algo2LeanExamples.Graph
import GraphIntoDijkstraFibonacci

/-!
Fibonacci-heap Dijkstra: terminating execution, shortest-path correctness, and
an O(E + V log V) bound on actual source ticks. The graph representation,
shortest-path mathematics, and finite outer driver are shared with binary-heap
Dijkstra. The standalone heap proofs supply all three local QueueContracts
through a checked compilation-unit embedding. The final public theorems need
only a represented graph and, for shortest distances, a valid source vertex.
No theorem assumes whole-program correctness, a search run, or termination.
-/

namespace DijkstraFibonacciAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra

/-! Shared graph representations retain the same field observations in both
Dijkstra compilations. Only executable summaries need a checked control-state adapter. -/

abbrev AdjacencyChain := GraphAnalysis.AdjacencyChain
abbrev GraphRep := GraphAnalysis.GraphRep
abbrev GraphFrame := GraphAnalysis.GraphFrame
abbrev EdgeFieldsUnchanged := GraphAnalysis.EdgeFieldsUnchanged
abbrev newGraphHeap := GraphAnalysis.newGraphHeap
abbrev addedEdgeHeap := GraphAnalysis.addedEdgeHeap
abbrev prependEdge := GraphAnalysis.prependEdge

/-- The common graph constructor has the same compiled summary in this algorithm. -/
theorem graph_constructor_summary (heap : Heap) (size : Int) :
    Graph.Call heap size (newGraphHeap heap size) heap.nextObject :=
  GraphIntoDijkstraFibonacci.summary_Graph (GraphAnalysis.graph_constructor_summary heap size)

theorem graph_constructor_verified (heap : Heap) (size : Int) :
    Graph.Call heap size (newGraphHeap heap size) heap.nextObject ∧
    GraphRep (newGraphHeap heap size) heap.nextObject (max 0 size) heap.nextCollection (fun _ => []) ∧
    Heap.cost heap (newGraphHeap heap size) = (fun _ => 0) := by
  obtain ⟨execution, representation, cost⟩ := GraphAnalysis.graph_constructor_verified heap size
  exact ⟨GraphIntoDijkstraFibonacci.summary_Graph execution, representation, cost⟩

/-- Graph building reuses the independently checked finite adjacency representation. -/
theorem add_edge_preserves_representation (heap : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (source target weight : Int)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (targetNonnegative : 0 ≤ target) (targetBound : target < size)
    (weightNonnegative : 0 ≤ weight) :
    ∃ after, Graph.add_edge.Call heap (graph, source, target, weight) after true ∧
      GraphRep after graph size heads (prependEdge adjacency source target weight) ∧
      Heap.cost heap after = (fun _ => 0) := by
  obtain ⟨after, execution, represented, cost⟩ := GraphAnalysis.add_edge_preserves_representation
    heap graph size heads adjacency source target weight representation sourceNonnegative sourceBound
    targetNonnegative targetBound weightNonnegative
  exact ⟨after, GraphIntoDijkstraFibonacci.summary_Graph_add_edge execution, represented, cost⟩

/-- Queue-object field writes preserve every graph and edge observation. -/
theorem graph_frame_queue_field (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (queue : Ref_FibonacciHeap) (validQueue : is_FibonacciHeap heap queue)
    (field : String) (value : ObjectValue) :
    GraphFrame heap (heap.writeField queue field value) graph heads :=
  GraphAnalysis.graph_frame_foreign_field heap graph heads queue "FibonacciHeap" validQueue.2
    (by decide) (by decide) field value


/-! These are actual compiled call contracts imported from the standalone
heap analysis. The checked adapter changes only the caller's control types;
all heap effects, observations, and costs are reused verbatim. -/

namespace Queue

abbrev Layout := FibonacciHeapAnalysis.Layout

theorem constructor_summary (heap : Heap) :
    FibonacciHeap.Call heap () (FibonacciHeapAnalysis.newHeap heap) heap.nextObject :=
  FibonacciQueueEmbedding.summary_FibonacciHeap (FibonacciHeapAnalysis.new_heap_summary heap)

theorem remove_from_ring_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    FibonacciHeap.remove_from_ring.Call heap (queue, vertex)
      (FibonacciHeapAnalysis.removeHeap heap layout vertex) () :=
  FibonacciQueueEmbedding.summary_FibonacciHeap_remove_from_ring
    (FibonacciHeapAnalysis.remove_from_ring_summary heap queue layout valid vertex)

theorem add_root_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    FibonacciHeap.add_root.Call heap (queue, vertex)
      (FibonacciHeapAnalysis.addRootHeap heap queue layout vertex) () :=
  FibonacciQueueEmbedding.summary_FibonacciHeap_add_root
    (FibonacciHeapAnalysis.add_root_summary heap queue layout valid vertex)

theorem link_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (child parent : Int) :
    FibonacciHeap.link.Call heap (queue, child, parent)
      (FibonacciHeapAnalysis.linkHeap heap layout child parent) () :=
  FibonacciQueueEmbedding.summary_FibonacciHeap_link
    (FibonacciHeapAnalysis.link_summary heap queue layout valid child parent)

theorem cut_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex parent : Int) :
    FibonacciHeap.cut.Call heap (queue, vertex, parent)
      (FibonacciHeapAnalysis.cutHeap heap queue layout vertex parent) () :=
  FibonacciQueueEmbedding.summary_FibonacciHeap_cut
    (FibonacciHeapAnalysis.cut_summary heap queue layout valid vertex parent)

end Queue

/-! Local execution contracts establish
the effect of one edge relaxation and the complete invalid-source behavior.
The graph-level correctness proof composes these local execution contracts. -/

/-- The named assignment updates exactly the supplied distance cell. This is a
    local statement: no function-entry or whole-transcript premise is needed. -/
theorem improve_heap_effect (before after : Configuration)
    (distance : SeqRef) (target candidate : Int)
    (location : dijkstra.At.improve before)
    (readDistance : dijkstra.Local.distance before = some distance)
    (readTarget : dijkstra.Local.target before = some target)
    (readCandidate : dijkstra.Local.candidate before = some candidate)
    (transition : Step before after) :
    after.heap = before.heap.write distance target candidate := by
  unfold dijkstra.At.improve at location
  split at location <;> try contradiction
  cases transition
  simp_all [dijkstra.Local.distance, dijkstra.Local.target, dijkstra.Local.candidate, Config.heap]

theorem improve_sets_distance (before after : Configuration)
    (distance : SeqRef) (target candidate : Int)
    (location : dijkstra.At.improve before)
    (readDistance : dijkstra.Local.distance before = some distance)
    (readTarget : dijkstra.Local.target before = some target)
    (readCandidate : dijkstra.Local.candidate before = some candidate)
    (transition : Step before after) :
    after.heap.read distance target = candidate := by
  rw [improve_heap_effect before after distance target candidate location readDistance
    readTarget readCandidate transition]
  simp

theorem improve_preserves_other_distance (before after : Configuration)
    (distance : SeqRef) (target candidate other : Int)
    (location : dijkstra.At.improve before)
    (readDistance : dijkstra.Local.distance before = some distance)
    (readTarget : dijkstra.Local.target before = some target)
    (readCandidate : dijkstra.Local.candidate before = some candidate)
    (transition : Step before after) (different : other ≠ target) :
    after.heap.read distance other = before.heap.read distance other := by
  rw [improve_heap_effect before after distance target candidate location readDistance
    readTarget readCandidate transition]
  simp [different]

/-- Invalid sources return a fresh constant `-1` sequence. No queue, adjacency
    list, or clock is touched, even when the caller already has mutable data. -/
theorem invalid_source_summary (heap : Heap) (graph : Ref_Graph) (source size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source) :
    dijkstra.Call heap (graph, source) (heap.allocate (fun _ => -1)) heap.nextRef := by
  have sizePreserved : field_Graph_size (heap.allocate (fun _ => -1)) graph = some size := by
    simpa [field_Graph_size, is_Graph, Heap.objectClass, Heap.readField] using readSize
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc46 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc45 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc44 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc43 _ _ _ (by simp [sizePreserved]))
  apply Reaches.prepend (Step.dijkstra_pc42_true _ _ _ (by simpa [sizePreserved] using invalid))
  apply Reaches.prepend (Step.dijkstra_pc41 _ _ _)
  exact Reaches.single (Step.dijkstra_pc40 _ _ _ (by simp))

/-- The boundary case has zero cost on every named clock, and the returned
    mathematical sequence equals `-1` at every integer index. -/
theorem invalid_source_output_with_cost (heap : Heap) (graph : Ref_Graph) (source size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source) :
    dijkstra.ReturnsWithCost (heap, graph, source) (fun _ => -1) (fun _ => 0) := by
  have summary := invalid_source_summary heap graph source size valid readSize invalid
  refine ⟨heap.allocate (fun _ => -1), heap.nextRef, ⟨summary.1, summary.2.root⟩, ?_, ?_⟩
  · funext index
    simp [Heap.allocate]
  · funext name
    simp [Heap.cost, dijkstra.load]

theorem invalid_source_output (heap : Heap) (graph : Ref_Graph) (source size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source) :
    dijkstra.Returns (heap, graph, source) (fun _ => -1) :=
  (invalid_source_output_with_cost heap graph source size valid readSize invalid).returns

/-- A local extraction-point observation, independent of any entry transcript. -/
def AtExtraction (state : Configuration) (heap : Heap) (graph : Ref_Graph)
    (distance settled : SeqRef) (queue : Ref_FibonacciHeap) : Prop :=
  dijkstra.At.extract state ∧ state.heap = heap ∧
  dijkstra.Local.graph state = some graph ∧ dijkstra.Local.distance state = some distance ∧
  dijkstra.Local.settled state = some settled ∧ dijkstra.Local.queue state = some queue

def settleHeap (heap : Heap) (settled : SeqRef) (vertex : Int) : Heap :=
  (heap.write settled vertex 1).tick "settlements"

/-- Initialization uses two reusable queue contracts, then hands the initialized
    local state to the extraction-loop proof. -/
theorem initialize_summary (heap queueHeap queuedHeap finalHeap : Heap)
    (graph : Ref_Graph) (queue : Ref_FibonacciHeap) (source size : Int) (result : SeqRef)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (constructor : FibonacciHeap.Call ((heap.allocate (fun _ => -1)).allocate (fun _ => 0))
      () queueHeap queue)
    (distanceAllocated : heap.nextRef < queueHeap.nextRef)
    (insertion : FibonacciHeap.push_or_decrease.Call (queueHeap.write heap.nextRef source 0)
      (queue, source, 0) queuedHeap ())
    (continuation : ∀ state,
      AtExtraction state queuedHeap graph heap.nextRef (heap.nextRef + 1) queue →
      dijkstra.CallFrom state finalHeap result) :
    dijkstra.Call heap (graph, source) finalHeap result := by
  have sizePreserved : field_Graph_size (heap.allocate (fun _ => -1)) graph = some size := by
    simpa [field_Graph_size, is_Graph, Heap.objectClass, Heap.readField] using readSize
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc46 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc45 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc44 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc43 _ _ _ (by simp [sizePreserved]))
  apply Reaches.prepend (Step.dijkstra_pc42_false _ _ _ (by simp [sizePreserved]; omega))
  apply Reaches.prepend (Step.dijkstra_pc39 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc38 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc37 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc36 _ _ _)
  apply Reaches.trans (constructor.2 _)
  apply Reaches.prepend (Step.dijkstra_pc35 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc34 _ _ _ distanceAllocated)
  apply Reaches.prepend (Step.dijkstra_pc33 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc32 _ _ _ (by exact insertion.1))
  apply Reaches.prepend (Step.dijkstra_pc31 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc30 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc29 _ _ _)
  apply Reaches.trans (insertion.2 _)
  apply (continuation (.active queuedHeap (.fn_dijkstra 4 _) []) ?_) caller
  simp [AtExtraction, dijkstra.At.extract, Config.heap, dijkstra.Local.graph,
    dijkstra.Local.distance, dijkstra.Local.settled, dijkstra.Local.queue]

/-- One final extraction suffices when the selected vertex has no outgoing
    edges. The queue's summary is reused as a call contract. -/
theorem final_extraction_summary (state : Configuration) (heap poppedHeap : Heap)
    (graph : Ref_Graph) (distance settled : SeqRef) (queue : Ref_FibonacciHeap)
    (vertex : Int) (heads : CollectionRef)
    (located : AtExtraction state heap graph distance settled queue)
    (queueSize : field_FibonacciHeap_size heap queue = some 1)
    (pop : FibonacciHeap.pop_min.Call heap queue poppedHeap vertex)
    (settledAllocated : settled < poppedHeap.nextRef)
    (distanceAllocated : distance < poppedHeap.nextRef)
    (queueEmpty : field_FibonacciHeap_size (settleHeap poppedHeap settled vertex) queue = some 0)
    (graphHeads : field_Graph_heads (settleHeap poppedHeap settled vertex) graph = some heads)
    (noEdges : seq_Edge_optional.get (settleHeap poppedHeap settled vertex) heads vertex = some none) :
    dijkstra.CallFrom state (settleHeap poppedHeap settled vertex) distance := by
  obtain ⟨location, sameHeap, readGraph, readDistance, readSettled, readQueue⟩ := located
  unfold dijkstra.At.extract at location
  split at location <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [dijkstra.Local.graph, dijkstra.Local.distance, dijkstra.Local.settled,
    dijkstra.Local.queue] at readGraph readDistance readSettled readQueue
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc4 _ _ _ (by simp [readQueue, queueSize]))
  apply Reaches.prepend (Step.dijkstra_pc3_true _ _ _ (by simp [readQueue, queueSize]))
  apply Reaches.prepend (Step.dijkstra_pc28 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc27 _ _ _ (by simpa [readQueue] using pop.1))
  apply Reaches.prepend (Step.dijkstra_pc26 _ _ _)
  simp only [readQueue]
  apply Reaches.trans (pop.2 _)
  apply Reaches.prepend (Step.dijkstra_pc25 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc24 _ _ _ (by simpa [readSettled] using settledAllocated))
  apply Reaches.prepend (Step.dijkstra_pc23 _ _ _)
  simp only [readSettled]
  change Reaches Step (.active (settleHeap poppedHeap settled vertex) _ _) _
  apply Reaches.prepend (Step.dijkstra_pc22 _ _ _ (by simp [readGraph, graphHeads, noEdges]))
  apply Reaches.prepend (Step.dijkstra_pc6 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc5_false _ _ _ (by simp [readGraph, graphHeads, noEdges]))
  apply Reaches.prepend (Step.dijkstra_pc4 _ _ _ (by simp [queueEmpty]))
  apply Reaches.prepend (Step.dijkstra_pc3_false _ _ _ (by simp [queueEmpty]))
  apply Reaches.prepend (Step.dijkstra_pc2 _ _ _)
  simpa [readDistance] using Reaches.single (Step.dijkstra_pc1
    (settleHeap poppedHeap settled vertex) _ caller (by simpa [settleHeap, readDistance] using distanceAllocated))


def AtEdges (state : Configuration) (heap : Heap) (graph : Ref_Graph)
    (distance settled : SeqRef) (queue : Ref_FibonacciHeap) (vertex : Int) (edge : Option Ref_Edge) : Prop :=
  dijkstra.At.edge_loop state ∧ state.heap = heap ∧
  dijkstra.Local.graph state = some graph ∧ dijkstra.Local.distance state = some distance ∧
  dijkstra.Local.settled state = some settled ∧ dijkstra.Local.queue state = some queue ∧
  dijkstra.Local.vertex state = some vertex ∧ dijkstra.Local.edge state = some edge

theorem extraction_to_edges (state : Configuration) (heap poppedHeap finalHeap : Heap)
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_FibonacciHeap)
    (vertex size : Int) (heads : CollectionRef) (edge : Option Ref_Edge)
    (located : AtExtraction state heap graph distance settled queue)
    (queueSize : field_FibonacciHeap_size heap queue = some size)
    (nonempty : 0 < size)
    (pop : FibonacciHeap.pop_min.Call heap queue poppedHeap vertex)
    (settledAllocated : settled < poppedHeap.nextRef)
    (graphHeads : field_Graph_heads (settleHeap poppedHeap settled vertex) graph = some heads)
    (readEdge : seq_Edge_optional.get (settleHeap poppedHeap settled vertex) heads vertex = some edge)
    (continuation : ∀ next, AtEdges next (settleHeap poppedHeap settled vertex)
      graph distance settled queue vertex edge → dijkstra.CallFrom next finalHeap result) :
    dijkstra.CallFrom state finalHeap result := by
  obtain ⟨location, sameHeap, readGraph, readDistance, readSettled, readQueue⟩ := located
  unfold dijkstra.At.extract at location
  split at location <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [dijkstra.Local.graph, dijkstra.Local.distance, dijkstra.Local.settled,
    dijkstra.Local.queue] at readGraph readDistance readSettled readQueue
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc4 _ _ _ (by simp [readQueue, queueSize]))
  apply Reaches.prepend (Step.dijkstra_pc3_true _ _ _ (by simp [readQueue, queueSize, nonempty]))
  apply Reaches.prepend (Step.dijkstra_pc28 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc27 _ _ _ (by simpa [readQueue] using pop.1))
  apply Reaches.prepend (Step.dijkstra_pc26 _ _ _)
  simp only [readQueue]
  apply Reaches.trans (pop.2 _)
  apply Reaches.prepend (Step.dijkstra_pc25 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc24 _ _ _ (by simpa [readSettled] using settledAllocated))
  apply Reaches.prepend (Step.dijkstra_pc23 _ _ _)
  simp only [readSettled]
  change Reaches Step (.active (settleHeap poppedHeap settled vertex) _ _) _
  apply Reaches.prepend (Step.dijkstra_pc22 _ _ _ (by simp [readGraph, graphHeads, readEdge]))
  apply (continuation (.active (settleHeap poppedHeap settled vertex) (.fn_dijkstra 6 _) []) ?_) caller
  simp [AtEdges, dijkstra.At.edge_loop, Config.heap, dijkstra.Local.graph,
    dijkstra.Local.distance, dijkstra.Local.settled, dijkstra.Local.queue,
    dijkstra.Local.vertex, dijkstra.Local.edge, readGraph, readDistance, graphHeads, readEdge]

theorem empty_edges_continue (state : Configuration) (heap finalHeap : Heap)
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_FibonacciHeap) (vertex : Int)
    (located : AtEdges state heap graph distance settled queue vertex none)
    (continuation : ∀ next, AtExtraction next heap graph distance settled queue →
      dijkstra.CallFrom next finalHeap result) : dijkstra.CallFrom state finalHeap result := by
  obtain ⟨location, sameHeap, readGraph, readDistance, readSettled, readQueue, readVertex, readEdge⟩ := located
  unfold dijkstra.At.edge_loop at location
  split at location <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [dijkstra.Local.graph, dijkstra.Local.distance, dijkstra.Local.settled,
    dijkstra.Local.queue, dijkstra.Local.vertex, dijkstra.Local.edge]
    at readGraph readDistance readSettled readQueue readVertex readEdge
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc6 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc5_false _ _ _ (by simp [readEdge]))
  apply (continuation (.active heap (.fn_dijkstra 4 _) []) ?_) caller
  simp [AtExtraction, dijkstra.At.extract, Config.heap, dijkstra.Local.graph,
    dijkstra.Local.distance, dijkstra.Local.settled, dijkstra.Local.queue,
    readGraph, readDistance, readSettled, readQueue]

def relaxationHeap (heap : Heap) (distance : SeqRef) (target candidate : Int) : Heap :=
  (heap.tick "edges").write distance target candidate

/-- One successful relaxation: charge the edge, update its tentative distance,
    reuse the queue insertion/decrease contract, then advance to the next edge. -/
theorem improve_edge_continue (state : Configuration) (heap queuedHeap finalHeap : Heap)
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_FibonacciHeap)
    (vertex target weight : Int) (edge : Ref_Edge) (nextEdge : Option Ref_Edge)
    (located : AtEdges state heap graph distance settled queue vertex (some edge))
    (distanceAllocated : distance < heap.nextRef) (settledAllocated : settled < heap.nextRef)
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (unsettled : heap.read settled target = 0)
    (better : heap.read distance target < 0 ∨ heap.read distance vertex + weight < heap.read distance target)
    (insertion : FibonacciHeap.push_or_decrease.Call
      (relaxationHeap heap distance target (heap.read distance vertex + weight))
      (queue, target, heap.read distance vertex + weight) queuedHeap ())
    (readNext : field_Edge_next (queuedHeap.tick "improvements") edge = some nextEdge)
    (continuation : ∀ next, AtEdges next (queuedHeap.tick "improvements")
      graph distance settled queue vertex nextEdge → dijkstra.CallFrom next finalHeap result) :
    dijkstra.CallFrom state finalHeap result := by
  obtain ⟨location, sameHeap, readGraph, readDistance, readSettled, readQueue, readVertex, readEdge⟩ := located
  unfold dijkstra.At.edge_loop at location
  split at location <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [dijkstra.Local.graph, dijkstra.Local.distance, dijkstra.Local.settled,
    dijkstra.Local.queue, dijkstra.Local.vertex, dijkstra.Local.edge]
    at readGraph readDistance readSettled readQueue readVertex readEdge
  have targetAfterTick : field_Edge_target (heap.tick "edges") edge = some target := readTarget
  have weightAfterTick : field_Edge_weight (heap.tick "edges") edge = some weight := readWeight
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc6 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc5_true _ _ _ (by simp [readEdge]))
  apply Reaches.prepend (Step.dijkstra_pc21 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc20 _ _ _ (by simp [readEdge, targetAfterTick]))
  apply Reaches.prepend (Step.dijkstra_pc19 _ _ _ (by simpa [readSettled] using settledAllocated))
  apply Reaches.prepend (Step.dijkstra_pc18_true _ _ _
    (by simp [readSettled, readEdge, targetAfterTick, unsettled]))
  apply Reaches.prepend (Step.dijkstra_pc17 _ _ _
    (by simp [readDistance, distanceAllocated, readEdge, weightAfterTick]))
  apply Reaches.prepend (Step.dijkstra_pc16 _ _ _ (by simp [readDistance, distanceAllocated]))
  apply Reaches.prepend (Step.dijkstra_pc15_true _ _ _
    (by simpa [readDistance, readVertex, readEdge, targetAfterTick, weightAfterTick] using better))
  apply Reaches.prepend (Step.dijkstra_pc14 _ _ _ (by simpa [readDistance] using distanceAllocated))
  apply Reaches.prepend (Step.dijkstra_pc13 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc12 _ _ _
    (by simpa [relaxationHeap, readQueue] using insertion.1))
  apply Reaches.prepend (Step.dijkstra_pc11 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc10 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc9 _ _ _)
  simp only [readDistance, readVertex, readEdge, readQueue, targetAfterTick, weightAfterTick, Option.getD_some]
  apply Reaches.trans (insertion.2 _)
  apply Reaches.prepend (Step.dijkstra_pc8 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc7 _ _ _ (by simp [readNext]))
  apply (continuation (.active (queuedHeap.tick "improvements") (.fn_dijkstra 6 _) []) ?_) caller
  simp [AtEdges, dijkstra.At.edge_loop, Config.heap, dijkstra.Local.graph,
    dijkstra.Local.distance, dijkstra.Local.settled, dijkstra.Local.queue,
    dijkstra.Local.vertex, dijkstra.Local.edge, readGraph, readSettled, readNext]


/-- An empty extraction queue returns the current distance sequence unchanged. -/
theorem extraction_done (state : Configuration) (heap : Heap)
    (graph : Ref_Graph) (distance settled : SeqRef) (queue : Ref_FibonacciHeap)
    (located : AtExtraction state heap graph distance settled queue)
    (queueEmpty : field_FibonacciHeap_size heap queue = some 0)
    (distanceAllocated : distance < heap.nextRef) :
    dijkstra.CallFrom state heap distance := by
  obtain ⟨location, sameHeap, readGraph, readDistance, readSettled, readQueue⟩ := located
  unfold dijkstra.At.extract at location
  split at location <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [dijkstra.Local.distance, dijkstra.Local.queue] at readDistance readQueue
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc4 _ _ _ (by simp [readQueue, queueEmpty]))
  apply Reaches.prepend (Step.dijkstra_pc3_false _ _ _ (by simp [readQueue, queueEmpty]))
  apply Reaches.prepend (Step.dijkstra_pc2 _ _ _)
  simpa [readDistance] using Reaches.single (Step.dijkstra_pc1 heap _ caller
    (by simpa [readDistance] using distanceAllocated))

/-- An edge to an already settled vertex charges one edge visit and advances;
    it neither changes distances nor calls the queue. -/
theorem settled_edge_continue (state : Configuration) (heap finalHeap : Heap)
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_FibonacciHeap)
    (vertex target : Int) (edge : Ref_Edge) (nextEdge : Option Ref_Edge)
    (located : AtEdges state heap graph distance settled queue vertex (some edge))
    (settledAllocated : settled < heap.nextRef)
    (readTarget : field_Edge_target heap edge = some target)
    (alreadySettled : heap.read settled target ≠ 0)
    (readNext : field_Edge_next heap edge = some nextEdge)
    (continuation : ∀ next, AtEdges next (heap.tick "edges")
      graph distance settled queue vertex nextEdge → dijkstra.CallFrom next finalHeap result) :
    dijkstra.CallFrom state finalHeap result := by
  obtain ⟨location, sameHeap, readGraph, readDistance, readSettled, readQueue, readVertex, readEdge⟩ := located
  unfold dijkstra.At.edge_loop at location
  split at location <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [dijkstra.Local.graph, dijkstra.Local.distance, dijkstra.Local.settled,
    dijkstra.Local.queue, dijkstra.Local.vertex, dijkstra.Local.edge]
    at readGraph readDistance readSettled readQueue readVertex readEdge
  have targetAfterTick : field_Edge_target (heap.tick "edges") edge = some target := readTarget
  have nextAfterTick : field_Edge_next (heap.tick "edges") edge = some nextEdge := readNext
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc6 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc5_true _ _ _ (by simp [readEdge]))
  apply Reaches.prepend (Step.dijkstra_pc21 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc20 _ _ _ (by simp [readEdge, targetAfterTick]))
  apply Reaches.prepend (Step.dijkstra_pc19 _ _ _ (by simpa [readSettled] using settledAllocated))
  apply Reaches.prepend (Step.dijkstra_pc18_false _ _ _
    (by simp [readSettled, readEdge, targetAfterTick, alreadySettled]))
  apply Reaches.prepend (Step.dijkstra_pc7 _ _ _ (by simp [readEdge, nextAfterTick]))
  apply (continuation (.active (heap.tick "edges") (.fn_dijkstra 6 _) []) ?_) caller
  simp [AtEdges, dijkstra.At.edge_loop, Config.heap, dijkstra.Local.graph,
    dijkstra.Local.distance, dijkstra.Local.settled, dijkstra.Local.queue,
    dijkstra.Local.vertex, dijkstra.Local.edge, readGraph, readDistance,
    readSettled, readQueue, readVertex, readEdge, nextAfterTick]

/-- A candidate no smaller than an existing finite distance only charges the
    edge visit. This includes equal candidates from parallel or zero-weight edges. -/
theorem unimproved_edge_continue (state : Configuration) (heap finalHeap : Heap)
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_FibonacciHeap)
    (vertex target weight : Int) (edge : Ref_Edge) (nextEdge : Option Ref_Edge)
    (located : AtEdges state heap graph distance settled queue vertex (some edge))
    (distanceAllocated : distance < heap.nextRef) (settledAllocated : settled < heap.nextRef)
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (unsettled : heap.read settled target = 0)
    (finite : 0 ≤ heap.read distance target)
    (noBetter : heap.read distance target ≤ heap.read distance vertex + weight)
    (readNext : field_Edge_next heap edge = some nextEdge)
    (continuation : ∀ next, AtEdges next (heap.tick "edges")
      graph distance settled queue vertex nextEdge → dijkstra.CallFrom next finalHeap result) :
    dijkstra.CallFrom state finalHeap result := by
  obtain ⟨location, sameHeap, readGraph, readDistance, readSettled, readQueue, readVertex, readEdge⟩ := located
  unfold dijkstra.At.edge_loop at location
  split at location <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [dijkstra.Local.graph, dijkstra.Local.distance, dijkstra.Local.settled,
    dijkstra.Local.queue, dijkstra.Local.vertex, dijkstra.Local.edge]
    at readGraph readDistance readSettled readQueue readVertex readEdge
  have targetAfterTick : field_Edge_target (heap.tick "edges") edge = some target := readTarget
  have weightAfterTick : field_Edge_weight (heap.tick "edges") edge = some weight := readWeight
  have nextAfterTick : field_Edge_next (heap.tick "edges") edge = some nextEdge := readNext
  intro caller
  apply Reaches.prepend (Step.dijkstra_pc6 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc5_true _ _ _ (by simp [readEdge]))
  apply Reaches.prepend (Step.dijkstra_pc21 _ _ _)
  apply Reaches.prepend (Step.dijkstra_pc20 _ _ _ (by simp [readEdge, targetAfterTick]))
  apply Reaches.prepend (Step.dijkstra_pc19 _ _ _ (by simpa [readSettled] using settledAllocated))
  apply Reaches.prepend (Step.dijkstra_pc18_true _ _ _
    (by simp [readSettled, readEdge, targetAfterTick, unsettled]))
  apply Reaches.prepend (Step.dijkstra_pc17 _ _ _
    (by simp [readDistance, distanceAllocated, readEdge, weightAfterTick]))
  apply Reaches.prepend (Step.dijkstra_pc16 _ _ _ (by simp [readDistance, distanceAllocated]))
  apply Reaches.prepend (Step.dijkstra_pc15_false _ _ _
    (by simp [readDistance, readVertex, readEdge, targetAfterTick, weightAfterTick]; omega))
  apply Reaches.prepend (Step.dijkstra_pc7 _ _ _ (by simp [readEdge, nextAfterTick]))
  apply (continuation (.active (heap.tick "edges") (.fn_dijkstra 6 _) []) ?_) caller
  simp [AtEdges, dijkstra.At.edge_loop, Config.heap, dijkstra.Local.graph,
    dijkstra.Local.distance, dijkstra.Local.settled, dijkstra.Local.queue,
    dijkstra.Local.vertex, dijkstra.Local.edge, readGraph, readDistance,
    readSettled, readQueue, readVertex, readEdge, nextAfterTick]



/-! Conditional client proof. QueueContracts contains only independently
verifiable method contracts; it assumes no Dijkstra execution or graph theorem. -/

abbrev Forest := Algo2Lean.Fibonacci.Forest

structure Client where
  graph : Ref_Graph
  size : Int
  heads : CollectionRef
  adjacency : Adjacency
  distance : SeqRef
  settled : SeqRef
  queue : Ref_FibonacciHeap

structure QueueState where
  heap : Heap
  layout : Queue.Layout
  forest : Forest

def QueueState.potential (state : QueueState) : Nat :=
  Algo2Lean.Fibonacci.scaledPotential state.forest.counts

structure Storage (client : Client) (state : QueueState) : Prop where
  graph : GraphRep state.heap client.graph client.size client.heads client.adjacency
  queue : FibonacciHeapAnalysis.QueueRep state.heap client.queue state.layout state.forest
  distanceAllocated : client.distance < state.heap.nextRef
  settledAllocated : client.settled < state.heap.nextRef
  separate : client.distance ≠ client.settled
  distanceSeparate : client.distance ∉ state.layout.refs
  settledSeparate : client.settled ∉ state.layout.refs

def QueueState.tick (state : QueueState) (name : String) : QueueState :=
  {state with heap := state.heap.tick name}

def QueueState.write (state : QueueState) (ref : SeqRef) (index value : Int) : QueueState :=
  {state with heap := state.heap.write ref index value}

theorem Storage.tick {client : Client} {state : QueueState} (storage : Storage client state)
    (name : String) : Storage client (state.tick name) := by
  exact ⟨storage.graph.preserved (GraphAnalysis.graph_frame_tick _ _ _ name 1),
    ⟨FibonacciHeapAnalysis.Layout.Valid.tick _ _ _ storage.queue.layoutValid name 1,
      storage.queue.represented⟩, storage.distanceAllocated, storage.settledAllocated,
    storage.separate, storage.distanceSeparate, storage.settledSeparate⟩

theorem Storage.write {client : Client} {state : QueueState} (storage : Storage client state)
    (ref : SeqRef) (index value : Int) (separate : ref ∉ state.layout.refs) :
    Storage client (state.write ref index value) := by
  have read (r : SeqRef) (member : r ∈ state.layout.refs) :
      (state.heap.write ref index value).read r = state.heap.read r := by
    funext i
    exact Heap.read_write_other_ref _ _ _ _ _ _ (by intro same; exact separate (same ▸ member))
  have snapshot : FibonacciHeapAnalysis.snapshot (state.heap.write ref index value) state.layout =
      FibonacciHeapAnalysis.snapshot state.heap state.layout := by
    unfold FibonacciHeapAnalysis.snapshot
    congr 1 <;> apply read <;> simp [FibonacciHeapAnalysis.Layout.refs]
  refine ⟨storage.graph.preserved (GraphAnalysis.graph_frame_write _ _ _ ref index value),
    ⟨FibonacciHeapAnalysis.Layout.Valid.write _ _ _ storage.queue.layoutValid ref index value, ?_⟩,
    storage.distanceAllocated, storage.settledAllocated, storage.separate,
    storage.distanceSeparate, storage.settledSeparate⟩
  change Algo2Lean.Fibonacci.Represented (FibonacciHeapAnalysis.snapshot _ _) _
  dsimp only [QueueState.write]
  rw [snapshot]
  exact storage.queue.represented

def QueueMatches (client : Client) (state : QueueState) : Prop :=
  ∀ vertex key, (vertex, key) ∈ state.forest.entries ↔
    state.heap.read client.settled vertex = 0 ∧
    0 ≤ state.heap.read client.distance vertex ∧ key = state.heap.read client.distance vertex

def popBudget (size : Int) : Nat := 12 * (2 * size.toNat.log2 + 2)

/-- Both method results preserve client storage and carry their actual clock
    deltas. Forest entries are the abstract queue contents, not an execution. -/
structure QueueUpdated (client : Client) (before after : QueueState) (vertex key : Int) : Prop where
  execution : FibonacciHeap.push_or_decrease.Call before.heap
    (client.queue, vertex, key) after.heap ()
  storage : Storage client after
  contents : ∀ v k, (v,k) ∈ after.forest.entries ↔
    (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v,k) ∈ before.forest.entries)
  distance : after.heap.read client.distance = before.heap.read client.distance
  settled : after.heap.read client.settled = before.heap.read client.settled
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : ∀ name, name = "edges" ∨ name = "improvements" ∨ name = "settlements" →
    after.heap.clocks name = before.heap.clocks name
  amortized : FibonacciHeapAnalysis.heapEventWork before.heap after.heap + after.potential ≤
    before.potential + 20

structure QueueExtracted (client : Client) (before after : QueueState) (vertex key : Int) : Prop where
  execution : FibonacciHeap.pop_min.Call before.heap client.queue after.heap vertex
  storage : Storage client after
  selected : (vertex,key) ∈ before.forest.entries
  least : ∀ v k, (v,k) ∈ before.forest.entries → key ≤ k
  contents : ∀ v k, (v,k) ∈ after.forest.entries ↔ v ≠ vertex ∧ (v,k) ∈ before.forest.entries
  distance : after.heap.read client.distance = before.heap.read client.distance
  settled : after.heap.read client.settled = before.heap.read client.settled
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : ∀ name, name = "edges" ∨ name = "improvements" ∨ name = "settlements" →
    after.heap.clocks name = before.heap.clocks name
  amortized : FibonacciHeapAnalysis.heapEventWork before.heap after.heap + after.potential ≤
    before.potential + popBudget client.size

/-- The local interface between the Dijkstra proof and its queue implementation.
    Every field concerns one public queue method only. In particular no field
    assumes that Dijkstra terminates, produces shortest paths, or has a search run.
    The `verifiedQueueContracts` instance supplies every field. -/
structure QueueContracts : Prop where
  constructor : ∀ (heap : Heap) (graph : Ref_Graph) (size : Int) (heads : CollectionRef)
    (adjacency : Adjacency) (distance settled : SeqRef),
    GraphRep heap graph size heads adjacency → distance < heap.nextRef →
    settled < heap.nextRef → distance ≠ settled →
    ∃ after layout,
      FibonacciHeap.Call heap () after heap.nextObject ∧
      Storage ⟨graph,size,heads,adjacency,distance,settled,heap.nextObject⟩ ⟨after,layout,[]⟩ ∧
      after.read distance = heap.read distance ∧ after.read settled = heap.read settled ∧
      after.clocks = heap.clocks
  update : ∀ client before vertex key, Storage client before → 0 ≤ vertex →
    (∀ old, (vertex,old) ∈ before.forest.entries → key < old) →
    ∃ after, QueueUpdated client before after vertex key
  extract : ∀ client before, Storage client before → before.forest ≠ [] →
    (∀ vertex key, (vertex,key) ∈ before.forest.entries → 0 ≤ vertex ∧ vertex < client.size) →
    ∃ after vertex key, QueueExtracted client before after vertex key

/-- A finite unsettled vertex set and exact queue matching suffice for execution.
    The shared `SearchRun` relation supplies the shortest-path interpretation. -/
structure LoopInvariant (client : Client) (state : QueueState) (remaining : List Int) : Prop where
  storage : Storage client state
  matching : QueueMatches client state
  finiteInRange : ∀ vertex, 0 ≤ state.heap.read client.distance vertex →
    0 ≤ vertex ∧ vertex < client.size
  unique : remaining.Nodup
  members : ∀ vertex, vertex ∈ remaining ↔
    0 ≤ vertex ∧ vertex < client.size ∧ state.heap.read client.settled vertex = 0

/-- The measured seven heap clocks compose without assuming zero starting clocks. -/
theorem heap_event_work_trans (a b c : Heap) :
    FibonacciHeapAnalysis.heapEventWork a c ≤
      FibonacciHeapAnalysis.heapEventWork a b + FibonacciHeapAnalysis.heapEventWork b c := by
  have triangle (name : String) : Heap.cost a c name ≤ Heap.cost a b name + Heap.cost b c name := by
    unfold Heap.cost
    omega
  have h1 := triangle "heap_operations"
  have h2 := triangle "heap_comparisons"
  have h3 := triangle "heap_links"
  have h4 := triangle "heap_cuts"
  have h5 := triangle "heap_root_scans"
  have h6 := triangle "heap_degree_scans"
  have h7 := triangle "heap_promotions"
  simp only [FibonacciHeapAnalysis.heapEventWork]
  omega

structure CostBounds (before after : QueueState) (vertices edges size : Nat) : Prop where
  settlements : Heap.cost before.heap after.heap "settlements" ≤ vertices
  visits : Heap.cost before.heap after.heap "edges" ≤ edges
  improvements : Heap.cost before.heap after.heap "improvements" ≤ edges
  amortized : FibonacciHeapAnalysis.heapEventWork before.heap after.heap + after.potential ≤
    before.potential + 20 * edges + 12 * (2 * size.log2 + 2) * vertices

theorem CostBounds.refl (state : QueueState) (size : Nat) : CostBounds state state 0 0 size := by
  constructor <;> simp [Heap.cost, FibonacciHeapAnalysis.heapEventWork]

theorem CostBounds.trans {a b c : QueueState} {v e v' e' size : Nat}
    (one : CostBounds a b v e size) (two : CostBounds b c v' e' size) :
    CostBounds a c (v+v') (e+e') size := by
  have cost (name : String) : Heap.cost a.heap c.heap name ≤
      Heap.cost a.heap b.heap name + Heap.cost b.heap c.heap name := by
    unfold Heap.cost
    omega
  refine ⟨Nat.le_trans (cost _) (Nat.add_le_add one.settlements two.settlements),
    Nat.le_trans (cost _) (Nat.add_le_add one.visits two.visits),
    Nat.le_trans (cost _) (Nat.add_le_add one.improvements two.improvements), ?_⟩
  have work := heap_event_work_trans a.heap b.heap c.heap
  have first := one.amortized
  have second := two.amortized
  simp only [Nat.mul_add] at first second ⊢
  omega

theorem CostBounds.weaken {a b : QueueState} {v e v' e' size : Nat}
    (one : CostBounds a b v e size) (vertices : v ≤ v') (edges : e ≤ e') :
    CostBounds a b v' e' size := by
  refine ⟨Nat.le_trans one.settlements vertices, Nat.le_trans one.visits edges,
    Nat.le_trans one.improvements edges, ?_⟩
  exact Nat.le_trans one.amortized (Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left 20 edges) _)
    (Nat.mul_le_mul_left _ vertices))

theorem skip_edge_cost (state : QueueState) (size : Nat) :
    CostBounds state (state.tick "edges") 0 1 size := by
  constructor <;> simp [QueueState.tick, QueueState.potential, Heap.cost, Heap.tick,
    FibonacciHeapAnalysis.heapEventWork]

theorem updated_edge_cost {client : Client} {state after : QueueState} {target candidate : Int}
    (effect : QueueUpdated client ((state.tick "edges").write client.distance target candidate)
      after target candidate) :
    CostBounds state (after.tick "improvements") 0 1 client.size.toNat := by
  have settlements := effect.bookkeeping "settlements" (by simp)
  have visits := effect.bookkeeping "edges" (by simp)
  have improvements := effect.bookkeeping "improvements" (by simp)
  have work := effect.amortized
  constructor
  · simp [QueueState.tick, QueueState.write, Heap.cost, Heap.tick, Heap.write, settlements]
  · simp [QueueState.tick, QueueState.write, Heap.cost, Heap.tick, Heap.write, visits]
  · simp [QueueState.tick, QueueState.write, Heap.cost, Heap.tick, Heap.write, improvements]
  · simpa [QueueState.tick, QueueState.write, QueueState.potential,
      FibonacciHeapAnalysis.heapEventWork, Heap.cost, Heap.tick, Heap.write] using work

theorem extracted_settled_cost {client : Client} {state after : QueueState} {vertex key : Int}
    (effect : QueueExtracted client state after vertex key) :
    CostBounds state ((after.write client.settled vertex 1).tick "settlements")
      1 0 client.size.toNat := by
  have settlements := effect.bookkeeping "settlements" (by simp)
  have visits := effect.bookkeeping "edges" (by simp)
  have improvements := effect.bookkeeping "improvements" (by simp)
  have work := effect.amortized
  constructor
  · simp [QueueState.tick, QueueState.write, Heap.cost, Heap.tick, Heap.write, settlements]
  · simp [QueueState.tick, QueueState.write, Heap.cost, Heap.tick, Heap.write, visits]
  · simp [QueueState.tick, QueueState.write, Heap.cost, Heap.tick, Heap.write, improvements]
  · simpa [QueueState.tick, QueueState.write, QueueState.potential, popBudget,
      FibonacciHeapAnalysis.heapEventWork, Heap.cost, Heap.tick, Heap.write] using work

/-- Execution through a scan is a local continuation interface. -/
def EdgeScanSummary (client : Client) (before after : Heap) (selected : Int)
    (head : Option Ref_Edge) : Prop :=
  ∀ finalHeap result,
    (∀ state, AtExtraction state after client.graph client.distance client.settled client.queue →
      dijkstra.CallFrom state finalHeap result) →
    ∀ state, AtEdges state before client.graph client.distance client.settled client.queue selected head →
      dijkstra.CallFrom state finalHeap result

structure AdjacencyScanned (client : Client) (before after : QueueState)
    (selected : Int) (head : Option Ref_Edge) (edges : List (Int × Int)) : Prop where
  storage : Storage client after
  matching : QueueMatches client after
  settled : after.heap.read client.settled = before.heap.read client.settled
  range : ∀ vertex, 0 ≤ after.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size
  scan : RelaxScan (fun vertex => before.heap.read client.settled vertex ≠ 0)
    selected edges (before.heap.read client.distance) (after.heap.read client.distance)
  costs : CostBounds before after 0 edges.length client.size.toNat
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : EdgeScanSummary client before.heap after.heap selected head


def EdgeStepSummary (client : Client) (before after : Heap) (selected : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge) : Prop :=
  ∀ finalHeap result,
    (∀ state, AtEdges state after client.graph client.distance client.settled client.queue selected next →
      dijkstra.CallFrom state finalHeap result) →
    ∀ state, AtEdges state before client.graph client.distance client.settled client.queue selected (some edge) →
      dijkstra.CallFrom state finalHeap result

structure EdgeAdvanced (client : Client) (before after : QueueState)
    (selected target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge) : Prop where
  storage : Storage client after
  matching : QueueMatches client after
  settled : after.heap.read client.settled = before.heap.read client.settled
  range : ∀ vertex, 0 ≤ after.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size
  scan : RelaxScan (fun vertex => before.heap.read client.settled vertex ≠ 0)
    selected [(target,weight)] (before.heap.read client.distance) (after.heap.read client.distance)
  costs : CostBounds before after 0 1 client.size.toNat
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : EdgeStepSummary client before.heap after.heap selected edge next

/-- One edge branch uses the update contract only when its candidate improves. -/
theorem advance_edge_of_queue_contracts (contracts : QueueContracts)
    (client : Client) (state : QueueState) (selected target weight : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge)
    (storage : Storage client state) (matching : QueueMatches client state)
    (range : ∀ vertex, 0 ≤ state.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size)
    (selectedFinite : 0 ≤ state.heap.read client.distance selected)
    (validEdge : is_Edge state.heap edge)
    (readTarget : field_Edge_target state.heap edge = some target)
    (readWeight : field_Edge_weight state.heap edge = some weight)
    (readNext : field_Edge_next state.heap edge = some next)
    (targetLower : 0 ≤ target) (targetUpper : target < client.size) (weightLower : 0 ≤ weight) :
    ∃ after, EdgeAdvanced client state after selected target weight edge next := by
  by_cases unsettled : state.heap.read client.settled target = 0
  · by_cases better : state.heap.read client.distance target < 0 ∨
        state.heap.read client.distance selected + weight < state.heap.read client.distance target
    · let candidate := state.heap.read client.distance selected + weight
      have candidateNonnegative : 0 ≤ candidate := by dsimp [candidate]; omega
      let prepared := (state.tick "edges").write client.distance target candidate
      have preparedStorage : Storage client prepared :=
        (storage.tick "edges").write _ target candidate storage.distanceSeparate
      obtain ⟨after, updated⟩ := contracts.update client prepared target candidate preparedStorage targetLower (by
        intro old member
        have key := (matching target old).mp member
        dsimp [candidate]
        omega)
      have distanceFinal : (after.tick "improvements").heap.read client.distance =
          updateDistance (state.heap.read client.distance) target candidate := by
        rw [show (after.tick "improvements").heap.read client.distance = after.heap.read client.distance from rfl,
          updated.distance]
        funext vertex
        simp [prepared, QueueState.tick, QueueState.write, Heap.read, Heap.write, updateDistance]
      have settledFinal : (after.tick "improvements").heap.read client.settled =
          state.heap.read client.settled := by
        rw [show (after.tick "improvements").heap.read client.settled = after.heap.read client.settled from rfl,
          updated.settled]
        funext vertex
        simp [prepared, QueueState.tick, QueueState.write, Heap.read, Heap.write, Ne.symm storage.separate]
      have frame : GraphFrame state.heap (after.tick "improvements").heap client.graph client.heads :=
        ((GraphAnalysis.graph_frame_tick _ _ _ "edges" 1).trans
          (GraphAnalysis.graph_frame_write _ _ _ client.distance target candidate)).trans
          (updated.frame.trans (GraphAnalysis.graph_frame_tick _ _ _ "improvements" 1))
      refine ⟨after.tick "improvements", updated.storage.tick "improvements", ?_, settledFinal, ?_, ?_,
        updated_edge_cost updated, frame, ?_⟩
      · intro vertex key
        change (vertex,key) ∈ after.forest.entries ↔ _
        rw [updated.contents, distanceFinal, settledFinal]
        change (vertex = target ∧ key = candidate) ∨ (vertex ≠ target ∧ (vertex,key) ∈ state.forest.entries) ↔ _
        rw [matching]
        by_cases same : vertex = target <;>
          simp [updateDistance, same, unsettled, candidateNonnegative]
      · intro vertex finite
        rw [distanceFinal] at finite
        by_cases same : vertex = target
        · simpa [same] using And.intro targetLower targetUpper
        · apply range vertex
          simpa [updateDistance, same] using finite
      · rw [distanceFinal, ← relax_distance_improves _ target candidate better]
        exact .relax (by simpa using unsettled) (.empty _)
      · intro finalHeap result continuation current located
        apply improve_edge_continue current state.heap after.heap finalHeap
          client.graph client.distance client.settled result client.queue selected target weight edge next
          located storage.distanceAllocated storage.settledAllocated readTarget readWeight unsettled better
          updated.execution
        · exact ((frame.edges edge validEdge).2.2.2).trans readNext
        · exact continuation
    · have finite : 0 ≤ state.heap.read client.distance target := by omega
      have noBetter : state.heap.read client.distance target ≤ state.heap.read client.distance selected + weight := by omega
      refine ⟨state.tick "edges", storage.tick "edges", matching, rfl, range, ?_,
        skip_edge_cost state _, GraphAnalysis.graph_frame_tick _ _ _ "edges" 1, ?_⟩
      · apply RelaxScan.relax (by simpa using unsettled)
        rw [relax_distance_unchanged _ target _ finite noBetter]
        exact .empty _
      · intro finalHeap result continuation current located
        exact unimproved_edge_continue current state.heap finalHeap client.graph client.distance client.settled
          result client.queue selected target weight edge next located storage.distanceAllocated storage.settledAllocated
          readTarget readWeight unsettled finite noBetter readNext continuation
  · refine ⟨state.tick "edges", storage.tick "edges", matching, rfl, range,
      RelaxScan.skip unsettled (.empty _), skip_edge_cost state _,
      GraphAnalysis.graph_frame_tick _ _ _ "edges" 1, ?_⟩
    intro finalHeap result continuation current located
    exact settled_edge_continue current state.heap finalHeap client.graph client.distance client.settled
      result client.queue selected target edge next located storage.settledAllocated readTarget unsettled readNext continuation

/-- Finite adjacency traversal shares the same pure RelaxScan relation as the
    binary implementation; only the local update contract depends on the heap. -/
theorem scan_adjacency_of_queue_contracts (contracts : QueueContracts)
    (client : Client) (state : QueueState) (selected : Int)
    (head : Option Ref_Edge) (edges : List (Int × Int))
    (storage : Storage client state) (matching : QueueMatches client state)
    (range : ∀ vertex, 0 ≤ state.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size)
    (selectedSettled : state.heap.read client.settled selected ≠ 0)
    (selectedFinite : 0 ≤ state.heap.read client.distance selected)
    (chain : AdjacencyChain state.heap client.size head edges) :
    ∃ after, AdjacencyScanned client state after selected head edges := by
  induction edges generalizing state head with
  | nil =>
    have empty := chain.empty_iff.mpr rfl
    subst head
    refine ⟨state, storage, matching, rfl, range, RelaxScan.empty _,
      CostBounds.refl state _, GraphAnalysis.GraphFrame.refl _ _ _, ?_⟩
    intro finalHeap result continuation current located
    exact empty_edges_continue current state.heap finalHeap client.graph client.distance client.settled
      result client.queue selected located continuation
  | cons pair rest ih =>
    cases chain with
    | cons edge target weight next tail valid readTarget readWeight readNext lower upper nonnegative remaining =>
      obtain ⟨middle, advanced⟩ := advance_edge_of_queue_contracts contracts client state
        selected target weight edge next storage matching range selectedFinite
        valid readTarget readWeight readNext lower upper nonnegative
      have selectedSame := RelaxScan.selected_unchanged _ selected [(target,weight)]
        (state.heap.read client.distance) (middle.heap.read client.distance) selectedSettled advanced.scan
      obtain ⟨after, scanned⟩ := ih middle next advanced.storage advanced.matching advanced.range
        (by rw [advanced.settled]; exact selectedSettled)
        (by rw [selectedSame]; exact selectedFinite) (remaining.preserved advanced.frame.edges)
      refine ⟨after, scanned.storage, scanned.matching, scanned.settled.trans advanced.settled,
        scanned.range, ?_, ?_, advanced.frame.trans scanned.frame, ?_⟩
      · have tailScan := scanned.scan
        rw [advanced.settled] at tailScan
        exact advanced.scan.append tailScan
      · simpa [Nat.add_comm] using advanced.costs.trans scanned.costs
      · intro finalHeap result continuation current located
        apply advanced.execution finalHeap result _ current located
        intro nextState nextLocated
        exact scanned.execution finalHeap result continuation nextState nextLocated

/-- The generic finite driver is instantiated with the actual compiled caller,
    graph representation, queue contents, and telescoping amortized accounting. -/
def executionInterface (client : Client) : Algo2Lean.Dijkstra.Execution.Interface QueueState := {
  distance := fun state => state.heap.read client.distance
  settled := fun state vertex => state.heap.read client.settled vertex ≠ 0
  invariant := LoopInvariant client
  completion := fun before after => ∀ current,
    AtExtraction current before.heap client.graph client.distance client.settled client.queue →
    dijkstra.CallFrom current after.heap client.distance
  accounting := fun before after vertices edges => CostBounds before after vertices edges client.size.toNat
  zero := fun state => CostBounds.refl state _
  compose := fun first second => first.trans second
  weaken := fun costs vertices edges => costs.weaken vertices edges }

theorem extraction_progress_of_queue_contracts (contracts : QueueContracts)
    (client : Client) (state : QueueState) (remaining : List Int)
    (invariant : LoopInvariant client state remaining) :
    Algo2Lean.Dijkstra.Execution.Progress (executionInterface client)
      (representedEdges client.size client.adjacency) client.adjacency state remaining := by
  by_cases empty : state.forest = []
  · apply Algo2Lean.Dijkstra.Execution.Progress.done
    · intro vertex unsettled
      have absent := invariant.matching vertex (state.heap.read client.distance vertex)
      simp only [empty, Algo2Lean.Fibonacci.Forest.entries, List.flatMap_nil, List.not_mem_nil,
        false_iff, and_true] at absent
      have zero : state.heap.read client.settled vertex = 0 := by simpa [executionInterface] using unsettled
      change state.heap.read client.distance vertex < 0
      omega
    · intro current located
      apply extraction_done current state.heap client.graph client.distance client.settled client.queue located
      · have size := invariant.storage.queue.represented.size
        have read := invariant.storage.queue.layoutValid.readSize
        have zero : state.layout.size = 0 := by
          simpa [FibonacciHeapAnalysis.snapshot, empty, Algo2Lean.Fibonacci.Forest.entries] using size
        simpa only [zero] using read
      · exact invariant.storage.distanceAllocated
  · have inRange (vertex key) (member : (vertex,key) ∈ state.forest.entries) :
        0 ≤ vertex ∧ vertex < client.size :=
      invariant.finiteInRange vertex ((invariant.matching vertex key).mp member).2.1
    obtain ⟨popped, vertex, key, extracted⟩ := contracts.extract client state invariant.storage empty inRange
    have selected := (invariant.matching vertex key).mp extracted.selected
    obtain ⟨lower, upper⟩ := invariant.finiteInRange vertex selected.2.1
    have member : vertex ∈ remaining := (invariant.members vertex).mpr ⟨lower,upper,selected.1⟩
    let settled := (popped.write client.settled vertex 1).tick "settlements"
    have stored : Storage client settled :=
      (extracted.storage.write _ vertex 1 extracted.storage.settledSeparate).tick "settlements"
    have distanceSame : settled.heap.read client.distance = state.heap.read client.distance := by
      change (popped.heap.write client.settled vertex 1).read client.distance = _
      rw [show (popped.heap.write client.settled vertex 1).read client.distance =
          popped.heap.read client.distance by
        funext v
        exact Heap.read_write_other_ref _ _ _ _ _ _ invariant.storage.separate]
      exact extracted.distance
    have settledValues (v : Int) : settled.heap.read client.settled v =
        if v = vertex then 1 else state.heap.read client.settled v := by
      change (popped.heap.write client.settled vertex 1).read client.settled v = _
      simpa [Heap.read, Heap.write] using
        congrArg (fun value => if v = vertex then 1 else value) (congrFun extracted.settled v)
    have matching : QueueMatches client settled := by
      intro v k
      change (v,k) ∈ popped.forest.entries ↔ _
      rw [extracted.contents, invariant.matching, distanceSame, settledValues]
      by_cases same : v = vertex <;> simp [same]
    have settledPredicate : (fun v => settled.heap.read client.settled v ≠ 0) =
        settleVertex (fun v => state.heap.read client.settled v ≠ 0) vertex := by
      funext v
      rw [settledValues]
      apply propext
      by_cases same : v = vertex <;> simp [settleVertex,same]
    have finiteInRange : ∀ v, 0 ≤ settled.heap.read client.distance v →
        0 ≤ v ∧ v < client.size := by rw [distanceSame]; exact invariant.finiteInRange
    obtain ⟨head, readHead, chain⟩ := stored.graph.chains vertex lower upper
    obtain ⟨after, scanned⟩ := scan_adjacency_of_queue_contracts contracts client settled vertex
      head (client.adjacency vertex) stored matching finiteInRange
      (by rw [settledValues]; simp) (by rw [distanceSame]; exact selected.2.1) chain
    have next : LoopInvariant client after (remaining.erase vertex) := by
      refine ⟨scanned.storage, scanned.matching, scanned.range, invariant.unique.erase vertex, ?_⟩
      intro v
      rw [invariant.unique.mem_erase_iff, invariant.members, scanned.settled, settledValues]
      by_cases same : v = vertex <;> simp [same]
    have sizePositive : 0 < state.layout.size := by
      have size := invariant.storage.queue.represented.size
      have nonzero : state.forest.entries.length ≠ 0 := by
        intro zero
        have nil := List.length_eq_zero_iff.mp zero
        have contradiction := extracted.selected
        rw [nil] at contradiction
        contradiction
      change state.layout.size = (state.forest.entries.length : Int) at size
      omega
    apply Algo2Lean.Dijkstra.Execution.Progress.next (after := after) (selected := vertex)
    refine ⟨member, next, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, selected.2.1, ?_⟩
      · change ¬state.heap.read client.settled vertex ≠ 0
        simp [selected.1]
      · intro v unsettled finite
        have entry := (invariant.matching v (state.heap.read client.distance v)).mpr
          ⟨by simpa [executionInterface] using unsettled,finite,rfl⟩
        have least := extracted.least v _ entry
        simpa [selected.2.2] using least
    · intro target weight
      simp [representedEdges,lower,upper]
    · have run := scanned.scan
      rw [distanceSame,settledPredicate] at run
      exact run
    · change (fun v => after.heap.read client.settled v ≠ 0) = _
      rw [scanned.settled,settledPredicate]
      rfl
    · intro final continuation current located
      apply extraction_to_edges current state.heap popped.heap final.heap client.graph
        client.distance client.settled client.distance client.queue vertex state.layout.size client.heads head
        located invariant.storage.queue.layoutValid.readSize sizePositive extracted.execution
        extracted.storage.settledAllocated stored.graph.readHeads readHead
      intro edgeState edgeLocated
      exact scanned.execution final.heap client.distance continuation edgeState edgeLocated
    · simpa using (extracted_settled_cost extracted).trans scanned.costs

/-- Conditional termination, logical search trace, and measured amortized cost
    of the entire extraction loop. Queue correctness is confined to local calls. -/
theorem extraction_loop_of_queue_contracts (contracts : QueueContracts)
    (client : Client) (state : QueueState) (remaining : List Int)
    (invariant : LoopInvariant client state remaining) :
    ∃ after, Algo2Lean.Dijkstra.Execution.Completed (executionInterface client)
      (representedEdges client.size client.adjacency) client.adjacency state after remaining :=
  Algo2Lean.Dijkstra.Execution.run (executionInterface client)
    (representedEdges client.size client.adjacency) client.adjacency
    (extraction_progress_of_queue_contracts contracts client) state remaining invariant

/-- Runtime combines every source tick once: the three Dijkstra clocks and
    the seven primitive Fibonacci heap clocks. -/
def runtimeWork (before after : Heap) : Nat :=
  FibonacciHeapAnalysis.heapEventWork before after + Heap.cost before after "edges" +
    Heap.cost before after "improvements" + Heap.cost before after "settlements"

theorem CostBounds.runtime {before after : QueueState} {vertices edges size : Nat}
    (bound : CostBounds before after vertices edges size) :
    runtimeWork before.heap after.heap ≤ before.potential +
      22 * edges + (12 * (2 * size.log2 + 2) + 1) * vertices := by
  have work := bound.amortized
  have visits := bound.visits
  have improvements := bound.improvements
  have settlements := bound.settlements
  unfold runtimeWork
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Full compiled execution and shortest distances, conditional only on the
    three public queue-method contracts. The cost charges actual clock deltas
    and is O(E + V log V); the final forest potential can only strengthen it. -/
theorem dijkstra_correct_of_queue_contracts (contracts : QueueContracts)
    (heap : Heap) (graph : Ref_Graph) (size source : Int) (heads : CollectionRef)
    (adjacency : Adjacency) (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) :
    ∃ after,
      dijkstra.Call heap (graph,source) after heap.nextRef ∧
      GraphRep after graph size heads adjacency ∧
      ShortestDistances (representedEdges size adjacency) source (after.read heap.nextRef) ∧
      runtimeWork heap after ≤ 22 * (edgeBudget adjacency (vertexRange size) + 1) +
        (popBudget size + 1) * size.toNat := by
  let allocated := (heap.allocate (fun _ => -1)).allocate (fun _ => 0)
  have allocatedGraph : GraphRep allocated graph size heads adjacency :=
    representation.preserved ((GraphAnalysis.graph_frame_allocate heap graph heads (fun _ => -1)).trans
      (GraphAnalysis.graph_frame_allocate _ graph heads (fun _ => 0)))
  obtain ⟨queueHeap, layout, constructor, storage, distances, flags, clocks⟩ := contracts.constructor
    allocated graph size heads adjacency heap.nextRef (heap.nextRef + 1) allocatedGraph
    (show heap.nextRef < heap.nextRef + 1 + 1 from Nat.lt_succ_of_le (Nat.le_succ _))
    (by simp [allocated, Heap.allocate])
    (Nat.ne_of_lt (Nat.lt_succ_self _))
  let client : Client := ⟨graph,size,heads,adjacency,heap.nextRef,heap.nextRef+1,heap.nextObject⟩
  let empty : QueueState := ⟨queueHeap,layout,[]⟩
  have stored : Storage client empty := storage
  have originalDistances : queueHeap.read heap.nextRef = fun _ => -1 := by
    rw [distances]
    funext vertex
    simp [allocated, Heap.read, Heap.allocate]
  have originalFlags : queueHeap.read (heap.nextRef+1) = fun _ => 0 := by
    rw [flags]
    funext vertex
    simp [allocated, Heap.read, Heap.allocate]
  let prepared := empty.write client.distance source 0
  have preparedStorage : Storage client prepared :=
    stored.write _ source 0 stored.distanceSeparate
  obtain ⟨initial, inserted⟩ := contracts.update client prepared source 0 preparedStorage sourceLower (by
    intro key member
    simp [prepared,empty,QueueState.write,Algo2Lean.Fibonacci.Forest.entries] at member)
  have initialDistances : initial.heap.read client.distance = Algo2Lean.Dijkstra.initialDistances source := by
    rw [inserted.distance]
    funext vertex
    change (queueHeap.write heap.nextRef source 0).read heap.nextRef vertex = _
    simpa [Heap.read,Heap.write,Algo2Lean.Dijkstra.initialDistances] using
      congrArg (fun value => if vertex = source then 0 else value) (congrFun originalDistances vertex)
  have initialFlags : initial.heap.read client.settled = fun _ => 0 := by
    rw [inserted.settled]
    funext vertex
    change (queueHeap.write heap.nextRef source 0).read (heap.nextRef+1) vertex = _
    rw [Heap.read_write_other_ref queueHeap (heap.nextRef+1) heap.nextRef vertex source 0 (Nat.succ_ne_self _)]
    exact congrFun originalFlags vertex
  have invariant : LoopInvariant client initial (vertexRange size) := by
    refine ⟨inserted.storage, ?_, ?_, vertexRange_nodup size, ?_⟩
    · intro vertex key
      rw [inserted.contents,initialDistances,initialFlags]
      change (vertex = source ∧ key = 0) ∨ (vertex ≠ source ∧ (vertex,key) ∈ Algo2Lean.Fibonacci.Forest.entries []) ↔ _
      by_cases same : vertex = source <;>
        simp [Algo2Lean.Fibonacci.Forest.entries,Algo2Lean.Dijkstra.initialDistances,same]
    · intro vertex finite
      rw [initialDistances] at finite
      by_cases same : vertex = source
      · subst vertex
        exact ⟨sourceLower,sourceUpper⟩
      · simp [Algo2Lean.Dijkstra.initialDistances,same] at finite
    · intro vertex
      rw [initialFlags]
      simp [client]
  obtain ⟨after, completed⟩ := extraction_loop_of_queue_contracts contracts client initial (vertexRange size) invariant
  obtain ⟨pending, finalInvariant⟩ := completed.invariant
  change LoopInvariant client after pending at finalInvariant
  obtain ⟨vertices, search, contained⟩ := completed.search
  change SearchRun (representedEdges size adjacency) adjacency
    (initial.heap.read client.distance) (fun vertex => initial.heap.read client.settled vertex ≠ 0)
    (after.heap.read client.distance) vertices at search
  rw [initialDistances,initialFlags] at search
  simp only [ne_self_iff_false] at search
  have correct := search.initial_correct representation.nonnegative_edges
  have initialCost : CostBounds ⟨heap,layout,[]⟩ initial 0 1 size.toNat := by
    have settlements := inserted.bookkeeping "settlements" (by simp)
    have visits := inserted.bookkeeping "edges" (by simp)
    have improvements := inserted.bookkeeping "improvements" (by simp)
    have work := inserted.amortized
    have same : prepared.heap.clocks = heap.clocks := by
      change queueHeap.clocks = heap.clocks
      simpa [allocated,Heap.allocate] using clocks
    have queueClocks : queueHeap.clocks = heap.clocks := same
    constructor
    · simp only [Heap.cost,settlements,same,Nat.sub_self,Nat.le_refl]
    · simp only [Heap.cost,visits,same,Nat.sub_self,Nat.zero_le]
    · simp only [Heap.cost,improvements,same,Nat.sub_self,Nat.zero_le]
    · simpa [FibonacciHeapAnalysis.heapEventWork,Heap.cost,same,queueClocks,QueueState.potential,
        prepared,empty,QueueState.write,Algo2Lean.Fibonacci.Forest.counts,
        Algo2Lean.Fibonacci.scaledPotential,Algo2Lean.Fibonacci.potential,
        Algo2Lean.Fibonacci.Forest.marks] using work
  refine ⟨after.heap, ?_, finalInvariant.storage.graph, correct, ?_⟩
  · apply initialize_summary heap queueHeap initial.heap after.heap graph heap.nextObject source size heap.nextRef
      representation.valid representation.readSize sourceLower sourceUpper constructor
      stored.distanceAllocated inserted.execution
    exact completed.execution
  · have cost := (initialCost.trans completed.cost).runtime
    simpa [QueueState.potential,Algo2Lean.Fibonacci.Forest.counts,
      Algo2Lean.Fibonacci.scaledPotential,Algo2Lean.Fibonacci.potential,Algo2Lean.Fibonacci.Forest.marks,
      vertexRange, popBudget, Nat.add_comm] using cost

/-- The explicit clocks are added with unit weight. This is the cost model
    implemented by the source's tick statements, not wall-clock time. -/
def clockWork (costs : Clocks) : Nat :=
  costs "heap_operations" + costs "heap_comparisons" + costs "heap_links" +
    costs "heap_cuts" + costs "heap_root_scans" + costs "heap_degree_scans" +
    costs "heap_promotions" + costs "edges" + costs "improvements" + costs "settlements"

/-- Ordinary outputs and runtime need no queue layout, forest, heap-result
    reference, transition, or transcript in their specification. This theorem
    assumes local queue contracts, supplied by `verifiedQueueContracts` for this heap. -/
theorem dijkstra_output_exists_of_queue_contracts (contracts : QueueContracts)
    (heap : Heap) (graph : Ref_Graph) (size source : Int) (heads : CollectionRef)
    (adjacency : Adjacency) (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) :
    ∃ output costs,
      dijkstra.ReturnsWithCost (heap,graph,source) output costs ∧
      ShortestDistances (representedEdges size adjacency) source output ∧
      clockWork costs ≤ 22 * (edgeBudget adjacency (vertexRange size) + 1) +
        (popBudget size + 1) * size.toNat := by
  obtain ⟨after, summary, _, correct, runtime⟩ := dijkstra_correct_of_queue_contracts
    contracts heap graph size source heads adjacency representation sourceLower sourceUpper
  exact ⟨after.read heap.nextRef, Heap.cost heap after,
    ⟨after,heap.nextRef,⟨summary.1,summary.2.root⟩,rfl,rfl⟩,correct,runtime⟩


/-- Completed executions have a unique final heap and result reference. The
    supporting certificate is checked against every compiled transition. -/
theorem execution_unique {heap leftHeap rightHeap : Heap}
    {input : Ref_Graph × Int} {leftResult rightResult : SeqRef}
    (first : dijkstra.Run heap input leftHeap leftResult)
    (second : dijkstra.Run heap input rightHeap rightResult) :
    leftHeap = rightHeap ∧ leftResult = rightResult := by
  have same := Reaches.eq_of_terminal (step := Step)
    DijkstraFibonacciDeterminism.step_deterministic first.2 second.2
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl,rfl⟩

theorem output_with_cost_unique {input : Heap × (Ref_Graph × Int)}
    {firstOutput secondOutput : Seq} {firstCosts secondCosts : Clocks}
    (first : dijkstra.ReturnsWithCost input firstOutput firstCosts)
    (second : dijkstra.ReturnsWithCost input secondOutput secondCosts) :
    firstOutput = secondOutput ∧ firstCosts = secondCosts := by
  obtain ⟨firstHeap,firstResult,firstRun,firstValue,firstCost⟩ := first
  obtain ⟨secondHeap,secondResult,secondRun,secondValue,secondCost⟩ := second
  obtain ⟨rfl,rfl⟩ := execution_unique firstRun secondRun
  exact ⟨firstValue.symm.trans secondValue,firstCost.symm.trans secondCost⟩

/-- Every compiled output satisfies shortest-path correctness and the combined
    actual-clock bound, assuming only the explicit local heap method contracts. -/
theorem dijkstra_output_correct_of_queue_contracts (contracts : QueueContracts)
    (heap : Heap) (graph : Ref_Graph) (size source : Int) (heads : CollectionRef)
    (adjacency : Adjacency) (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (output : Seq) (costs : Clocks)
    (run : dijkstra.ReturnsWithCost (heap,graph,source) output costs) :
    ShortestDistances (representedEdges size adjacency) source output ∧
      clockWork costs ≤ 22 * (edgeBudget adjacency (vertexRange size) + 1) +
        (popBudget size + 1) * size.toNat := by
  obtain ⟨verifiedOutput,verifiedCosts,verifiedRun,correct,bound⟩ :=
    dijkstra_output_exists_of_queue_contracts contracts heap graph size source heads adjacency
      representation sourceLower sourceUpper
  obtain ⟨rfl,rfl⟩ := output_with_cost_unique run verifiedRun
  exact ⟨correct,bound⟩

/-- A queue footprint cannot alias a Graph or Edge object because class tags
    are preserved and the queue's class is distinct. -/
theorem graph_frame_of_modifies {before after : Heap} (graph : Ref_Graph) (heads : CollectionRef)
    (queue : Ref_FibonacciHeap) (refs : List SeqRef) (validQueue : is_FibonacciHeap before queue)
    (frame : before.Modifies after refs [queue]) : GraphFrame before after graph heads := by
  have sameGraph : is_Graph after graph ↔ is_Graph before graph := by
    simp only [is_Graph,frame.nextObject,frame.classes]
  have differentGraph (valid : is_Graph before graph) : graph ≠ queue := by
    intro same
    have first := valid.2
    rw [same,validQueue.2] at first
    contradiction
  refine ⟨sameGraph.mpr,?_,?_,?_,?_,?_⟩
  · change field_Graph_size after graph = field_Graph_size before graph
    simp only [field_Graph_size,sameGraph]
    by_cases valid : is_Graph before graph
    · simp [valid,frame.readField graph (by simpa using differentGraph valid)]
    · simp [valid]
  · change field_Graph_heads after graph = field_Graph_heads before graph
    simp only [field_Graph_heads,sameGraph]
    by_cases valid : is_Graph before graph
    · simp [valid,frame.readField graph (by simpa using differentGraph valid)]
    · simp [valid]
  · change seq_Edge_optional.valid before heads → seq_Edge_optional.valid after heads
    simp [SequenceType.valid,Heap.validSequence,Heap.sequenceType,frame.nextCollection,frame.collections]
  · intro vertex
    change seq_Edge_optional.get after heads vertex = seq_Edge_optional.get before heads vertex
    simp [SequenceType.get,SequenceType.valid,Heap.validSequence,Heap.sequenceType,Heap.readElement,
      frame.nextCollection,frame.collections]
  · intro ref valid
    change is_Edge before ref at valid
    have different : ref ≠ queue := by
      intro same
      have first := valid.2
      rw [same,validQueue.2] at first
      contradiction
    have validAfter : is_Edge after ref := by simpa [is_Edge,frame.nextObject,frame.classes] using valid
    refine ⟨validAfter,?_,?_,?_⟩
    · change field_Edge_target after ref = field_Edge_target before ref
      simp [field_Edge_target,valid,validAfter,frame.readField ref (by simpa using different)]
    · change field_Edge_weight after ref = field_Edge_weight before ref
      simp [field_Edge_weight,valid,validAfter,frame.readField ref (by simpa using different)]
    · change field_Edge_next after ref = field_Edge_next before ref
      simp [field_Edge_next,valid,validAfter,frame.readField ref (by simpa using different)]

/-- Local queue correctness plus a small storage footprint preserves every
    client invariant; there is no need to inspect the queue's internal updates. -/
theorem Storage.of_modifies {client : Client} {before after : QueueState}
    (storage : Storage client before)
    (frame : before.heap.Modifies after.heap before.layout.refs [client.queue])
    (refs : after.layout.refs = before.layout.refs)
    (queue : FibonacciHeapAnalysis.QueueRep after.heap client.queue after.layout after.forest) :
    Storage client after := by
  refine ⟨storage.graph.preserved (graph_frame_of_modifies client.graph client.heads client.queue
    before.layout.refs storage.queue.layoutValid.object frame),queue,?_,?_,storage.separate,?_,?_⟩
  · rw [frame.nextRef]; exact storage.distanceAllocated
  · rw [frame.nextRef]; exact storage.settledAllocated
  · rw [refs]; exact storage.distanceSeparate
  · rw [refs]; exact storage.settledSeparate

theorem Storage.clients_unchanged {client : Client} {before after : QueueState}
    (storage : Storage client before)
    (frame : before.heap.Modifies after.heap before.layout.refs [client.queue]) :
    after.heap.read client.distance = before.heap.read client.distance ∧
      after.heap.read client.settled = before.heap.read client.settled :=
  ⟨frame.read client.distance storage.distanceSeparate,frame.read client.settled storage.settledSeparate⟩

/-- Construction allocates fresh storage; every pre-existing object is untouched. -/
theorem queue_constructor_old_object (heap : Heap) (ref : ObjectRef) (old : ref < heap.nextObject) :
    (FibonacciHeapAnalysis.newHeap heap).objects ref = heap.objects ref := by
  have different : ref ≠ heap.nextObject := Nat.ne_of_lt old
  simp [FibonacciHeapAnalysis.newHeap,FibonacciHeapAnalysis.initializedHeap,
    FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_keys, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_parents, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_children, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_left, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_right, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_degrees, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_marks, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_present, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_table, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_minimum, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_size,Heap.writeField,Heap.allocateObject,different]

/-- Every already allocated sequence retains all its integer-indexed values. -/
theorem queue_constructor_old_sequence (heap : Heap) (ref : SeqRef) (old : ref < heap.nextRef) :
    (FibonacciHeapAnalysis.newHeap heap).read ref = heap.read ref := by
  have different (offset : Nat) : ref ≠ heap.nextRef + offset :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _))
  have notBase : ref ≠ heap.nextRef := Nat.ne_of_lt old
  funext index
  simp [FibonacciHeapAnalysis.newHeap,FibonacciHeapAnalysis.initializedHeap,
    FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_keys, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_parents, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_children, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_left, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_right, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_degrees, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_marks, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_present, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_table, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_minimum, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_size,Heap.read,Heap.allocate,Nat.add_assoc,different,notBase]

theorem queue_constructor_next_ref (heap : Heap) :
    (FibonacciHeapAnalysis.newHeap heap).nextRef = heap.nextRef + 9 := by
  simp [FibonacciHeapAnalysis.newHeap,FibonacciHeapAnalysis.initializedHeap,
    FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_keys, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_parents, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_children, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_left, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_right, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_degrees, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_marks, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_present, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_table, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_minimum, FibonacciHeapLibrary.Algo2LeanGenerated.set_FibonacciHeap_size,Nat.add_assoc]

/-- The new object's fresh class and the untouched old stores preserve the
    graph representation, including all shared adjacency-list tails. -/
theorem queue_constructor_graph_frame (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (valid : is_Graph heap graph) :
    GraphFrame heap (FibonacciHeapAnalysis.newHeap heap) graph heads := by
  have objects := queue_constructor_old_object heap graph valid.1
  have validAfter : is_Graph (FibonacciHeapAnalysis.newHeap heap) graph := by
    constructor
    · change graph < heap.nextObject + 1
      exact Nat.lt_succ_of_lt valid.1
    · simpa only [Heap.objectClass,objects] using valid.2
  refine ⟨fun _ => validAfter,?_,?_,id,fun _ => rfl,?_⟩
  · change field_Graph_size (FibonacciHeapAnalysis.newHeap heap) graph = field_Graph_size heap graph
    simp [field_Graph_size,validAfter,valid,Heap.readField,objects]
  · change field_Graph_heads (FibonacciHeapAnalysis.newHeap heap) graph = field_Graph_heads heap graph
    simp [field_Graph_heads,validAfter,valid,Heap.readField,objects]
  · intro ref validEdge
    change is_Edge heap ref at validEdge
    have oldObjects := queue_constructor_old_object heap ref validEdge.1
    have edgeAfter : is_Edge (FibonacciHeapAnalysis.newHeap heap) ref := by
      constructor
      · change ref < heap.nextObject + 1
        exact Nat.lt_succ_of_lt validEdge.1
      · simpa only [Heap.objectClass,oldObjects] using validEdge.2
    refine ⟨edgeAfter,?_,?_,?_⟩
    · change field_Edge_target (FibonacciHeapAnalysis.newHeap heap) ref = field_Edge_target heap ref
      simp [field_Edge_target,edgeAfter,validEdge,Heap.readField,oldObjects]
    · change field_Edge_weight (FibonacciHeapAnalysis.newHeap heap) ref = field_Edge_weight heap ref
      simp [field_Edge_weight,edgeAfter,validEdge,Heap.readField,oldObjects]
    · change field_Edge_next (FibonacciHeapAnalysis.newHeap heap) ref = field_Edge_next heap ref
      simp [field_Edge_next,edgeAfter,validEdge,Heap.readField,oldObjects]

/-- This discharges the constructor field of QueueContracts unconditionally. -/
theorem queue_constructor_verified (heap : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (graphRep : GraphRep heap graph size heads adjacency)
    (distanceAllocated : distance < heap.nextRef) (settledAllocated : settled < heap.nextRef)
    (separate : distance ≠ settled) :
    ∃ after layout,
      FibonacciHeap.Call heap () after heap.nextObject ∧
      Storage ⟨graph,size,heads,adjacency,distance,settled,heap.nextObject⟩ ⟨after,layout,[]⟩ ∧
      after.read distance = heap.read distance ∧ after.read settled = heap.read settled ∧
      after.clocks = heap.clocks := by
  refine ⟨FibonacciHeapAnalysis.newHeap heap,FibonacciHeapAnalysis.emptyLayout heap,
    Queue.constructor_summary heap,?_,queue_constructor_old_sequence heap distance distanceAllocated,
    queue_constructor_old_sequence heap settled settledAllocated,rfl⟩
  refine ⟨graphRep.preserved (queue_constructor_graph_frame heap graph heads graphRep.valid),
    FibonacciHeapAnalysis.new_heap_representation heap,?_,?_,separate,?_,?_⟩
  · change distance < (FibonacciHeapAnalysis.newHeap heap).nextRef
    rw [queue_constructor_next_ref]
    exact Nat.lt_of_lt_of_le distanceAllocated (Nat.le_add_right _ _)
  · change settled < (FibonacciHeapAnalysis.newHeap heap).nextRef
    rw [queue_constructor_next_ref]
    exact Nat.lt_of_lt_of_le settledAllocated (Nat.le_add_right _ _)
  · have different (offset : Nat) : distance ≠ heap.nextRef + offset :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le distanceAllocated (Nat.le_add_right _ _))
    simp [FibonacciHeapAnalysis.emptyLayout,FibonacciHeapAnalysis.Layout.refs,different,
      Nat.ne_of_lt distanceAllocated]
  · have different (offset : Nat) : settled ≠ heap.nextRef + offset :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le settledAllocated (Nat.le_add_right _ _))
    simp [FibonacciHeapAnalysis.emptyLayout,FibonacciHeapAnalysis.Layout.refs,different,
      Nat.ne_of_lt settledAllocated]
/-- Unique active handles within the graph range bound the queue's cardinality,
    independently of the internal tree or ring shape. -/
theorem queue_cardinality_bound {client : Client} {state : QueueState}
    (storage : Storage client state)
    (range : ∀ vertex key, (vertex,key) ∈ state.forest.entries →
      0 ≤ vertex ∧ vertex < client.size) : state.forest.entries.length ≤ client.size.toNat := by
  have bound := nodup_subset_length (state.forest.entries.map Prod.fst) (vertexRange client.size)
    storage.queue.represented.valid.1 (by
      intro vertex member
      obtain ⟨⟨v,k⟩,entry,same⟩ := List.mem_map.mp member
      obtain ⟨nonnegative,upper⟩ := range v k entry
      rw [←same]
      simp [vertexRange_member,nonnegative,upper])
  simpa only [List.length_map,vertexRange,List.length_map,List.length_range] using bound

/-- The entry permutation returned by delete-min is the exact membership
    deletion needed by the client invariant. Uniqueness prevents duplicates. -/
theorem removed_entries_iff {before after : Algo2Lean.Fibonacci.Forest} {vertex key : Int}
    (unique : before.Unique)
    (contents : ((vertex,key) :: after.entries).Perm before.entries) (v k : Int) :
    (v,k) ∈ after.entries ↔ v ≠ vertex ∧ (v,k) ∈ before.entries := by
  have distinct := (contents.map Prod.fst).nodup_iff.mpr unique
  have absent := (List.nodup_cons.mp distinct).1
  constructor
  · intro entry
    refine ⟨?_,contents.mem_iff.mp (List.mem_cons_of_mem _ entry)⟩
    intro same
    apply absent
    exact List.mem_map.mpr ⟨(v,k),entry,same⟩
  · rintro ⟨different,entry⟩
    have inside := contents.mem_iff.mpr entry
    rcases List.mem_cons.mp inside with same | member
    · exact False.elim (different (congrArg Prod.fst same))
    · exact member

/-- Adapt the standalone extraction theorem using only its public summary,
    logical contents, storage footprint, and amortized measured cost. -/
theorem queue_extract_of_heap_contract {client : Client} {before after : QueueState}
    (storage : Storage client before) (nonempty : before.forest ≠ [])
    (range : ∀ vertex key, (vertex,key) ∈ before.forest.entries → 0 ≤ vertex ∧ vertex < client.size)
    (summary : FibonacciHeapLibrary.FibonacciHeap.pop_min.Call before.heap client.queue
      after.heap before.layout.minimum)
    (represented : FibonacciHeapAnalysis.QueueRep after.heap client.queue after.layout after.forest)
    (contents : ((before.layout.minimum,before.heap.read before.layout.keys before.layout.minimum) ::
      after.forest.entries).Perm before.forest.entries)
    (frame : before.heap.Modifies after.heap before.layout.refs [client.queue])
    (refs : after.layout.refs = before.layout.refs)
    (bookkeeping : ∀ name, name = "edges" ∨ name = "improvements" ∨ name = "settlements" →
      after.heap.clocks name = before.heap.clocks name)
    (amortized : FibonacciHeapAnalysis.heapEventWork before.heap after.heap + after.potential ≤
      before.potential + 12 * (2 * before.forest.entries.length.log2 + 2)) :
    QueueExtracted client before after before.layout.minimum
      (before.heap.read before.layout.keys before.layout.minimum) := by
  have preserved := storage.clients_unchanged frame
  refine ⟨FibonacciQueueEmbedding.summary_FibonacciHeap_pop_min summary,
    storage.of_modifies frame refs represented,contents.mem_iff.mp (by simp),?_,
    removed_entries_iff storage.queue.represented.valid.1 contents,preserved.1,preserved.2,
    graph_frame_of_modifies client.graph client.heads client.queue before.layout.refs
      storage.queue.layoutValid.object frame,bookkeeping,?_⟩
  · intro vertex key member
    have entry := storage.queue.represented.entry member
    have present : before.heap.read before.layout.present vertex = 1 := entry.2
    have least := (storage.queue.minimum nonempty).2.2 vertex (by rw [present]; decide)
    have value : before.heap.read before.layout.keys vertex = key := entry.1
    simpa only [value] using least
  · have logBound := Algo2Lean.Fibonacci.log2_mono (queue_cardinality_bound storage range)
    unfold popBudget
    omega

/-- Heap methods preserve the three clocks owned by their Dijkstra caller. -/
theorem bookkeeping_of_preserves_other_clocks {before after : Heap}
    (preserved : FibonacciHeapAnalysis.PreservesOtherClocks before after) :
    ∀ name, name = "edges" ∨ name = "improvements" ∨ name = "settlements" →
      after.clocks name = before.clocks name := by
  intro name named
  rcases named with rfl | rfl | rfl <;>
    apply preserved <;> simp [FibonacciHeapAnalysis.heapClocks]

/-- Reuse the standalone heap update proof through its checked compilation-unit
    embedding. The client reasons only about entries, storage, and measured work. -/
theorem queue_update_verified (client : Client) (before : QueueState) (vertex key : Int)
    (storage : Storage client before) (nonnegative : 0 ≤ vertex)
    (improvement : ∀ old, (vertex,old) ∈ before.forest.entries → key < old) :
    ∃ after, QueueUpdated client before after vertex key := by
  obtain ⟨heap,layout,forest,summary,represented,contents,frame,refs,clocks,amortized⟩ :=
    storage.queue.update vertex key nonnegative improvement
  let after : QueueState := ⟨heap,layout,forest⟩
  have preserved := storage.clients_unchanged (after := after) frame
  exact ⟨after,FibonacciQueueEmbedding.summary_FibonacciHeap_push_or_decrease summary,
    storage.of_modifies frame refs represented,contents,preserved.1,preserved.2,
    graph_frame_of_modifies client.graph client.heads client.queue before.layout.refs
      storage.queue.layoutValid.object frame,
    bookkeeping_of_preserves_other_clocks clocks,amortized⟩

/-- Reuse the standalone delete-min proof, widening its cardinality bound only
    by the client's range invariant. No heap implementation is inspected here. -/
theorem queue_extract_verified (client : Client) (before : QueueState)
    (storage : Storage client before) (nonempty : before.forest ≠ [])
    (range : ∀ vertex key, (vertex,key) ∈ before.forest.entries →
      0 ≤ vertex ∧ vertex < client.size) :
    ∃ after vertex key, QueueExtracted client before after vertex key := by
  obtain ⟨heap,layout,forest,contract⟩ := storage.queue.pop_minimum nonempty
  exact ⟨⟨heap,layout,forest⟩,before.layout.minimum,
    before.heap.read before.layout.keys before.layout.minimum,
    queue_extract_of_heap_contract storage nonempty range contract.execution
      contract.represented contract.contents contract.frame contract.refs
      (bookkeeping_of_preserves_other_clocks contract.otherClocks) contract.amortized⟩

/-- All three local contracts are proved for the actual compiled Fibonacci heap.
    This instance closes the modular Dijkstra correctness and runtime proof. -/
def verifiedQueueContracts : QueueContracts where
  constructor := queue_constructor_verified
  update := queue_update_verified
  extract := queue_extract_verified

/-- The compiled algorithm terminates with shortest distances and the combined
    measured runtime bound, using the verified Fibonacci heap implementation. -/
theorem dijkstra_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) :
    ∃ after,
      dijkstra.Call heap (graph,source) after heap.nextRef ∧
      GraphRep after graph size heads adjacency ∧
      ShortestDistances (representedEdges size adjacency) source (after.read heap.nextRef) ∧
      runtimeWork heap after ≤ 22 * (edgeBudget adjacency (vertexRange size) + 1) +
        (popBudget size + 1) * size.toNat :=
  dijkstra_correct_of_queue_contracts verifiedQueueContracts heap graph size source heads adjacency
    representation sourceLower sourceUpper

/-- A valid source has an ordinary distance-sequence output and a bounded sum
    of the ten instrumented clocks. -/
theorem dijkstra_output_exists (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) :
    ∃ output costs,
      dijkstra.ReturnsWithCost (heap,graph,source) output costs ∧
      ShortestDistances (representedEdges size adjacency) source output ∧
      clockWork costs ≤ 22 * (edgeBudget adjacency (vertexRange size) + 1) +
        (popBudget size + 1) * size.toNat :=
  dijkstra_output_exists_of_queue_contracts verifiedQueueContracts heap graph size source heads
    adjacency representation sourceLower sourceUpper

-- Main result: Running time
/-- Every generated output satisfies correctness and the Fibonacci-heap runtime
    bound, without any caller-supplied queue contract. -/
theorem dijkstra_output_with_cost_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (output : Seq) (costs : Clocks)
    (run : dijkstra.ReturnsWithCost (heap,graph,source) output costs) :
    ShortestDistances (representedEdges size adjacency) source output ∧
      clockWork costs ≤ 22 * (edgeBudget adjacency (vertexRange size) + 1) +
        (popBudget size + 1) * size.toNat :=
  dijkstra_output_correct_of_queue_contracts verifiedQueueContracts heap graph size source heads
    adjacency representation sourceLower sourceUpper output costs run

/-- The ordinary output interface states correctness without exposing clocks,
    layouts, forest representations, transitions, or transcripts. -/
theorem dijkstra_output_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (output : Seq) (run : dijkstra.Returns (heap,graph,source) output) :
    ShortestDistances (representedEdges size adjacency) source output := by
  obtain ⟨costs,withCost⟩ := run.withCost
  exact (dijkstra_output_with_cost_correct heap graph size source heads adjacency representation
    sourceLower sourceUpper output costs withCost).1

-- Main result: Correctness
/-- The generated output proposition is equivalent to the mathematical
    shortest-distance specification. -/
theorem dijkstra_output_iff (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) (output : Seq) :
    dijkstra.Returns (heap,graph,source) output ↔
      ShortestDistances (representedEdges size adjacency) source output := by
  constructor
  · exact dijkstra_output_correct heap graph size source heads adjacency representation
      sourceLower sourceUpper output
  · intro correct
    obtain ⟨verifiedOutput,costs,verified,verifiedCorrect,_⟩ := dijkstra_output_exists heap graph
      size source heads adjacency representation sourceLower sourceUpper
    have same := verifiedCorrect.unique correct
    subst output
    exact verified.returns

/-- Every represented graph terminates for every integer source. Invalid
    sources return an all-`-1` sequence without charging any ticks. -/
theorem dijkstra_terminates (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency) :
    ∃ output costs, dijkstra.ReturnsWithCost (heap,graph,source) output costs := by
  by_cases valid : 0 ≤ source ∧ source < size
  · obtain ⟨output,costs,run,_⟩ := dijkstra_output_exists heap graph size source heads adjacency
      representation valid.1 valid.2
    exact ⟨output,costs,run⟩
  · exact ⟨fun _ => -1,fun _ => 0,
      invalid_source_output_with_cost heap graph source size representation.valid
        representation.readSize (by omega)⟩

end DijkstraFibonacciAnalysis
