import DijkstraGeneratedPoints
import Algo2LeanLib.Dijkstra
import Algo2LeanLib.DijkstraExecution
import Algo2LeanExamples.Graph
import GraphIntoDijkstra
import Algo2LeanLib.Footprint
import Algo2LeanLib.CallCost

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
General correctness, termination, and runtime of compiled Dijkstra.

Path mathematics and the queue-independent loop proof are shared in
`Algo2LeanLib.Dijkstra`; this proof adds indexed-heap call contracts, storage and
queue invariants, and the actual adjacency/extraction loops. The primary
`dijkstra_call_contract` preserves caller storage and returns an allocated
shortest-distance sequence with composable clock increments. The ordinary-value
view `dijkstra_output_iff` gives the shortest-distance specification, and
dijkstra_terminates covers every integer source. The smaller edgeless and
one-edge families retain exact costs as readable examples.
-/

namespace DijkstraAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra

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
    (distance settled : SeqRef) (queue : Ref_MinHeap) : Prop :=
  dijkstra.At.extract state ∧ state.heap = heap ∧
  dijkstra.Local.graph state = some graph ∧ dijkstra.Local.distance state = some distance ∧
  dijkstra.Local.settled state = some settled ∧ dijkstra.Local.queue state = some queue

def settleHeap (heap : Heap) (settled : SeqRef) (vertex : Int) : Heap :=
  (heap.write settled vertex 1).tick "settlements"

/-- Initialization uses two reusable queue contracts, then hands the initialized
    local state to the extraction-loop proof. -/
theorem initialize_summary (heap queueHeap queuedHeap finalHeap : Heap)
    (graph : Ref_Graph) (queue : Ref_MinHeap) (source size : Int) (result : SeqRef)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (constructor : MinHeap.Call ((heap.allocate (fun _ => -1)).allocate (fun _ => 0))
      () queueHeap queue)
    (distanceAllocated : heap.nextRef < queueHeap.nextRef)
    (insertion : MinHeap.push_or_decrease.Call (queueHeap.write heap.nextRef source 0)
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
    (graph : Ref_Graph) (distance settled : SeqRef) (queue : Ref_MinHeap)
    (vertex : Int) (heads : CollectionRef)
    (located : AtExtraction state heap graph distance settled queue)
    (queueSize : field_MinHeap_size heap queue = some 1)
    (pop : MinHeap.pop_min.Call heap queue poppedHeap vertex)
    (settledAllocated : settled < poppedHeap.nextRef)
    (distanceAllocated : distance < poppedHeap.nextRef)
    (queueEmpty : field_MinHeap_size (settleHeap poppedHeap settled vertex) queue = some 0)
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
  apply Reaches.prepend (Step.dijkstra_pc27 _ _ _ (by simpa [readQueue] using! pop.1))
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

-- Queue contracts verify the MinHeap class embedded in this single-file example.
-- The modular Dijkstra examples import the indexed_heap component and reuse its
-- independent analysis through a priority-queue contract.
namespace Queue

-- Queue contracts use these aliases for the shared graph representation.
@[simp] theorem object_class_allocate (heap : Heap) (values : Seq) (queue : ObjectRef) :
    (heap.allocate values).objectClass queue = heap.objectClass queue :=
  Heap.objectClass_allocate heap values queue

@[simp] theorem read_field_allocate (heap : Heap) (values : Seq) (queue : ObjectRef) (field : String) :
    (heap.allocate values).readField queue field = heap.readField queue field :=
  Heap.readField_allocate heap values queue field

-- A small source-facing description of the object's storage. The three arrays
-- are separate mutable sequences; aliases to the MinHeap object remain valid.
structure Layout where
  vertices : SeqRef
  positions : SeqRef
  keys : SeqRef
  size : Int

structure Layout.Valid (layout : Layout) (heap : Heap) (queue : Ref_MinHeap) : Prop where
  object : is_MinHeap heap queue
  readVertices : field_MinHeap_vertices heap queue = some layout.vertices
  readPositions : field_MinHeap_positions heap queue = some layout.positions
  readKeys : field_MinHeap_keys heap queue = some layout.keys
  readSize : field_MinHeap_size heap queue = some layout.size
  verticesAllocated : layout.vertices < heap.nextRef
  positionsAllocated : layout.positions < heap.nextRef
  keysAllocated : layout.keys < heap.nextRef
  verticesPositions : layout.vertices ≠ layout.positions
  verticesKeys : layout.vertices ≠ layout.keys
  positionsKeys : layout.positions ≠ layout.keys

-- These observations use only the generated field interface. Updating an
-- array does not replace the object's fields or change its identity.
@[simp] theorem vertices_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_vertices (heap.write ref index value) queue =
      field_MinHeap_vertices heap queue := rfl

@[simp] theorem positions_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_positions (heap.write ref index value) queue =
      field_MinHeap_positions heap queue := rfl

-- Exact heap effect of swap, including the cost counter. The original two
-- vertices are read before either array is changed, including when i = j.
def swapHeap (heap : Heap) (layout : Layout) (i j : Int) : Heap :=
  let a := heap.read layout.vertices i
  let b := heap.read layout.vertices j
  ((((heap.write layout.vertices i b).write layout.vertices j a).write
    layout.positions a j).write layout.positions b i).tick "heap_swaps"

theorem swap_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (i j : Int) :
    MinHeap.swap.Call heap (queue, i, j) (swapHeap heap layout i j) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_swap_pc9 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc8 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc7 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc6 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc5 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc4 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc3 _ _ _)
  apply Reaches.prepend (Step.MinHeap_swap_pc2 _ _ _)
  simp only [vertices_write, positions_write, valid.readVertices, valid.readPositions,
    Option.getD_some, swapHeap]
  exact Reaches.single (Step.MinHeap_swap_pc1 _ _ _)

-- A permutation of positions, with all other positions left fixed.
def exchange (values : Seq) (i j index : Int) : Int :=
  if index = j then values i else if index = i then values j else values index

theorem swap_vertices (heap : Heap) (layout : Layout) (i j index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (swapHeap heap layout i j).read layout.vertices index =
      exchange (heap.read layout.vertices) i j index := by
  simp [swapHeap, exchange, Heap.read, Heap.write, separate]

theorem swap_positions (heap : Heap) (layout : Layout) (i j vertex : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (swapHeap heap layout i j).read layout.positions vertex =
      if vertex = heap.read layout.vertices j then i
      else if vertex = heap.read layout.vertices i then j
      else heap.read layout.positions vertex := by
  simp [swapHeap, Heap.read, Heap.write, Ne.symm separate]

theorem swap_keys (heap : Heap) (layout : Layout) (i j vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (swapHeap heap layout i j).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [swapHeap, Heap.read, Heap.write, Ne.symm separateVertices, Ne.symm separatePositions]

theorem swap_cost (heap : Heap) (layout : Layout) (i j : Int) :
    Heap.cost heap (swapHeap heap layout i j) = Clocks.single "heap_swaps" 1 := by
  funext name
  by_cases swaps : name = "heap_swaps"
  · subst name
    simp [swapHeap, Heap.cost, Heap.tick, Heap.write, Clocks.single]
  · simp [swapHeap, Heap.cost, Heap.tick, Heap.write, Clocks.single, swaps]

-- No duplicate active vertices, no stale positive positions, and exactly -1
-- for vertices outside the heap. These are finite-prefix map invariants.
structure Indexed (vertices positions : Seq) (size : Int) : Prop where
  forward : ∀ index, 0 ≤ index → index < size → positions (vertices index) = index
  backward : ∀ vertex, 0 ≤ positions vertex →
    positions vertex < size ∧ vertices (positions vertex) = vertex
  absent : ∀ vertex, positions vertex < 0 → positions vertex = -1

theorem Indexed.distinct {vertices positions : Seq} {size i j : Int}
    (indexed : Indexed vertices positions size)
    (iNonnegative : 0 ≤ i) (iBound : i < size)
    (jNonnegative : 0 ≤ j) (jBound : j < size) :
    vertices i = vertices j → i = j := by
  intro same
  have left := indexed.forward i iNonnegative iBound
  have right := indexed.forward j jNonnegative jBound
  rw [same] at left
  exact left.symm.trans right

@[simp] theorem exchange_left (values : Seq) (i j : Int) :
    exchange values i j i = values j := by
  by_cases same : i = j <;> simp [exchange, same]

@[simp] theorem exchange_right (values : Seq) (i j : Int) :
    exchange values i j j = values i := by simp [exchange]

-- Swapping two valid heap positions preserves the inverse map, including a
-- self-swap. No heap-order assumption or concrete input values are required.
theorem swap_preserves_indexed (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) :
    Indexed ((swapHeap heap layout i j).read layout.vertices)
      ((swapHeap heap layout i j).read layout.positions) layout.size := by
  have left := indexed.forward i iNonnegative iBound
  have right := indexed.forward j jNonnegative jBound
  have equalIndices : heap.read layout.vertices i = heap.read layout.vertices j → i = j :=
    indexed.distinct iNonnegative iBound jNonnegative jBound
  constructor
  · intro index nonnegative bound
    rw [swap_vertices heap layout i j index separate]
    by_cases atRight : index = j
    · subst index
      rw [exchange_right, swap_positions heap layout i j _ separate]
      by_cases same : heap.read layout.vertices i = heap.read layout.vertices j
      · simp [equalIndices same]
      · simp [same]
    · by_cases atLeft : index = i
      · subst index
        rw [exchange_left, swap_positions heap layout i j _ separate]
        simp
      · have notRight : heap.read layout.vertices index ≠ heap.read layout.vertices j := by
          intro same
          exact atRight (indexed.distinct nonnegative bound jNonnegative jBound same)
        have notLeft : heap.read layout.vertices index ≠ heap.read layout.vertices i := by
          intro same
          exact atLeft (indexed.distinct nonnegative bound iNonnegative iBound same)
        simp only [exchange, atRight, atLeft, ite_false]
        rw [swap_positions heap layout i j _ separate]
        simpa [notRight, notLeft] using indexed.forward index nonnegative bound
  · intro vertex nonnegative
    by_cases isRight : vertex = heap.read layout.vertices j
    · subst vertex
      simp only [swap_positions heap layout i j _ separate, ite_true]
      exact ⟨iBound, by rw [swap_vertices heap layout i j i separate, exchange_left]⟩
    · by_cases isLeft : vertex = heap.read layout.vertices i
      · subst vertex
        simp only [swap_positions heap layout i j _ separate, isRight, ite_false, ite_true]
        exact ⟨jBound, by rw [swap_vertices heap layout i j j separate, exchange_right]⟩
      · have unchanged : (swapHeap heap layout i j).read layout.positions vertex =
            heap.read layout.positions vertex := by
          rw [swap_positions heap layout i j _ separate]
          simp [isRight, isLeft]
        rw [unchanged] at nonnegative ⊢
        obtain ⟨bound, identity⟩ := indexed.backward vertex nonnegative
        have notRight : heap.read layout.positions vertex ≠ j := by
          intro same
          rw [same] at identity
          exact isRight identity.symm
        have notLeft : heap.read layout.positions vertex ≠ i := by
          intro same
          rw [same] at identity
          exact isLeft identity.symm
        refine ⟨bound, ?_⟩
        rw [swap_vertices heap layout i j _ separate]
        simpa [exchange, notRight, notLeft] using identity
  · intro vertex negative
    rw [swap_positions heap layout i j _ separate] at negative ⊢
    split at negative <;> simp_all
    · omega
    split at negative <;> simp_all
    · omega
    exact indexed.absent vertex negative

-- Position numbers may change, but exactly the same vertices remain present.
theorem swap_preserves_membership (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) (vertex : Int) :
    0 ≤ (swapHeap heap layout i j).read layout.positions vertex ↔
      0 ≤ heap.read layout.positions vertex := by
  rw [swap_positions heap layout i j vertex separate]
  by_cases atRight : vertex = heap.read layout.vertices j
  · subst vertex
    simp [indexed.forward j jNonnegative jBound, iNonnegative, jNonnegative]
  · by_cases atLeft : vertex = heap.read layout.vertices i
    · subst vertex
      simp [atRight, indexed.forward i iNonnegative iBound, iNonnegative, jNonnegative]
    · simp [atRight, atLeft]

theorem swap_preserves_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (i j : Int) :
    layout.Valid (swapHeap heap layout i j) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem swap_indexed_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (i j : Int) (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) :
    ∃ after, MinHeap.swap.Call heap (queue, i, j) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after = Clocks.single "heap_swaps" 1 := by
  refine ⟨swapHeap heap layout i j, swap_summary heap queue layout valid i j,
    swap_preserves_layout heap queue layout valid i j, ?_, swap_cost heap layout i j⟩
  exact swap_preserves_indexed heap layout i j valid.verticesPositions indexed
    iNonnegative iBound jNonnegative jBound

-- Simple endpoint cases are checked against the compiled methods as well.
theorem pop_empty_summary (heap : Heap) (queue : Ref_MinHeap) (size : Int)
    (valid : is_MinHeap heap queue) (stored : field_MinHeap_size heap queue = some size)
    (empty : size ≤ 0) :
    MinHeap.pop_min.Call heap queue heap (-1) := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [stored]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_true _ _ _ (by simp [stored, empty]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc19 _ _ _)
  exact Reaches.single (Step.MinHeap_pop_min_pc18 _ _ _)

theorem sift_up_root_summary (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    MinHeap.sift_up.Call heap (queue, 0) heap () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_sift_up_pc3_false _ _ _ (by simp))
  apply Reaches.prepend (Step.MinHeap_sift_up_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_sift_up_pc1 _ _ _)

theorem sift_down_leaf_summary (heap : Heap) (queue : Ref_MinHeap) (index size : Int)
    (valid : is_MinHeap heap queue) (stored : field_MinHeap_size heap queue = some size)
    (leaf : size ≤ 2 * index + 1) :
    MinHeap.sift_down.Call heap (queue, index) heap () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [stored]))
  apply Reaches.prepend (Step.MinHeap_sift_down_pc3_false _ _ _ (by simp [stored]; omega))
  apply Reaches.prepend (Step.MinHeap_sift_down_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_sift_down_pc1 _ _ _)

-- The mathematical depth is the prospective logarithmic bound. Each upward
-- move decreases it by exactly one; downward moves increase it by one.
def depth (index : Int) : Nat := (index.toNat + 1).log2

theorem parent_bounds (index : Int) (positive : 0 < index) :
    0 ≤ Int.fdiv (index - 1) 2 ∧ Int.fdiv (index - 1) 2 < index := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem parent_depth (index : Int) (positive : 0 < index) :
    depth (Int.fdiv (index - 1) 2) + 1 = depth index := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have offset : ((index - 1) / 2).toNat + 1 = (index.toNat + 1) / 2 := by omega
  unfold depth
  rw [offset, Nat.log2_def (index.toNat + 1), if_pos (by omega)]

theorem child_depth (index child : Int) (nonnegative : 0 ≤ index)
    (isChild : child = 2 * index + 1 ∨ child = 2 * index + 2) :
    depth child = depth index + 1 := by
  have offset : (child.toNat + 1) / 2 = index.toNat + 1 := by omega
  unfold depth
  rw [Nat.log2_def (child.toNat + 1), if_pos (by omega), offset]

-- Construction keeps its heap effect in source order. Each sequence has a
-- distinct fresh reference, and the empty queue has no present vertices.
def initializedHeap (heap : Heap) (queue : Ref_MinHeap) : Heap :=
  let first := set_MinHeap_vertices (heap.allocate (fun _ => 0)) queue heap.nextRef
  let second := set_MinHeap_positions (first.allocate (fun _ => -1)) queue first.nextRef
  let third := set_MinHeap_keys (second.allocate (fun _ => 0)) queue second.nextRef
  set_MinHeap_size third queue 0

def emptyLayout (heap : Heap) : Layout :=
  ⟨heap.nextRef, heap.nextRef + 1, heap.nextRef + 2, 0⟩

theorem initialized_object (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) : is_MinHeap (initializedHeap heap queue) queue := by
  simpa [initializedHeap, is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions,
    set_MinHeap_keys, set_MinHeap_size] using valid

theorem initialization_summary (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    MinHeap.__init__.Call heap queue (initializedHeap heap queue) () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap___init___pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc14 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc12 _ _ _
    (by simpa [is_MinHeap] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc11 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc9 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc8 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc7 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc5 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc4 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc3 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions,
      set_MinHeap_keys] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc2 _ _ _)
  exact Reaches.single (Step.MinHeap___init___pc1 _ _ _)

def newHeap (heap : Heap) : Heap :=
  initializedHeap (heap.allocateObject "MinHeap") heap.nextObject

theorem new_heap_summary (heap : Heap) :
    MinHeap.Call heap () (newHeap heap) heap.nextObject := by
  have allocated : is_MinHeap (heap.allocateObject "MinHeap") heap.nextObject := by
    simp [is_MinHeap]
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc5 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc3 _ _ _)
  apply Reaches.trans ((initialization_summary _ _ allocated).2 _)
  apply Reaches.prepend (Step.MinHeap_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_pc1 _ _ _ (initialized_object _ _ allocated))

theorem initialization_layout (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    (emptyLayout heap).Valid (initializedHeap heap queue) queue := by
  have object := initialized_object heap queue valid
  have present := valid.2
  constructor
  · exact object
  · simp [emptyLayout, initializedHeap, field_MinHeap_vertices, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_positions, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_keys, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_size, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asInt, Nat.add_assoc]
  · change heap.nextRef < heap.nextRef + 3
    omega
  · change heap.nextRef + 1 < heap.nextRef + 3
    omega
  · change heap.nextRef + 2 < heap.nextRef + 3
    omega
  · change heap.nextRef ≠ heap.nextRef + 1
    omega
  · change heap.nextRef ≠ heap.nextRef + 2
    omega
  · change heap.nextRef + 1 ≠ heap.nextRef + 2
    omega

theorem initialized_positions (heap : Heap) (queue : Ref_MinHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).positions vertex = -1 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, set_MinHeap_vertices,
    set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size]

theorem new_heap_layout (heap : Heap) :
    (emptyLayout heap).Valid (newHeap heap) heap.nextObject := by
  exact initialization_layout (heap.allocateObject "MinHeap") heap.nextObject (by simp [is_MinHeap])

theorem new_heap_positions (heap : Heap) (vertex : Int) :
    (newHeap heap).read (emptyLayout heap).positions vertex = -1 := by
  exact initialized_positions (heap.allocateObject "MinHeap") heap.nextObject vertex

theorem new_heap_clocks (heap : Heap) : (newHeap heap).clocks = heap.clocks := rfl

@[simp] theorem keys_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_keys (heap.write ref index value) queue = field_MinHeap_keys heap queue := rfl

@[simp] theorem size_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_size (heap.write ref index value) queue = field_MinHeap_size heap queue := rfl

def insertedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) : Heap :=
  set_MinHeap_size (((heap.write layout.keys vertex key).write layout.vertices 0 vertex).write
    layout.positions vertex 0) queue 1

theorem insert_empty_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (empty : layout.size = 0) (vertex key : Int)
    (absent : heap.read layout.positions vertex < 0) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key)
      (insertedHeap heap queue layout vertex key) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_true _ _ _
    (by simp [valid.readPositions, absent]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc14 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc13 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc12 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc11 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc9 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc7 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc5 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_size] using! valid.object))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc3 _ _ _)
  simp only [vertices_write, positions_write, size_write,
    valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    Option.getD_some, empty, Int.zero_add]
  apply Reaches.trans ((sift_up_root_summary _ _
    (by simpa [is_MinHeap, set_MinHeap_size] using! valid.object)).2 _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

theorem inserted_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    { layout with size := 1 }.Valid (insertedHeap heap queue layout vertex key) queue := by
  constructor
  · simpa [insertedHeap, is_MinHeap, set_MinHeap_size] using! valid.object
  · simpa [insertedHeap, field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using! valid.readVertices
  · simpa [insertedHeap, field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using! valid.readPositions
  · simpa [insertedHeap, field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using! valid.readKeys
  · exact field_MinHeap_size_set _ _ _ valid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem inserted_vertex (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (insertedHeap heap queue layout vertex key).read layout.vertices 0 = vertex := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write, separate]

theorem inserted_position (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) :
    (insertedHeap heap queue layout vertex key).read layout.positions vertex = 0 := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write]

theorem inserted_key (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (insertedHeap heap queue layout vertex key).read layout.keys vertex = key := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm separateVertices, Ne.symm separatePositions]

theorem inserted_clocks (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) :
    (insertedHeap heap queue layout vertex key).clocks = heap.clocks := rfl

def poppedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Heap :=
  (set_MinHeap_size (swapHeap heap layout 0 0) queue 0).write
    layout.positions (heap.read layout.vertices 0) (-1)

theorem pop_singleton_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (singleton : layout.size = 1) :
    MinHeap.pop_min.Call heap queue (poppedHeap heap queue layout)
      (heap.read layout.vertices 0) := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 0
  have positions : field_MinHeap_positions
      (set_MinHeap_size (swapHeap heap layout 0 0) queue 0) queue = some layout.positions := by
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_false _ _ _ (by simp [valid.readSize, singleton]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc17 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc16 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc14 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc12 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc11 _ _ _)
  simp only [valid.readSize, valid.readVertices, Option.getD_some, singleton, Int.sub_self]
  apply Reaches.trans ((swap_summary heap queue layout valid 0 0).2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc10 _ _ _ swappedValid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc9 _ _ _
    (by simpa [positions] using! swappedValid.positionsAllocated))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc7_false _ _ _ (by simp))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc2 _ _ _)
  simp only [positions, Option.getD_some]
  exact Reaches.single (Step.MinHeap_pop_min_pc1 _ _ _)

theorem popped_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    { layout with size := 0 }.Valid (poppedHeap heap queue layout) queue := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 0
  constructor
  · change is_MinHeap (set_MinHeap_size (swapHeap heap layout 0 0) queue 0) queue
    simpa [is_MinHeap, set_MinHeap_size] using swappedValid.object
  · simp only [poppedHeap, vertices_write]
    simpa [field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using swappedValid.readVertices
  · simp only [poppedHeap, positions_write]
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  · simp only [poppedHeap, keys_write]
    simpa [field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using swappedValid.readKeys
  · simpa [poppedHeap] using field_MinHeap_size_set _ _ 0 swappedValid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem popped_position (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) :
    (poppedHeap heap queue layout).read layout.positions (heap.read layout.vertices 0) = -1 := by
  simp [poppedHeap]

theorem popped_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (poppedHeap heap queue layout).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [poppedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm separateVertices, Ne.symm separatePositions]

theorem popped_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (poppedHeap heap queue layout).read layout.vertices index = heap.read layout.vertices index := by
  simp [poppedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write, separate]
  split <;> simp_all

theorem popped_cost (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) :
    Heap.cost heap (poppedHeap heap queue layout) = Clocks.single "heap_swaps" 1 := by
  exact swap_cost heap layout 0 0

-- Client-owned arrays, such as Dijkstra's distances and settled flags, are
-- unchanged by creating and manipulating this separate priority queue.
theorem new_heap_read_old (heap : Heap) (ref : SeqRef) (index : Int)
    (allocated : ref < heap.nextRef) :
    (newHeap heap).read ref index = heap.read ref index := by
  have first : ref ≠ heap.nextRef := Nat.ne_of_lt allocated
  have second : ref ≠ heap.nextRef + 1 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))
  have third : ref ≠ heap.nextRef + 2 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))
  simp [newHeap, initializedHeap, set_MinHeap_vertices, set_MinHeap_positions,
    set_MinHeap_keys, set_MinHeap_size, Heap.read, Heap.allocate, Heap.allocateObject,
    first, second, third, Nat.add_assoc]

theorem inserted_read_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (vertex key : Int) (ref : SeqRef) (index : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions)
    (notKeys : ref ≠ layout.keys) :
    (insertedHeap heap queue layout vertex key).read ref index = heap.read ref index := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions, notKeys]

theorem popped_read_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (ref : SeqRef) (index : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions) :
    (poppedHeap heap queue layout).read ref index = heap.read ref index := by
  simp [poppedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions]

/-- The parent of a positive position in the zero-based binary heap. -/
def parent (index : Int) : Int := Int.fdiv (index - 1) 2

/-- Heap order concerns only the finite active prefix; priorities are arbitrary integers. -/
def Ordered (priority : Seq) (size : Int) : Prop :=
  ∀ child, 0 < child → child < size → priority (parent child) ≤ priority child

/-- Local parent comparisons imply that the root is a minimum of the active heap. -/
theorem Ordered.root_minimum {priority : Seq} {size : Int} (ordered : Ordered priority size)
    (index : Int) (nonnegative : 0 ≤ index) (within : index < size) :
    priority 0 ≤ priority index := by
  have result : ∀ n : Nat, (n : Int) < size → priority 0 ≤ priority (n : Int) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro bound
      by_cases zero : n = 0
      · subst n; exact Int.le_refl _
      · have positive : 0 < (n : Int) := by omega
        have bounds := parent_bounds (n : Int) positive
        have smaller : (parent (n : Int)).toNat < n := by
          unfold parent
          omega
        have parentBound : ((parent (n : Int)).toNat : Int) < size := by
          unfold parent
          omega
        have previous := ih _ smaller parentBound
        have parentCast : ((parent (n : Int)).toNat : Int) = parent (n : Int) :=
          Int.toNat_of_nonneg bounds.1
        rw [parentCast] at previous
        exact Int.le_trans previous (ordered _ positive bound)
  simpa [Int.toNat_of_nonneg nonnegative] using result index.toNat (by omega)

/-- At sift-up's moving position only its incoming edge may violate heap order.
    Its parent is also below its children, so exchanging parent and child is safe. -/
structure UpInvariant (priority : Seq) (size index : Int) : Prop where
  orderedExcept : ∀ child, 0 < child → child < size → child ≠ index →
    priority (parent child) ≤ priority child
  parentBelowChildren : ∀ child, 0 < child → child < size → parent child = index →
    0 < index → priority (parent index) ≤ priority child

/-- Once the exceptional edge is ordered (or the root is reached), sift-up is done. -/
theorem UpInvariant.finish {priority : Seq} {size index : Int}
    (invariant : UpInvariant priority size index)
    (done : index ≤ 0 ∨ priority (parent index) ≤ priority index) :
    Ordered priority size := by
  intro child positive bound
  by_cases same : child = index
  · subst child
    rcases done with nonpositive | ordered
    · omega
    · exact ordered
  · exact invariant.orderedExcept child positive bound same

/-- Exchanging an out-of-order position with its parent moves the single
    exceptional edge up one level; every other heap-order edge stays valid. -/
theorem UpInvariant.exchange_parent {priority : Seq} {size index : Int}
    (invariant : UpInvariant priority size index)
    (positive : 0 < index) (within : index < size)
    (outOfOrder : priority index < priority (parent index)) :
    UpInvariant (exchange priority index (parent index)) size (parent index) := by
  have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index positive
  have different : index ≠ parent index := by omega
  constructor
  · intro child childPositive childBound notParent
    by_cases atIndex : child = index
    · subst child
      rw [exchange_right, exchange_left]
      exact Int.le_of_lt outOfOrder
    · by_cases fromIndex : parent child = index
      · have below := invariant.parentBelowChildren child childPositive childBound fromIndex positive
        simpa [exchange, fromIndex, atIndex, notParent, different, Ne.symm different] using below
      · by_cases fromParent : parent child = parent index
        · have old := invariant.orderedExcept child childPositive childBound atIndex
          rw [fromParent] at old
          simpa [exchange, fromParent, atIndex, notParent] using
            Int.le_trans (Int.le_of_lt outOfOrder) old
        · simpa [exchange, fromIndex, fromParent, atIndex, notParent] using
            invariant.orderedExcept child childPositive childBound atIndex
  · intro child childPositive childBound fromParent parentPositive
    have ancestorBounds : 0 ≤ parent (parent index) ∧ parent (parent index) < parent index :=
      parent_bounds (parent index) parentPositive
    have ancestorNotParent : parent (parent index) ≠ parent index := by omega
    have ancestorNotIndex : parent (parent index) ≠ index := by omega
    have childBounds : parent child < child := (parent_bounds child childPositive).2
    have notParent : child ≠ parent index := by omega
    have oldParent := invariant.orderedExcept (parent index) parentPositive (by omega) (by omega)
    by_cases atIndex : child = index
    · subst child
      simpa [exchange, ancestorNotParent, ancestorNotIndex, different] using oldParent
    · have oldChild := invariant.orderedExcept child childPositive childBound atIndex
      rw [fromParent] at oldChild
      simpa [exchange, ancestorNotParent, ancestorNotIndex, notParent, atIndex] using
        Int.le_trans oldParent oldChild

/-- Lowering one priority is precisely the precondition that sift-up repairs. -/
theorem Ordered.decrease {priority : Seq} {size index key : Int}
    (ordered : Ordered priority size) (within : index < size)
    (lower : key ≤ priority index) :
    UpInvariant (fun position => if position = index then key else priority position) size index := by
  constructor
  · intro child positive bound different
    by_cases parentSame : parent child = index
    · have old := ordered child positive bound
      rw [parentSame] at old
      simpa [parentSame, different] using Int.le_trans lower old
    · simpa [parentSame, different] using ordered child positive bound
  · intro child positive bound fromIndex indexPositive
    have parentDifferent : parent index ≠ index := by
      have : parent index < index := (parent_bounds index indexPositive).2
      omega
    have childDifferent : child ≠ index := by
      have : parent child < child := (parent_bounds child positive).2
      omega
    have first := ordered index indexPositive within
    have second := ordered child positive bound
    rw [fromIndex] at second
    simpa [parentDifferent, childDifferent] using Int.le_trans first second

/-- The abstract priority exchange is exactly the effect of the compiled swap. -/
theorem swap_priorities (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (fun position => (swapHeap heap layout i j).read layout.keys
      ((swapHeap heap layout i j).read layout.vertices position)) =
    exchange (fun position => heap.read layout.keys (heap.read layout.vertices position)) i j := by
  funext position
  rw [swap_keys heap layout i j _ separateVertices separatePositions,
    swap_vertices heap layout i j position separate]
  simp only [exchange]
  split <;> simp_all
  split <;> simp_all

/-- A representation-level minimum statement, ready for an extraction contract. -/
theorem root_minimum_vertex (heap : Heap) (layout : Layout)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun position => heap.read layout.keys (heap.read layout.vertices position))
      layout.size)
    (vertex : Int) (present : 0 ≤ heap.read layout.positions vertex) :
    heap.read layout.keys (heap.read layout.vertices 0) ≤ heap.read layout.keys vertex := by
  obtain ⟨bound, identity⟩ := indexed.backward vertex present
  have minimum := ordered.root_minimum (heap.read layout.positions vertex) present bound
  simpa [identity] using minimum

/-- Appending an absent vertex updates both directions of the position map. -/
theorem Indexed.insert {vertices positions : Seq} {size vertex : Int}
    (indexed : Indexed vertices positions size) (nonnegative : 0 ≤ size)
    (absent : positions vertex = -1) :
    Indexed (fun index => if index = size then vertex else vertices index)
      (fun value => if value = vertex then size else positions value) (size + 1) := by
  constructor
  · intro index lower upper
    by_cases last : index = size
    · subst index; simp
    · have oldBound : index < size := by omega
      have different : vertices index ≠ vertex := by
        intro same
        have old := indexed.forward index lower oldBound
        rw [same, absent] at old
        omega
      simpa [last, different] using indexed.forward index lower oldBound
  · intro value present
    by_cases same : value = vertex
    · subst value; simp; omega
    · simp only [same, ite_false] at present ⊢
      obtain ⟨bound, identity⟩ := indexed.backward value present
      have different : positions value ≠ size := by omega
      exact ⟨by omega, by simp [different, identity]⟩
  · intro value negative
    by_cases same : value = vertex
    · subst value
      simp only [ite_true] at negative
      omega
    · simpa [same] using indexed.absent value (by simpa [same] using negative)

/-- Adding a leaf preserves all order edges except the new leaf's parent edge. -/
theorem Ordered.append {priority : Seq} {size key : Int}
    (ordered : Ordered priority size) :
    UpInvariant (fun index => if index = size then key else priority index) (size + 1) size := by
  constructor
  · intro child positive bound different
    have oldBound : child < size := by omega
    have parentBound : parent child < child := (parent_bounds child positive).2
    have parentDifferent : parent child ≠ size := by omega
    simpa [different, parentDifferent] using ordered child positive oldBound
  · intro child positive bound fromLast lastPositive
    have parentBound : parent child < child := (parent_bounds child positive).2
    omega

-- The loop proof is expressed through the named source location and its two
-- live inputs. Other temporary locals are irrelevant to the specification.
def AtSiftUp (state : Configuration) (queue : Ref_MinHeap) (index : Int) : Prop :=
  MinHeap.sift_up.At.up_loop state ∧
    MinHeap.sift_up.Local.self state = some queue ∧
    MinHeap.sift_up.Local.i state = some index

@[simp] theorem keys_tick (heap : Heap) (name : String) (amount : Nat) (queue : Ref_MinHeap) :
    field_MinHeap_keys (heap.tick name amount) queue = field_MinHeap_keys heap queue := rfl

@[simp] theorem vertices_tick (heap : Heap) (name : String) (amount : Nat) (queue : Ref_MinHeap) :
    field_MinHeap_vertices (heap.tick name amount) queue = field_MinHeap_vertices heap queue := rfl

theorem sift_up_stop (state : Configuration) (queue : Ref_MinHeap) (index : Int)
    (location : AtSiftUp state queue index) (atRoot : index ≤ 0) :
    MinHeap.sift_up.CallFrom state state.heap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_false _ _ _
      (by simp only [decide_eq_false_iff_not]; omega))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc2 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_up_pc1 _ _ _)

theorem sift_up_ordered (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (location : AtSiftUp state queue index)
    (valid : layout.Valid state.heap queue) (positive : 0 < index)
    (ordered : state.heap.read layout.keys (state.heap.read layout.vertices
        (Int.fdiv (index - 1) 2)) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices index)) :
    MinHeap.sift_up.CallFrom state (state.heap.tick "heap_comparisons") () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    change heap.read layout.keys (heap.read layout.vertices (Int.fdiv (s.v1 - 1) 2)) ≤
      heap.read layout.keys (heap.read layout.vertices s.v1) at ordered
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_true _ _ _ (by simp [positive]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc16 _ _ _ (by decide))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc13_true _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using ordered))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc12 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_up_pc11 _ _ _)

theorem Layout.Valid.tick {layout : Layout} {heap : Heap} {queue : Ref_MinHeap}
    (valid : layout.Valid heap queue) (name : String) (amount : Nat := 1) :
    layout.Valid (heap.tick name amount) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

def upHeap (heap : Heap) (layout : Layout) (index : Int) : Heap :=
  swapHeap (heap.tick "heap_comparisons") layout index (Int.fdiv (index - 1) 2)

theorem upHeap_priorities (heap : Heap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (fun position => (upHeap heap layout index).read layout.keys
      ((upHeap heap layout index).read layout.vertices position)) =
      exchange (fun position => heap.read layout.keys (heap.read layout.vertices position))
        index (parent index) := by
  simpa [upHeap, parent] using swap_priorities (heap.tick "heap_comparisons") layout
    index (parent index) separate separateVertices separatePositions

theorem upHeap_read_other (heap : Heap) (layout : Layout) (index : Int)
    (ref : SeqRef) (position : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions) :
    (upHeap heap layout index).read ref position = heap.read ref position := by
  simp [upHeap, swapHeap, Heap.read, Heap.write, notVertices, notPositions]

-- One unsuccessful comparison swaps with the parent and returns to the named
-- loop location. Any proof for the remaining loop can be plugged in here.
theorem sift_up_continue (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (finalHeap : Heap) (location : AtSiftUp state queue index)
    (valid : layout.Valid state.heap queue) (positive : 0 < index)
    (unordered : ¬ state.heap.read layout.keys (state.heap.read layout.vertices
        (Int.fdiv (index - 1) 2)) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices index))
    (remaining : ∀ nextState, AtSiftUp nextState queue (Int.fdiv (index - 1) 2) →
      nextState.heap = upHeap state.heap layout index →
      MinHeap.sift_up.CallFrom nextState finalHeap ()) :
    MinHeap.sift_up.CallFrom state finalHeap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    change ¬ heap.read layout.keys (heap.read layout.vertices (Int.fdiv (s.v1 - 1) 2)) ≤
      heap.read layout.keys (heap.read layout.vertices s.v1) at unordered
    let parent := Int.fdiv (s.v1 - 1) 2
    let nextState : Configuration := .active (upHeap heap layout s.v1)
      (.fn_MinHeap_sift_up 4 { s with
        v1 := parent
        v2 := parent
        t4 := decide (s.v1 > 0)
        t5 := ()
        t6 := s.v0
        t7 := s.v1
        t8 := parent
        t9 := decide (heap.read layout.keys (heap.read layout.vertices parent) ≤
          heap.read layout.keys (heap.read layout.vertices s.v1)) }) originalStack
    have finish := remaining nextState ⟨True.intro, rfl, rfl⟩ rfl
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_true _ _ _ (by simp [positive]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc16 _ _ _ (by decide))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc13_false _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using unordered))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc10 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc9 _ _ _ valid.object)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc8 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc7 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc6 _ _ _)
    apply Reaches.trans ((swap_summary (heap.tick "heap_comparisons") s.v0 layout
      (valid.tick "heap_comparisons") s.v1 parent).2 _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc5 _ _ _)
    simpa only [keys_tick, vertices_tick, valid.readKeys, valid.readVertices,
      Option.getD_some, Heap.read_tick] using! finish stack

-- Reordering the integer arrays leaves object fields, typed collections, and
-- all allocation counters unchanged. In particular, graph objects in a caller
-- remain available with their original fields after either sifting method.
structure OtherStoragePreserved (before after : Heap) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections

theorem OtherStoragePreserved.refl (heap : Heap) : OtherStoragePreserved heap heap :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem OtherStoragePreserved.trans {first second third : Heap}
    (initial : OtherStoragePreserved first second)
    (remaining : OtherStoragePreserved second third) : OtherStoragePreserved first third :=
  ⟨remaining.nextRef.trans initial.nextRef, remaining.nextObject.trans initial.nextObject,
    remaining.objects.trans initial.objects, remaining.nextCollection.trans initial.nextCollection,
    remaining.collections.trans initial.collections⟩

/-- The three sequence identities owned by an indexed queue. -/
def Layout.refs (layout : Layout) : List SeqRef :=
  [layout.vertices, layout.positions, layout.keys]

/-- Existing exact array and storage facts give a reusable caller footprint. -/
theorem OtherStoragePreserved.footprint {before after : Heap}
    (storage : OtherStoragePreserved before after) (refs : List SeqRef)
    (arrays : ∀ ref, ref ∉ refs → after.read ref = before.read ref) :
    before.Footprint after refs [] [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_eq storage.nextRef.symm
  · exact Nat.le_of_eq storage.nextObject.symm
  · exact Nat.le_of_eq storage.nextCollection.symm
  · intro ref _; simp only [Heap.objectClass, storage.objects]
  · intro ref _; simp only [Heap.collectionType, storage.collections]
  · intro ref _ outside; exact arrays ref outside
  · intro ref _ _; exact congrFun storage.objects ref
  · intro ref _ _; exact congrFun storage.collections ref

-- The remaining loop has one final heap for every configuration with these
-- source inputs. Induction follows tree depth, not the transcript length.
theorem sift_up_loop (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after,
      (∀ state, AtSiftUp state queue index → state.heap = heap →
        MinHeap.sift_up.CallFrom state after ()) ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      after.clocks "heap_comparisons" ≤ heap.clocks "heap_comparisons" + depth index ∧
      after.clocks "heap_swaps" ≤ heap.clocks "heap_swaps" + depth index ∧
      (UpInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  generalize rankEq : depth index = rank
  induction rank using Nat.strongRecOn generalizing heap index with
  | ind rank inductionHypothesis =>
    by_cases positive : 0 < index
    · have parentFacts := parent_bounds index positive
      have depthChange := parent_depth index positive
      by_cases ordered : heap.read layout.keys
          (heap.read layout.vertices (Int.fdiv (index - 1) 2)) ≤
          heap.read layout.keys (heap.read layout.vertices index)
      · refine ⟨heap.tick "heap_comparisons", ?_, valid.tick "heap_comparisons", indexed,
          ?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · intro state location sameHeap
          have validState : layout.Valid state.heap queue := by simpa [sameHeap] using valid
          have orderedState : state.heap.read layout.keys
              (state.heap.read layout.vertices (Int.fdiv (index - 1) 2)) ≤
              state.heap.read layout.keys (state.heap.read layout.vertices index) := by
            simpa [sameHeap] using ordered
          simpa [sameHeap] using sift_up_ordered state queue layout index location
            validState positive orderedState
        · simp only [Heap.clocks_tick_same]
          omega
        · simp [Heap.tick]
        · intro invariant
          exact invariant.finish (Or.inr ordered)
        · intro ref _ _ position
          exact Heap.read_tick heap "heap_comparisons" 1 ref position
        · intro vertex
          rfl
        · intro name notComparisons _
          exact Heap.clocks_tick_other heap "heap_comparisons" name notComparisons
      · let nextHeap := upHeap heap layout index
        have nextValid : layout.Valid nextHeap queue :=
          swap_preserves_layout (heap.tick "heap_comparisons") queue layout
            (valid.tick "heap_comparisons") index (Int.fdiv (index - 1) 2)
        have nextIndexed : Indexed (nextHeap.read layout.vertices)
            (nextHeap.read layout.positions) layout.size :=
          swap_preserves_indexed (heap.tick "heap_comparisons") layout index
            (Int.fdiv (index - 1) 2) valid.verticesPositions indexed
            nonnegative bound parentFacts.1 (by omega)
        obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
            unchanged, presentIff, otherClocks, storage⟩ :=
          inductionHypothesis (depth (Int.fdiv (index - 1) 2)) (by omega)
            nextHeap (Int.fdiv (index - 1) 2) nextValid nextIndexed parentFacts.1 (by omega) rfl
        refine ⟨after, ?_, afterValid, afterIndexed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro state location sameHeap
          apply sift_up_continue state queue layout index after location
            (by simpa [sameHeap] using valid) positive (by simpa [sameHeap] using ordered)
          intro nextState nextLocation nextHeapEq
          apply remaining nextState nextLocation
          simpa [sameHeap, nextHeap] using nextHeapEq
        · simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write] at comparisons
          omega
        · simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write] at swaps
          omega
        · intro invariant
          apply repair
          change UpInvariant (fun position => (upHeap heap layout index).read layout.keys
            ((upHeap heap layout index).read layout.vertices position)) layout.size (parent index)
          rw [upHeap_priorities heap layout index valid.verticesPositions valid.verticesKeys valid.positionsKeys]
          exact invariant.exchange_parent positive bound (by unfold parent; omega)
        · intro ref notVertices notPositions position
          rw [unchanged ref notVertices notPositions position]
          exact upHeap_read_other heap layout index ref position notVertices notPositions
        · intro vertex
          rw [presentIff vertex]
          exact swap_preserves_membership (heap.tick "heap_comparisons") layout index
            (Int.fdiv (index - 1) 2) valid.verticesPositions indexed nonnegative bound
            parentFacts.1 (by omega) vertex
        · intro name notComparisons notSwaps
          rw [otherClocks name notComparisons notSwaps]
          simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write, notComparisons, notSwaps]
        · exact (show OtherStoragePreserved heap nextHeap from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage
    · refine ⟨heap, ?_, valid, indexed, Nat.le_add_right _ _, Nat.le_add_right _ _,
        ?_, ?_, ?_, ?_, OtherStoragePreserved.refl heap⟩
      · intro state location sameHeap
        simpa [sameHeap] using sift_up_stop state queue index location (by omega)
      · intro invariant
        exact invariant.finish (Or.inl (by omega))
      · intro ref _ _ position
        rfl
      · intro vertex
        rfl
      · intro name _ _
        rfl

-- A valid active index always terminates. The map invariant is preserved, and
-- each of the two instrumented operation counts is at most floor(log2(i+1)).
-- Sift-up repairs its expected single-edge order exception. Keys and client
-- arrays are preserved because only the vertices and positions arrays change.
theorem sift_up_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after, MinHeap.sift_up.Call heap (queue, index) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after "heap_comparisons" ≤ depth index ∧
      Heap.cost heap after "heap_swaps" ≤ depth index ∧
      (UpInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
      unchanged, presentIff, otherClocks, storage⟩ :=
    sift_up_loop heap queue layout index valid indexed nonnegative bound
  refine ⟨after, ⟨valid.object, ?_⟩, afterValid, afterIndexed, ?_, ?_, repair,
    unchanged, presentIff, otherClocks, storage⟩
  · exact remaining (MinHeap.sift_up.initial heap (queue, index)) ⟨True.intro, rfl, rfl⟩ rfl
  · unfold Heap.cost
    omega
  · unfold Heap.cost
    omega

/-- A non-improving key leaves queue data unchanged and charges one comparison. -/
theorem push_unchanged_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (unchanged : heap.read layout.keys vertex ≤ key) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key)
      (heap.tick "heap_comparisons") () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_false _ _ _
    (by simp [valid.readPositions]; omega))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc22 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc21 _ _ _
    (by change (field_MinHeap_keys heap queue).isSome = true ∧
          (field_MinHeap_keys heap queue).getD 0 < heap.nextRef
        simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc20_false _ _ _
    (by change decide (key < (heap.tick "heap_comparisons").read
          ((field_MinHeap_keys (heap.tick "heap_comparisons") queue).getD 0) vertex) = false
        change decide (key < heap.read ((field_MinHeap_keys heap queue).getD 0) vertex) = false
        simp [valid.readKeys]; omega))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

/-- The heap seen by sift-up after an existing key is lowered. -/
def decreasedHeap (heap : Heap) (layout : Layout) (vertex key : Int) : Heap :=
  (heap.tick "heap_comparisons").write layout.keys vertex key

/-- The caller composes a sift-up contract without inspecting sift-up's transitions. -/
theorem decrease_summary (heap finalHeap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (improves : key < heap.read layout.keys vertex)
    (sift : MinHeap.sift_up.Call (decreasedHeap heap layout vertex key)
      (queue, heap.read layout.positions vertex) finalHeap ()) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key) finalHeap () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_false _ _ _
    (by simp [valid.readPositions]; omega))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc22 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc21 _ _ _
    (by change (field_MinHeap_keys heap queue).isSome = true ∧
          (field_MinHeap_keys heap queue).getD 0 < heap.nextRef
        simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc20_true _ _ _
    (by change decide (key < heap.read ((field_MinHeap_keys heap queue).getD 0) vertex) = true
        simp [valid.readKeys, improves]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc19 _ _ _
    (by change (field_MinHeap_keys heap queue).isSome = true ∧
          (field_MinHeap_keys heap queue).getD 0 < heap.nextRef
        simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc18 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc17 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc16 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc15 _ _ _)
  change Reaches Step
    (.active ((heap.tick "heap_comparisons").write
        ((field_MinHeap_keys heap queue).getD 0) vertex key)
      (.fn_MinHeap_sift_up 4 { v0 := queue, v1 := heap.read ((field_MinHeap_positions heap queue).getD 0) vertex }) _) _
  simp only [valid.readKeys, valid.readPositions, Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

/-- Preparing an absent vertex at the new last position, before sift-up. -/
def appendedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) : Heap :=
  set_MinHeap_size (((heap.write layout.keys vertex key).write layout.vertices layout.size vertex).write
    layout.positions vertex layout.size) queue (layout.size + 1)

/-- Insertion itself is a few writes, followed by a reusable sift-up summary. -/
theorem append_summary (heap finalHeap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (absent : heap.read layout.positions vertex < 0)
    (sift : MinHeap.sift_up.Call (appendedHeap heap queue layout vertex key)
      (queue, layout.size) finalHeap ()) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key) finalHeap () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_true _ _ _
    (by simp [valid.readPositions, absent]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc14 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc13 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc12 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc11 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc9 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc7 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc5 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_size] using! valid.object))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc3 _ _ _)
  simp only [vertices_write, positions_write, size_write,
    valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

/-- Array writes preserve the object's fields, reference bounds, and separation. -/
theorem Layout.Valid.write {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (valid : layout.Valid heap queue) (ref : SeqRef) (index value : Int) :
    layout.Valid (heap.write ref index value) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem appended_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    { layout with size := layout.size + 1 }.Valid (appendedHeap heap queue layout vertex key) queue := by
  constructor
  · simpa [appendedHeap, is_MinHeap, set_MinHeap_size] using! valid.object
  · simpa [appendedHeap, field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using! valid.readVertices
  · simpa [appendedHeap, field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using! valid.readPositions
  · simpa [appendedHeap, field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using! valid.readKeys
  · exact field_MinHeap_size_set _ _ _ valid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem appended_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key index : Int) :
    (appendedHeap heap queue layout vertex key).read layout.vertices index =
      if index = layout.size then vertex else heap.read layout.vertices index := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    valid.verticesPositions, valid.verticesKeys]

theorem appended_positions (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key value : Int) :
    (appendedHeap heap queue layout vertex key).read layout.positions value =
      if value = vertex then layout.size else heap.read layout.positions value := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm valid.verticesPositions, valid.positionsKeys]

theorem appended_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key value : Int) :
    (appendedHeap heap queue layout vertex key).read layout.keys value =
      if value = vertex then key else heap.read layout.keys value := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm valid.verticesKeys, Ne.symm valid.positionsKeys]

theorem appended_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ layout.size) (vertex key : Int)
    (absent : heap.read layout.positions vertex = -1) :
    Indexed ((appendedHeap heap queue layout vertex key).read layout.vertices)
      ((appendedHeap heap queue layout vertex key).read layout.positions) (layout.size + 1) := by
  have vertices : (appendedHeap heap queue layout vertex key).read layout.vertices =
      (fun index => if index = layout.size then vertex else heap.read layout.vertices index) :=
    funext (appended_vertices heap queue layout valid vertex key)
  have positions : (appendedHeap heap queue layout vertex key).read layout.positions =
      (fun value => if value = vertex then layout.size else heap.read layout.positions value) :=
    funext (appended_positions heap queue layout valid vertex key)
  rw [vertices, positions]
  exact indexed.insert nonnegative absent

/-- Order predicates only inspect active positions; infinite sequence tails do not matter. -/
theorem Ordered.congr {first second : Seq} {size : Int} (ordered : Ordered first size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    Ordered second size := by
  intro child positive bound
  have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
  rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
  exact ordered child positive bound

theorem UpInvariant.congr {first second : Seq} {size index : Int}
    (invariant : UpInvariant first size index)
    (within : index < size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    UpInvariant second size index := by
  constructor
  · intro child positive bound different
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
    exact invariant.orderedExcept child positive bound different
  · intro child positive bound fromIndex indexPositive
    have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index indexPositive
    rw [← same child (by omega) bound, ← same (parent index) bounds.1 (by omega)]
    exact invariant.parentBelowChildren child positive bound fromIndex indexPositive

/-- Appending an absent vertex creates exactly the local disorder that sift-up repairs. -/
theorem appended_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (vertex key : Int) (absent : heap.read layout.positions vertex = -1) :
    UpInvariant (fun index => (appendedHeap heap queue layout vertex key).read layout.keys
      ((appendedHeap heap queue layout vertex key).read layout.vertices index)) (layout.size + 1) layout.size := by
  apply (ordered.append (key := key)).congr (by omega)
  intro index lower upper
  rw [appended_keys heap queue layout valid, appended_vertices heap queue layout valid]
  by_cases last : index = layout.size
  · simp [last]
  · have oldBound : index < layout.size := by omega
    have different : heap.read layout.vertices index ≠ vertex := by
      intro same
      have old := indexed.forward index lower oldBound
      rw [same, absent] at old
      omega
    simp [last, different]

/-- Lowering a present vertex leaves the position map intact. -/
theorem decreased_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (vertex key : Int) :
    Indexed ((decreasedHeap heap layout vertex key).read layout.vertices)
      ((decreasedHeap heap layout vertex key).read layout.positions) layout.size := by
  have vertices : (decreasedHeap heap layout vertex key).read layout.vertices =
      heap.read layout.vertices := by
    funext index
    simp [decreasedHeap, valid.verticesKeys]
  have positions : (decreasedHeap heap layout vertex key).read layout.positions =
      heap.read layout.positions := by
    funext value
    simp [decreasedHeap, valid.positionsKeys]
  rw [vertices, positions]
  exact indexed

/-- The array-backed decrease changes the priority at just the vertex's active position. -/
theorem decreased_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (vertex key : Int) (present : 0 ≤ heap.read layout.positions vertex)
    (lower : key ≤ heap.read layout.keys vertex) :
    UpInvariant (fun index => (decreasedHeap heap layout vertex key).read layout.keys
      ((decreasedHeap heap layout vertex key).read layout.vertices index))
      layout.size (heap.read layout.positions vertex) := by
  obtain ⟨bound, identity⟩ := indexed.backward vertex present
  have lowerAtIndex : key ≤ heap.read layout.keys
      (heap.read layout.vertices (heap.read layout.positions vertex)) := by simpa [identity] using lower
  apply (ordered.decrease bound lowerAtIndex).congr bound
  intro index nonnegative within
  have vertices : (decreasedHeap heap layout vertex key).read layout.vertices index =
      heap.read layout.vertices index := by
    simp [decreasedHeap, Heap.read, Heap.write, valid.verticesKeys]
  rw [vertices]
  by_cases same : index = heap.read layout.positions vertex
  · subst index
    simp [decreasedHeap, identity]
  · have different : heap.read layout.vertices index ≠ vertex := by
      intro equal
      have old := indexed.forward index nonnegative within
      rw [equal] at old
      omega
    simp [decreasedHeap, same, different]

/-- A usable priority queue combines storage validity, inverse positions, and
    heap order. Clients need no program counters or transcript representation. -/
structure QueueRep (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Prop where
  valid : layout.Valid heap queue
  nonnegative : 0 ≤ layout.size
  indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size
  ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size

/-- Every constructor call supplies a valid empty priority queue. -/
theorem new_heap_rep (heap : Heap) :
    QueueRep (newHeap heap) heap.nextObject (emptyLayout heap) := by
  refine ⟨new_heap_layout heap, by simp [emptyLayout], ?_, ?_⟩
  · constructor
    · intro index lower upper
      change index < 0 at upper
      omega
    · intro vertex present
      rw [new_heap_positions] at present
      omega
    · intro vertex _
      exact new_heap_positions heap vertex
  · intro child positive upper
    change child < 0 at upper
    omega

/-- Insert one absent vertex, restore heap order, and pay at most one comparison
    and swap per parent level. No other vertex enters or leaves the queue. -/
theorem insert_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (absent : heap.read layout.positions vertex = -1) :
    ∃ after, MinHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue { layout with size := layout.size + 1 } ∧
      (∀ value, 0 ≤ after.read layout.positions value ↔
        value = vertex ∨ 0 ≤ heap.read layout.positions value) ∧
      (∀ value, after.read layout.keys value =
        if value = vertex then key else heap.read layout.keys value) ∧
      Heap.cost heap after "heap_comparisons" ≤ depth layout.size ∧
      Heap.cost heap after "heap_swaps" ≤ depth layout.size ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
        ∀ index, after.read ref index = heap.read ref index) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved (set_MinHeap_size heap queue (layout.size + 1)) after := by
  have sizeNonnegative := representation.nonnegative
  let prepared := appendedHeap heap queue layout vertex key
  let enlarged := { layout with size := layout.size + 1 }
  have valid : enlarged.Valid prepared queue :=
    appended_layout heap queue layout representation.valid vertex key
  have indexed : Indexed (prepared.read layout.vertices) (prepared.read layout.positions) enlarged.size :=
    appended_indexed heap queue layout representation.valid representation.indexed
      representation.nonnegative vertex key absent
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_up_summary prepared queue enlarged layout.size valid indexed representation.nonnegative (by dsimp [enlarged]; omega)
  refine ⟨after, append_summary heap after queue layout representation.valid vertex key (by omega) sift,
    ⟨afterValid, by dsimp [enlarged]; omega, afterIndexed, ?_⟩, ?_, ?_, comparisons, swaps, ?_, ?_, ?_⟩
  · exact repair (appended_order heap queue layout representation.valid representation.indexed
      representation.ordered vertex key absent)
  · intro value
    rw [membership value]
    change 0 ≤ (appendedHeap heap queue layout vertex key).read layout.positions value ↔ _
    rw [appended_positions heap queue layout representation.valid]
    by_cases same : value = vertex <;> simp [same, representation.nonnegative]
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    exact appended_keys heap queue layout representation.valid vertex key value
  · intro ref notVertices notPositions notKeys index
    rw [unchanged ref notVertices notPositions index]
    simp [prepared, appendedHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions, notKeys]
  · exact clocks
  · exact (show OtherStoragePreserved (set_MinHeap_size heap queue (layout.size + 1)) prepared
      from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage

/-- Lower one present key, preserving membership and size, and restore order.
    The first comparison tests improvement; remaining work is logarithmic. -/
theorem decrease_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (improves : key < heap.read layout.keys vertex) :
    ∃ after, MinHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue layout ∧
      (∀ value, 0 ≤ after.read layout.positions value ↔ 0 ≤ heap.read layout.positions value) ∧
      (∀ value, after.read layout.keys value =
        if value = vertex then key else heap.read layout.keys value) ∧
      Heap.cost heap after "heap_comparisons" ≤ depth (heap.read layout.positions vertex) + 1 ∧
      Heap.cost heap after "heap_swaps" ≤ depth (heap.read layout.positions vertex) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
        ∀ index, after.read ref index = heap.read ref index) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  let prepared := decreasedHeap heap layout vertex key
  have valid : layout.Valid prepared queue :=
    (representation.valid.tick "heap_comparisons").write layout.keys vertex key
  have indexed := decreased_indexed heap queue layout representation.valid representation.indexed vertex key
  have bound := (representation.indexed.backward vertex present).1
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_up_summary prepared queue layout (heap.read layout.positions vertex) valid indexed present bound
  refine ⟨after, decrease_summary heap after queue layout representation.valid vertex key present improves sift,
    ⟨afterValid, representation.nonnegative, afterIndexed, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact repair (decreased_order heap queue layout representation.valid representation.indexed
      representation.ordered vertex key present (Int.le_of_lt improves))
  · intro value
    rw [membership value]
    simp [prepared, decreasedHeap, representation.valid.positionsKeys]
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    by_cases same : value = vertex <;> simp [prepared, decreasedHeap, same]
  · change after.clocks "heap_comparisons" - (heap.clocks "heap_comparisons" + 1) ≤ _ at comparisons
    unfold Heap.cost
    omega
  · exact swaps
  · intro ref notVertices notPositions notKeys index
    rw [unchanged ref notVertices notPositions index]
    simp [prepared, decreasedHeap, notKeys]
  · intro name notComparisons notSwaps
    rw [clocks name notComparisons notSwaps]
    simp [prepared, decreasedHeap, Heap.tick, Heap.write, notComparisons]
  · exact (show OtherStoragePreserved heap prepared from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage

/-- An equal or larger proposed key performs exactly one comparison and keeps
    the same valid queue, all array contents, and all other counters. -/
theorem unchanged_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (notLower : heap.read layout.keys vertex ≤ key) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key)
      (heap.tick "heap_comparisons") () ∧
      QueueRep (heap.tick "heap_comparisons") queue layout ∧
      Heap.cost heap (heap.tick "heap_comparisons") = Clocks.single "heap_comparisons" 1 := by
  refine ⟨push_unchanged_summary heap queue layout representation.valid vertex key present notLower,
    ⟨representation.valid.tick "heap_comparisons", representation.nonnegative,
      representation.indexed, representation.ordered⟩, ?_⟩
  rw [← Heap.charge_single]
  exact Heap.cost_charge heap _

/-- During sift-down, only edges leaving the moving position may be unordered.
    Its parent is below its children, so promoting the smaller child is safe. -/
structure DownInvariant (priority : Seq) (size index : Int) : Prop where
  orderedExcept : ∀ child, 0 < child → child < size → parent child ≠ index →
    priority (parent child) ≤ priority child
  parentBelowChildren : ∀ child, 0 < child → child < size → parent child = index →
    0 < index → priority (parent index) ≤ priority child

/-- Once the moving entry is below both children (including a leaf), the
    entire active prefix is a heap. -/
theorem DownInvariant.finish {priority : Seq} {size index : Int}
    (invariant : DownInvariant priority size index)
    (orderedChildren : ∀ child, 0 < child → child < size → parent child = index →
      priority index ≤ priority child) :
    Ordered priority size := by
  intro child positive bound
  by_cases fromIndex : parent child = index
  · simpa [fromIndex] using orderedChildren child positive bound fromIndex
  · exact invariant.orderedExcept child positive bound fromIndex

/-- A smaller minimum child can be promoted, moving the only possible disorder
    down one level. The sibling edge and all ancestor edges remain ordered. -/
theorem DownInvariant.exchange_minimum {priority : Seq} {size index chosen : Int}
    (invariant : DownInvariant priority size index)
    (chosenPositive : 0 < chosen) (chosenBound : chosen < size)
    (fromIndex : parent chosen = index)
    (smaller : priority chosen < priority index)
    (minimum : ∀ child, 0 < child → child < size → parent child = index →
      priority chosen ≤ priority child) :
    DownInvariant (exchange priority index chosen) size chosen := by
  have indexSmaller : index < chosen := by
    have bounds : parent chosen < chosen := (parent_bounds chosen chosenPositive).2
    omega
  have different : index ≠ chosen := by omega
  constructor
  · intro child positive bound notChosen
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    by_cases atIndex : child = index
    · subst child
      have parentNotIndex : parent index ≠ index := by omega
      have parentNotChosen : parent index ≠ chosen := by omega
      have old := invariant.parentBelowChildren chosen chosenPositive chosenBound fromIndex positive
      simpa [exchange, parentNotIndex, parentNotChosen, different] using old
    · by_cases atChosen : child = chosen
      · subst child
        rw [fromIndex, exchange_left, exchange_right]
        exact Int.le_of_lt smaller
      · by_cases parentIndex : parent child = index
        · have old := minimum child positive bound parentIndex
          simpa [exchange, atIndex, atChosen, parentIndex, different] using old
        · simpa [exchange, atIndex, atChosen, parentIndex, notChosen] using
            invariant.orderedExcept child positive bound parentIndex
  · intro child positive bound parentChosen _
    have bounds : parent child < child := (parent_bounds child positive).2
    have childNotIndex : child ≠ index := by omega
    have childNotChosen : child ≠ chosen := by omega
    have old := invariant.orderedExcept child positive bound (by omega)
    rw [parentChosen] at old
    simpa [exchange, fromIndex, different, childNotIndex, childNotChosen] using old

/-- Replacing the root and shortening an ordered active prefix establishes
    sift-down's precondition. This is the order argument for minimum removal. -/
theorem Ordered.replace_root {priority : Seq} {size shorter key : Int}
    (ordered : Ordered priority size) (shrink : shorter ≤ size) :
    DownInvariant (fun index => if index = 0 then key else priority index) shorter 0 := by
  constructor
  · intro child positive bound parentNotRoot
    have childNotRoot : child ≠ 0 := by omega
    simpa [childNotRoot, parentNotRoot] using ordered child positive (by omega)
  · intro child positive bound fromIndex rootPositive
    omega

/-- Only the active prefix matters when moving between an abstract priority
    function and its concrete heap-array representation. -/
theorem DownInvariant.congr {first second : Seq} {size index : Int}
    (invariant : DownInvariant first size index) (within : index < size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    DownInvariant second size index := by
  constructor
  · intro child positive bound different
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
    exact invariant.orderedExcept child positive bound different
  · intro child positive bound fromIndex indexPositive
    have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index indexPositive
    rw [← same child (by omega) bound, ← same (parent index) bounds.1 (by omega)]
    exact invariant.parentBelowChildren child positive bound fromIndex indexPositive

/-- Binary-tree parents give exactly the source's two child positions. -/
theorem parent_children (index child : Int) :
    parent child = index ↔ child = 2 * index + 1 ∨ child = 2 * index + 2 := by
  unfold parent
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

-- Sift-down first selects the smaller child, then compares it with the parent.
def selectedChild (heap : Heap) (layout : Layout) (index : Int) : Int :=
  if 2 * index + 2 < layout.size ∧
      heap.read layout.keys (heap.read layout.vertices (2 * index + 2)) <
      heap.read layout.keys (heap.read layout.vertices (2 * index + 1))
  then 2 * index + 2 else 2 * index + 1

def selectionComparisons (layout : Layout) (index : Int) : Nat :=
  if 2 * index + 2 < layout.size then 1 else 0

def AtSiftDown (state : Configuration) (queue : Ref_MinHeap) (index : Int) : Prop :=
  MinHeap.sift_down.At.down_loop state ∧
    MinHeap.sift_down.Local.self state = some queue ∧
    MinHeap.sift_down.Local.i state = some index

def AtChildComparison (state : Configuration) (queue : Ref_MinHeap) (index child : Int) : Prop :=
  MinHeap.sift_down.At.compare_child state ∧
    MinHeap.sift_down.Local.self state = some queue ∧
    MinHeap.sift_down.Local.i state = some index ∧
    MinHeap.sift_down.Local.child state = some child

theorem sift_down_stop (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (location : AtSiftDown state queue index)
    (valid : layout.Valid state.heap queue) (leaf : layout.size ≤ 2 * index + 1) :
    MinHeap.sift_down.CallFrom state state.heap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_down.At.down_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [valid.readSize]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc3_false _ _ _
      (by simp [valid.readSize]; omega))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc2 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_down_pc1 _ _ _)

theorem sift_down_select (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (finalHeap : Heap) (location : AtSiftDown state queue index)
    (valid : layout.Valid state.heap queue) (hasChild : 2 * index + 1 < layout.size)
    (remaining : ∀ nextState,
      AtChildComparison nextState queue index (selectedChild state.heap layout index) →
      nextState.heap = state.heap.tick "heap_comparisons" (selectionComparisons layout index) →
      MinHeap.sift_down.CallFrom nextState finalHeap ()) :
    MinHeap.sift_down.CallFrom state finalHeap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_down.At.down_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [valid.readSize]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc3_true _ _ _ (by simp [valid.readSize, hasChild]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc23 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc22 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc21 _ _ _ (by simp [valid.readSize]))
    by_cases rightPresent : 2 * s.v1 + 2 < layout.size
    · apply Reaches.prepend (Step.MinHeap_sift_down_pc20_true _ _ _
        (by simp [valid.readSize]; omega))
      apply Reaches.prepend (Step.MinHeap_sift_down_pc19 _ _ _)
      apply Reaches.prepend (Step.MinHeap_sift_down_pc18 _ _ _
        (by simp [valid.readKeys, valid.readVertices, valid.keysAllocated, valid.verticesAllocated]))
      by_cases rightSmaller : heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
          heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))
      · apply Reaches.prepend (Step.MinHeap_sift_down_pc17_true _ _ _
          (by simpa [valid.readKeys, valid.readVertices, Int.add_assoc] using rightSmaller))
        apply Reaches.prepend (Step.MinHeap_sift_down_pc16 _ _ _)
        let nextState : Configuration := .active (heap.tick "heap_comparisons")
          (.fn_MinHeap_sift_down 15 { s with
            v2 := 2 * s.v1 + 2
            v3 := 2 * s.v1 + 2
            t5 := decide (2 * s.v1 + 1 < layout.size)
            t12 := decide (2 * s.v1 + 2 < layout.size)
            t13 := decide (heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
              heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))) }) originalStack
        have finish := remaining nextState
          (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
            MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
            selectedChild, rightPresent, rightSmaller, Config.heap])
          (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
        simpa [nextState, valid.readSize, valid.readKeys, valid.readVertices, Int.add_assoc] using finish stack
      · apply Reaches.prepend (Step.MinHeap_sift_down_pc17_false _ _ _
          (by simpa [valid.readKeys, valid.readVertices, Int.add_assoc] using rightSmaller))
        let nextState : Configuration := .active (heap.tick "heap_comparisons")
          (.fn_MinHeap_sift_down 15 { s with
            v2 := 2 * s.v1 + 1
            v3 := 2 * s.v1 + 2
            t5 := decide (2 * s.v1 + 1 < layout.size)
            t12 := decide (2 * s.v1 + 2 < layout.size)
            t13 := decide (heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
              heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))) }) originalStack
        have finish := remaining nextState
          (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
            MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
            selectedChild, rightPresent, rightSmaller, Config.heap])
          (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
        simpa [nextState, valid.readSize, valid.readKeys, valid.readVertices, Int.add_assoc] using finish stack
    · apply Reaches.prepend (Step.MinHeap_sift_down_pc20_false _ _ _
        (by simp [valid.readSize]; omega))
      let nextState : Configuration := .active heap
        (.fn_MinHeap_sift_down 15 { s with
          v2 := 2 * s.v1 + 1
          v3 := 2 * s.v1 + 2
          t5 := decide (2 * s.v1 + 1 < layout.size)
          t12 := decide (2 * s.v1 + 2 < layout.size) }) originalStack
      have finish := remaining nextState
        (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
          MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
          selectedChild, rightPresent, Config.heap])
        (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
      simpa [nextState, valid.readSize, Int.add_assoc] using finish stack

theorem sift_down_ordered (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index child : Int) (location : AtChildComparison state queue index child)
    (valid : layout.Valid state.heap queue)
    (ordered : state.heap.read layout.keys (state.heap.read layout.vertices index) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices child)) :
    MinHeap.sift_down.CallFrom state (state.heap.tick "heap_comparisons") () := by
  rcases location with ⟨atCompare, readSelf, readIndex, readChild⟩
  cases state with
  | done => cases atCompare
  | active heap frame originalStack =>
    cases frame <;> try { cases atCompare }
    rename_i pc s
    have counter : pc = 15 := by
      unfold MinHeap.sift_down.At.compare_child at atCompare
      split at atCompare <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i,
      MinHeap.sift_down.Local.child] at readSelf readIndex readChild
    cases readSelf
    cases readIndex
    cases readChild
    change layout.Valid heap s.v0 at valid
    change heap.read layout.keys (heap.read layout.vertices s.v1) ≤
      heap.read layout.keys (heap.read layout.vertices s.v2) at ordered
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc13_true _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using ordered))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc12 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_down_pc11 _ _ _)

theorem sift_down_continue (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index child : Int) (finalHeap : Heap) (location : AtChildComparison state queue index child)
    (valid : layout.Valid state.heap queue)
    (unordered : ¬ state.heap.read layout.keys (state.heap.read layout.vertices index) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices child))
    (remaining : ∀ nextState, AtSiftDown nextState queue child →
      nextState.heap = swapHeap (state.heap.tick "heap_comparisons") layout index child →
      MinHeap.sift_down.CallFrom nextState finalHeap ()) :
    MinHeap.sift_down.CallFrom state finalHeap () := by
  rcases location with ⟨atCompare, readSelf, readIndex, readChild⟩
  cases state with
  | done => cases atCompare
  | active heap frame originalStack =>
    cases frame <;> try { cases atCompare }
    rename_i pc s
    have counter : pc = 15 := by
      unfold MinHeap.sift_down.At.compare_child at atCompare
      split at atCompare <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i,
      MinHeap.sift_down.Local.child] at readSelf readIndex readChild
    cases readSelf
    cases readIndex
    cases readChild
    change layout.Valid heap s.v0 at valid
    change ¬ heap.read layout.keys (heap.read layout.vertices s.v1) ≤
      heap.read layout.keys (heap.read layout.vertices s.v2) at unordered
    let nextState : Configuration := .active
      (swapHeap (heap.tick "heap_comparisons") layout s.v1 s.v2)
      (.fn_MinHeap_sift_down 4 { s with
        v1 := s.v2
        t6 := ()
        t7 := s.v0
        t8 := s.v1
        t9 := s.v2
        t10 := decide (heap.read layout.keys (heap.read layout.vertices s.v1) ≤
          heap.read layout.keys (heap.read layout.vertices s.v2)) }) originalStack
    have finish := remaining nextState ⟨True.intro, rfl, rfl⟩ rfl
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc13_false _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using unordered))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc10 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc9 _ _ _ valid.object)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc8 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc7 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc6 _ _ _)
    apply Reaches.trans ((swap_summary (heap.tick "heap_comparisons") s.v0 layout
      (valid.tick "heap_comparisons") s.v1 s.v2).2 _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc5 _ _ _)
    simpa only [keys_tick, vertices_tick, valid.readKeys, valid.readVertices,
      Option.getD_some, Heap.read_tick] using finish stack

theorem selectedChild_bounds (heap : Heap) (layout : Layout) (index : Int)
    (nonnegative : 0 ≤ index) (hasChild : 2 * index + 1 < layout.size) :
    0 < selectedChild heap layout index ∧ selectedChild heap layout index < layout.size ∧
      parent (selectedChild heap layout index) = index := by
  unfold selectedChild
  split
  · rename_i chosen
    refine ⟨by omega, chosen.1, ?_⟩
    rw [parent_children]
    exact Or.inr rfl
  · refine ⟨by omega, hasChild, ?_⟩
    rw [parent_children]
    exact Or.inl rfl

theorem selectedChild_minimum (heap : Heap) (layout : Layout) (index child : Int)
    (childBound : child < layout.size) (childOf : parent child = index) :
    heap.read layout.keys (heap.read layout.vertices (selectedChild heap layout index)) ≤
      heap.read layout.keys (heap.read layout.vertices child) := by
  have options := (parent_children index child).mp childOf
  rcases options with rfl | rfl <;> unfold selectedChild <;> split <;> rename_i selected
  · exact Int.le_of_lt selected.2
  · exact Int.le_refl _
  · exact Int.le_refl _
  · have notSmaller : ¬ heap.read layout.keys (heap.read layout.vertices (2 * index + 2)) <
        heap.read layout.keys (heap.read layout.vertices (2 * index + 1)) := by
      intro smaller
      exact selected ⟨childBound, smaller⟩
    omega

theorem depth_mono {first second : Int} (ordered : first ≤ second) : depth first ≤ depth second := by
  unfold depth
  apply (Nat.le_log2 (by omega)).2
  exact Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)

theorem selectedChild_depth (heap : Heap) (layout : Layout) (index : Int)
    (nonnegative : 0 ≤ index) :
    depth (selectedChild heap layout index) = depth index + 1 := by
  apply child_depth index _ nonnegative
  unfold selectedChild
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem selectionComparisons_bound (layout : Layout) (index : Int) :
    selectionComparisons layout index ≤ 1 := by
  unfold selectionComparisons
  split <;> decide

-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.
theorem sift_down_loop (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after,
      (∀ state, AtSiftDown state queue index → state.heap = heap →
        MinHeap.sift_down.CallFrom state after ()) ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      after.clocks "heap_comparisons" ≤ heap.clocks "heap_comparisons" +
        2 * (depth (layout.size - 1) - depth index) ∧
      after.clocks "heap_swaps" ≤ heap.clocks "heap_swaps" +
        (depth (layout.size - 1) - depth index) ∧
      (DownInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  generalize rankEq : depth (layout.size - 1) - depth index = rank
  induction rank using Nat.strongRecOn generalizing heap index with
  | ind rank inductionHypothesis =>
    by_cases hasChild : 2 * index + 1 < layout.size
    · let child := selectedChild heap layout index
      let comparedHeap := (heap.tick "heap_comparisons" (selectionComparisons layout index)).tick "heap_comparisons"
      have childFacts := selectedChild_bounds heap layout index nonnegative hasChild
      have childDepth := selectedChild_depth heap layout index nonnegative
      have depthBound : depth child ≤ depth (layout.size - 1) := depth_mono (by dsimp [child]; omega)
      have selectionBound := selectionComparisons_bound layout index
      have comparedValid : layout.Valid comparedHeap queue :=
        (valid.tick "heap_comparisons" (selectionComparisons layout index)).tick "heap_comparisons"
      by_cases ordered : heap.read layout.keys (heap.read layout.vertices index) ≤
          heap.read layout.keys (heap.read layout.vertices child)
      · refine ⟨comparedHeap, ?_, comparedValid, indexed, ?_, ?_, ?_, ?_, ?_, ?_,
          ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · intro state location sameHeap
          apply sift_down_select state queue layout index comparedHeap location
            (by simpa [sameHeap] using valid) hasChild
          intro compareState compareLocation compareHeap
          have location' : AtChildComparison compareState queue index child := by
            simpa [sameHeap, child] using compareLocation
          have valid' : layout.Valid compareState.heap queue := by
            simpa [compareHeap, sameHeap] using
              valid.tick "heap_comparisons" (selectionComparisons layout index)
          have ordered' : compareState.heap.read layout.keys (compareState.heap.read layout.vertices index) ≤
              compareState.heap.read layout.keys (compareState.heap.read layout.vertices child) := by
            simpa [compareHeap, sameHeap] using ordered
          simpa [comparedHeap, compareHeap, sameHeap] using
            sift_down_ordered compareState queue layout index child location' valid' ordered'
        · simp only [comparedHeap, Heap.clocks_tick_same]
          dsimp [child] at depthBound
          omega
        · simp [comparedHeap, Heap.tick]
        · intro invariant
          apply invariant.finish
          intro descendant _ descendantBound childOf
          exact Int.le_trans ordered (selectedChild_minimum heap layout index descendant descendantBound childOf)
        · intro ref _ _ position
          rfl
        · intro vertex
          rfl
        · intro name notComparisons _
          simp [comparedHeap, Heap.tick, notComparisons]
      · let nextHeap := swapHeap comparedHeap layout index child
        have nextValid : layout.Valid nextHeap queue :=
          swap_preserves_layout comparedHeap queue layout comparedValid index child
        have nextIndexed : Indexed (nextHeap.read layout.vertices)
            (nextHeap.read layout.positions) layout.size :=
          swap_preserves_indexed comparedHeap layout index child valid.verticesPositions indexed
            nonnegative bound (by dsimp [child]; omega) childFacts.2.1
        have smaller : depth (layout.size - 1) - depth child < rank := by
          dsimp [child] at depthBound ⊢
          omega
        obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
            unchanged, membership, otherClocks, storage⟩ :=
          inductionHypothesis (depth (layout.size - 1) - depth child) smaller nextHeap child
            nextValid nextIndexed (by dsimp [child]; omega) childFacts.2.1 rfl
        refine ⟨after, ?_, afterValid, afterIndexed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro state location sameHeap
          apply sift_down_select state queue layout index after location
            (by simpa [sameHeap] using valid) hasChild
          intro compareState compareLocation compareHeap
          apply sift_down_continue compareState queue layout index child after
            (by simpa [sameHeap, child] using compareLocation)
            (by simpa [compareHeap, sameHeap] using
              valid.tick "heap_comparisons" (selectionComparisons layout index))
            (by simpa [compareHeap, sameHeap] using ordered)
          intro nextState nextLocation nextHeapEq
          apply remaining nextState nextLocation
          simpa [nextHeap, comparedHeap, compareHeap, sameHeap] using nextHeapEq
        · simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write] at comparisons
          dsimp [child] at comparisons depthBound
          omega
        · simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write] at swaps
          dsimp [child] at swaps depthBound
          omega
        · intro invariant
          apply repair
          change DownInvariant (fun position => (swapHeap comparedHeap layout index child).read layout.keys
            ((swapHeap comparedHeap layout index child).read layout.vertices position)) layout.size child
          rw [swap_priorities comparedHeap layout index child valid.verticesPositions valid.verticesKeys valid.positionsKeys]
          exact invariant.exchange_minimum childFacts.1 childFacts.2.1 childFacts.2.2
            (by omega) (fun descendant _ descendantBound childOf =>
              selectedChild_minimum heap layout index descendant descendantBound childOf)
        · intro ref notVertices notPositions position
          rw [unchanged ref notVertices notPositions position]
          simp [nextHeap, comparedHeap, swapHeap, Heap.read, Heap.write, notVertices, notPositions]
        · intro vertex
          rw [membership vertex]
          exact swap_preserves_membership comparedHeap layout index child valid.verticesPositions
            indexed nonnegative bound (by dsimp [child]; omega) childFacts.2.1 vertex
        · intro name notComparisons notSwaps
          rw [otherClocks name notComparisons notSwaps]
          simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write, notComparisons, notSwaps]
        · exact (show OtherStoragePreserved heap nextHeap from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage
    · refine ⟨heap, ?_, valid, indexed, Nat.le_add_right _ _, Nat.le_add_right _ _,
        ?_, ?_, ?_, ?_, OtherStoragePreserved.refl heap⟩
      · intro state location sameHeap
        simpa [sameHeap] using sift_down_stop state queue layout index location
          (by simpa [sameHeap] using valid) (by omega)
      · intro invariant
        apply invariant.finish
        intro child _ childBound childOf
        have children := (parent_children index child).mp childOf
        omega
      · intro ref _ _ position
        rfl
      · intro vertex
        rfl
      · intro name _ _
        rfl

-- The public contract allows arbitrary initial priorities. Its conditional
-- repair clause explains when this terminating run also restores heap order.
theorem sift_down_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after, MinHeap.sift_down.Call heap (queue, index) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after "heap_comparisons" ≤ 2 * (depth (layout.size - 1) - depth index) ∧
      Heap.cost heap after "heap_swaps" ≤ depth (layout.size - 1) - depth index ∧
      (DownInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
      unchanged, membership, otherClocks, storage⟩ :=
    sift_down_loop heap queue layout index valid indexed nonnegative bound
  refine ⟨after, ⟨valid.object, ?_⟩, afterValid, afterIndexed, ?_, ?_, repair,
    unchanged, membership, otherClocks, storage⟩
  · exact remaining (MinHeap.sift_down.initial heap (queue, index)) ⟨True.intro, rfl, rfl⟩ rfl
  · unfold Heap.cost
    omega
  · unfold Heap.cost
    omega

/-- The heap after moving the old root to the last position, shrinking the
    active prefix, and marking that old root absent, before any sift-down. -/
def removedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Heap :=
  (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)).write
    layout.positions (heap.read layout.vertices 0) (-1)

theorem removed_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    { layout with size := layout.size - 1 }.Valid (removedHeap heap queue layout) queue := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 (layout.size - 1)
  constructor
  · change is_MinHeap (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue
      (layout.size - 1)) queue
    simpa [is_MinHeap, set_MinHeap_size] using swappedValid.object
  · simp only [removedHeap, vertices_write]
    simpa [field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using swappedValid.readVertices
  · simp only [removedHeap, positions_write]
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  · simp only [removedHeap, keys_write]
    simpa [field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using swappedValid.readKeys
  · simpa [removedHeap] using field_MinHeap_size_set _ _ (layout.size - 1) swappedValid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem removed_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (removedHeap heap queue layout).read layout.vertices index =
      exchange (heap.read layout.vertices) 0 (layout.size - 1) index := by
  have preserved : (removedHeap heap queue layout).read layout.vertices index =
      (swapHeap heap layout 0 (layout.size - 1)).read layout.vertices index := by
    simp [removedHeap, set_MinHeap_size, Heap.read, Heap.write, separate]
  exact preserved.trans (swap_vertices heap layout 0 (layout.size - 1) index separate)

theorem removed_positions (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int) :
    (removedHeap heap queue layout).read layout.positions vertex =
      if vertex = heap.read layout.vertices 0 then -1
      else (swapHeap heap layout 0 (layout.size - 1)).read layout.positions vertex := by
  simp [removedHeap, set_MinHeap_size, Heap.read, Heap.write]

/-- Removing the last entry of an indexed prefix preserves its inverse map.
    This purely mathematical lemma also covers a singleton prefix. -/
theorem Indexed.remove_last (vertices positions : Seq) (size : Int)
    (indexed : Indexed vertices positions size) (nonempty : 0 < size) :
    Indexed vertices (fun vertex => if vertex = vertices (size - 1) then -1 else positions vertex)
      (size - 1) := by
  have lastNonnegative : 0 ≤ size - 1 := by omega
  have lastBound : size - 1 < size := by omega
  constructor
  · intro index nonnegative bound
    have notLast : vertices index ≠ vertices (size - 1) := by
      intro same
      have equal := indexed.distinct nonnegative (by omega) lastNonnegative lastBound same
      omega
    simpa [notLast] using indexed.forward index nonnegative (by omega)
  · intro vertex nonnegative
    have notLast : vertex ≠ vertices (size - 1) := by
      intro same
      simp [same] at nonnegative
    simp only [notLast, ite_false] at nonnegative ⊢
    obtain ⟨bound, identity⟩ := indexed.backward vertex nonnegative
    have different : positions vertex ≠ size - 1 := by
      intro same
      rw [same] at identity
      exact notLast identity.symm
    exact ⟨by omega, identity⟩
  · intro vertex negative
    by_cases same : vertex = vertices (size - 1)
    · simp [same]
    · simp only [same, ite_false] at negative ⊢
      exact indexed.absent vertex negative

/-- Shrinking after the swap removes exactly one entry and preserves all
    inverse-map invariants, before heap order is repaired by sift-down. -/
theorem removed_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonempty : 0 < layout.size) :
    Indexed ((removedHeap heap queue layout).read layout.vertices)
      ((removedHeap heap queue layout).read layout.positions) (layout.size - 1) := by
  let swapped := swapHeap heap layout 0 (layout.size - 1)
  have swappedIndexed : Indexed (swapped.read layout.vertices) (swapped.read layout.positions)
      layout.size :=
    swap_preserves_indexed heap layout 0 (layout.size - 1) valid.verticesPositions indexed
      (by omega) nonempty (by omega) (by omega)
  have last : swapped.read layout.vertices (layout.size - 1) = heap.read layout.vertices 0 := by
    simp [swapped, swap_vertices heap layout 0 (layout.size - 1) _ valid.verticesPositions]
  have vertices : (removedHeap heap queue layout).read layout.vertices =
      swapped.read layout.vertices := by
    funext index
    rw [removed_vertices heap queue layout index valid.verticesPositions]
    exact (swap_vertices heap layout 0 (layout.size - 1) index valid.verticesPositions).symm
  have positions : (removedHeap heap queue layout).read layout.positions =
      fun vertex => if vertex = swapped.read layout.vertices (layout.size - 1) then -1
        else swapped.read layout.positions vertex := by
    funext vertex
    rw [removed_positions, last]
  rw [vertices, positions]
  exact swappedIndexed.remove_last _ _ _ nonempty

/-- Membership after removal is old membership excluding the old root. -/
theorem removed_membership (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonempty : 0 < layout.size) (vertex : Int) :
    0 ≤ (removedHeap heap queue layout).read layout.positions vertex ↔
      0 ≤ heap.read layout.positions vertex ∧ vertex ≠ heap.read layout.vertices 0 := by
  rw [removed_positions]
  by_cases same : vertex = heap.read layout.vertices 0
  · simp [same]
  · simpa [same] using
      swap_preserves_membership heap layout 0 (layout.size - 1) valid.verticesPositions
        indexed (by omega) nonempty (by omega) (by omega) vertex

theorem removed_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (removedHeap heap queue layout).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [removedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm separateVertices, Ne.symm separatePositions]

theorem removed_read_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (ref : SeqRef) (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions)
    (index : Int) :
    (removedHeap heap queue layout).read ref index = heap.read ref index := by
  simp [removedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions]

theorem removed_cost (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) :
    Heap.cost heap (removedHeap heap queue layout) = Clocks.single "heap_swaps" 1 := by
  exact swap_cost heap layout 0 (layout.size - 1)

theorem removed_clocks_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (name : String) (notSwaps : name ≠ "heap_swaps") :
    (removedHeap heap queue layout).clocks name = heap.clocks name := by
  change (heap.tick "heap_swaps").clocks name = heap.clocks name
  exact Heap.clocks_tick_other heap "heap_swaps" name notSwaps

/-- Removing from a queue of at least two vertices composes a single swap and
    the supplied sift-down summary. The returned vertex is the original root. -/
theorem pop_with_sift_summary (heap after : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (multiple : 1 < layout.size)
    (sift : MinHeap.sift_down.Call (removedHeap heap queue layout) (queue, 0) after ()) :
    MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_false _ _ _ (by simp [valid.readSize]; omega))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc17 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc16 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc14 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc12 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc11 _ _ _)
  simp only [valid.readSize, valid.readVertices, Option.getD_some]
  apply Reaches.trans ((swap_summary heap queue layout valid 0 (layout.size - 1)).2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc10 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc9 _ _ _
    (by simpa [swapHeap, set_MinHeap_size, field_MinHeap_positions, is_MinHeap,
      valid.object, valid.readPositions] using!
      show (field_MinHeap_positions heap queue).isSome = true ∧
        (field_MinHeap_positions heap queue).getD 0 < heap.nextRef from
      by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc7_true _ _ _ (by simp; omega))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc5 _ _ _
    (by change is_MinHeap (set_MinHeap_size
          (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)) queue
        simpa [is_MinHeap, set_MinHeap_size] using
          (swap_preserves_layout heap queue layout valid 0 (layout.size - 1)).object))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc3 _ _ _)
  have positions : field_MinHeap_positions
      (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)) queue =
      some layout.positions := by
    simpa [field_MinHeap_positions, set_MinHeap_size, is_MinHeap] using! valid.readPositions
  simp only [positions, Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_pop_min_pc1 _ _ _)

/-- The public representation immediately supplies the root's minimum contract. -/
theorem QueueRep.root_minimum {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (vertex : Int)
    (present : 0 ≤ heap.read layout.positions vertex) :
    heap.read layout.keys (heap.read layout.vertices 0) ≤ heap.read layout.keys vertex :=
  root_minimum_vertex heap layout representation.indexed representation.ordered vertex present

/-- A represented empty queue has no present vertices, including outside the
    graph's vertex range. Its absent-position sentinel is exactly -1. -/
theorem QueueRep.empty_positions {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (empty : layout.size = 0) (vertex : Int) :
    heap.read layout.positions vertex = -1 := by
  apply representation.indexed.absent
  by_cases present : 0 ≤ heap.read layout.positions vertex
  · have bound := (representation.indexed.backward vertex present).1
    omega
  · omega

theorem pop_empty_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (empty : layout.size = 0) :
    MinHeap.pop_min.Call heap queue heap (-1) ∧
      (∀ vertex, heap.read layout.positions vertex = -1) ∧
      Heap.cost heap heap = (fun _ => 0) := by
  refine ⟨pop_empty_summary heap queue layout.size representation.valid.object
    representation.valid.readSize (by omega), representation.empty_positions empty, ?_⟩
  funext name
  simp [Heap.cost]

/-- On the shortened active prefix, root removal replaces only the root's
    priority. Existing descendants retain their old ordering. -/
theorem removed_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (multiple : 1 < layout.size) :
    DownInvariant (fun index => (removedHeap heap queue layout).read layout.keys
      ((removedHeap heap queue layout).read layout.vertices index)) (layout.size - 1) 0 := by
  apply (ordered.replace_root (shorter := layout.size - 1)
    (key := heap.read layout.keys (heap.read layout.vertices (layout.size - 1))) (by omega)).congr (by omega)
  intro index nonnegative bound
  rw [removed_keys heap queue layout _ valid.verticesKeys valid.positionsKeys,
    removed_vertices heap queue layout index valid.verticesPositions]
  have notLast : index ≠ layout.size - 1 := by omega
  have rootNotLast : (0 : Int) ≠ layout.size - 1 := by omega
  by_cases root : index = 0 <;> simp [exchange, root, notLast, rootNotLast]

/-- Minimum extraction's client contract: remove one minimum-priority vertex,
    preserve every other key, restore the queue, and bound the two cost clocks. -/
structure Extracted (before after : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int) : Prop where
  representation : QueueRep after queue { layout with size := layout.size - 1 }
  wasPresent : 0 ≤ before.read layout.positions vertex
  minimum : ∀ value, 0 ≤ before.read layout.positions value →
    before.read layout.keys vertex ≤ before.read layout.keys value
  membership : ∀ value, 0 ≤ after.read layout.positions value ↔
    0 ≤ before.read layout.positions value ∧ value ≠ vertex
  keys : ∀ value, after.read layout.keys value = before.read layout.keys value
  comparisons : Heap.cost before after "heap_comparisons" ≤ 2 * depth (layout.size - 2)
  swaps : Heap.cost before after "heap_swaps" ≤ depth (layout.size - 2) + 1
  otherArrays : ∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions →
    ∀ index, after.read ref index = before.read ref index
  otherClocks : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name
  otherStorage : OtherStoragePreserved (set_MinHeap_size before queue (layout.size - 1)) after

/-- Extracting a singleton needs only its implemented self-swap. -/
theorem pop_singleton_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (singleton : layout.size = 1) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  have nonempty : 0 < layout.size := by omega
  have same : removedHeap heap queue layout = poppedHeap heap queue layout := by
    simp only [removedHeap, singleton, Int.sub_self, poppedHeap]
  refine ⟨removedHeap heap queue layout, ?_, ?_⟩
  · rw [same]
    exact pop_singleton_summary heap queue layout representation.valid singleton
  · constructor
    · refine ⟨removed_layout heap queue layout representation.valid, by simp [singleton],
        removed_indexed heap queue layout representation.valid representation.indexed nonempty, ?_⟩
      intro child positive bound
      change child < layout.size - 1 at bound
      omega
    · rw [representation.indexed.forward 0 (by omega) nonempty]
      omega
    · exact representation.root_minimum
    · exact removed_membership heap queue layout representation.valid representation.indexed nonempty
    · exact fun value => removed_keys heap queue layout value representation.valid.verticesKeys
        representation.valid.positionsKeys
    · rw [removed_cost]
      simp [Clocks.single]
    · rw [removed_cost]
      simp [Clocks.single]
    · exact removed_read_other heap queue layout
    · intro name _ notSwaps
      exact removed_clocks_other heap queue layout name notSwaps
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- For a larger queue, the caller supplies sift-down's proved contract after
    the root/last exchange. The proof never inspects sift-down transitions. -/
theorem pop_multiple_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (multiple : 1 < layout.size) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  let prepared := removedHeap heap queue layout
  let shorter := { layout with size := layout.size - 1 }
  have valid : shorter.Valid prepared queue := removed_layout heap queue layout representation.valid
  have indexed : Indexed (prepared.read layout.vertices) (prepared.read layout.positions) shorter.size :=
    removed_indexed heap queue layout representation.valid representation.indexed (by omega)
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_down_summary prepared queue shorter 0 valid indexed (by omega) (by dsimp [shorter]; omega)
  refine ⟨after, pop_with_sift_summary heap after queue layout representation.valid multiple sift, ?_⟩
  constructor
  · refine ⟨afterValid, by dsimp [shorter]; omega, afterIndexed, ?_⟩
    exact repair (removed_order heap queue layout representation.valid representation.ordered multiple)
  · rw [representation.indexed.forward 0 (by omega) (by omega)]
    omega
  · exact representation.root_minimum
  · intro value
    rw [membership value]
    exact removed_membership heap queue layout representation.valid representation.indexed (by omega) value
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    exact removed_keys heap queue layout value representation.valid.verticesKeys representation.valid.positionsKeys
  · simpa [Heap.cost, prepared, removedHeap, swapHeap, Heap.tick, Heap.write,
      set_MinHeap_size, shorter, depth, Int.sub_sub] using! comparisons
  · have bound : after.clocks "heap_swaps" - (heap.clocks "heap_swaps" + 1) ≤
        depth (layout.size - 2) := by
      simpa [Heap.cost, prepared, removedHeap, swapHeap, Heap.tick, Heap.write,
        set_MinHeap_size, shorter, depth, Int.sub_sub] using! swaps
    unfold Heap.cost
    omega
  · intro ref notVertices notPositions index
    rw [unchanged ref notVertices notPositions index]
    exact removed_read_other heap queue layout ref notVertices notPositions index
  · intro name notComparisons notSwaps
    rw [clocks name notComparisons notSwaps]
    exact removed_clocks_other heap queue layout name notSwaps
  · exact (show OtherStoragePreserved (set_MinHeap_size heap queue (layout.size - 1)) prepared
      from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage

/-- Every nonempty represented queue has a terminating minimum extraction with
    logarithmic operation costs and a reusable heap-level postcondition. -/
theorem pop_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (nonempty : 0 < layout.size) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  by_cases multiple : 1 < layout.size
  · exact pop_multiple_correct heap queue layout representation multiple
  · exact pop_singleton_correct heap queue layout representation (by omega)

/-- Ordinary output users can state minimum correctness and costs without
    mentioning the internal root position or the final heap. -/
theorem pop_minimum_output (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (nonempty : 0 < layout.size) :
    ∃ vertex costs, MinHeap.pop_min.ReturnsWithCost (heap, queue) vertex costs ∧
      0 ≤ heap.read layout.positions vertex ∧
      (∀ value, 0 ≤ heap.read layout.positions value →
        heap.read layout.keys vertex ≤ heap.read layout.keys value) ∧
      costs "heap_comparisons" ≤ 2 * depth (layout.size - 2) ∧
      costs "heap_swaps" ≤ depth (layout.size - 2) + 1 := by
  obtain ⟨after, run, effect⟩ := pop_correct heap queue layout representation nonempty
  exact ⟨heap.read layout.vertices 0, Heap.cost heap after,
    ⟨after, ⟨run.1, run.2.root⟩, rfl⟩, effect.wasPresent, effect.minimum,
    effect.comparisons, effect.swaps⟩

end Queue

/-- Input builder for a graph with the given size and no edges. The graph's
    public reference is `0`; its adjacency heads all contain `none`. -/
def edgelessGraph (size : Int) : Heap :=
  let heads := seq_Edge_optional.const ({} : Heap) none
  (create_Graph heads.1 size heads.2).1

theorem edgeless_graph_valid (size : Int) : is_Graph (edgelessGraph size) 0 := by
  exact ⟨by change 0 < 1; decide, rfl⟩

theorem edgeless_graph_size (size : Int) : field_Graph_size (edgelessGraph size) 0 = some size := by
  rfl

theorem edgeless_graph_heads (size : Int) : field_Graph_heads (edgelessGraph size) 0 = some 0 := by
  rfl

theorem edgeless_graph_no_edges (size index : Int) :
    seq_Edge_optional.get (edgelessGraph size) 0 index = some none := by
  rfl

def edgelessAllocated (size : Int) : Heap :=
  ((edgelessGraph size).allocate (fun _ => -1)).allocate (fun _ => 0)

def edgelessPrepared (size source : Int) : Heap :=
  (Queue.newHeap (edgelessAllocated size)).write 0 source 0

def edgelessLayout : Queue.Layout := ⟨2, 3, 4, 0⟩

theorem edgeless_prepared_layout (size source : Int) :
    edgelessLayout.Valid (edgelessPrepared size source) 1 := by
  have valid := Queue.new_heap_layout (edgelessAllocated size)
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem edgeless_prepared_positions (size source vertex : Int) :
    (edgelessPrepared size source).read edgelessLayout.positions vertex = -1 := by
  change ((Queue.newHeap (edgelessAllocated size)).write 0 source 0).read 3 vertex = -1
  simp only [Heap.read_write_other_ref _ 3 0 vertex source 0 (by decide)]
  exact Queue.new_heap_positions (edgelessAllocated size) vertex

def edgelessQueued (size source : Int) : Heap :=
  Queue.insertedHeap (edgelessPrepared size source) 1 edgelessLayout source 0

theorem edgeless_insertion_summary (size source : Int) :
    MinHeap.push_or_decrease.Call (edgelessPrepared size source) (1, source, 0)
      (edgelessQueued size source) () := by
  exact Queue.insert_empty_summary _ _ _ (edgeless_prepared_layout size source) rfl source 0
    (by rw [edgeless_prepared_positions]; omega)

theorem edgeless_queued_layout (size source : Int) :
    { edgelessLayout with size := 1 }.Valid (edgelessQueued size source) 1 := by
  exact Queue.inserted_layout _ _ _ (edgeless_prepared_layout size source) source 0

theorem edgeless_queued_vertex (size source : Int) :
    (edgelessQueued size source).read edgelessLayout.vertices 0 = source := by
  exact Queue.inserted_vertex _ _ _ source 0 (by decide)

def edgelessPopped (size source : Int) : Heap :=
  Queue.poppedHeap (edgelessQueued size source) 1 { edgelessLayout with size := 1 }

theorem edgeless_extraction_summary (size source : Int) :
    MinHeap.pop_min.Call (edgelessQueued size source) 1 (edgelessPopped size source) source := by
  simpa only [edgeless_queued_vertex] using! Queue.pop_singleton_summary _ _ _
    (edgeless_queued_layout size source) rfl

def edgelessFinal (size source : Int) : Heap := settleHeap (edgelessPopped size source) 1 source

theorem edgeless_final_queue_empty (size source : Int) :
    field_MinHeap_size (edgelessFinal size source) 1 = some 0 := by
  exact (Queue.popped_layout _ _ _ (edgeless_queued_layout size source)).readSize

theorem edgeless_final_graph_heads (size source : Int) :
    field_Graph_heads (edgelessFinal size source) 0 = some 0 := by
  rfl

theorem edgeless_final_no_edges (size source vertex : Int) :
    seq_Edge_optional.get (edgelessFinal size source) 0 vertex = some none := by
  rfl

/-- End-to-end execution for every positive graph size and every valid source,
    using the actual adjacency-list and binary-heap implementation. -/
theorem edgeless_summary (size source : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    dijkstra.Call (edgelessGraph size) (0, source) (edgelessFinal size source) 0 := by
  apply initialize_summary (edgelessGraph size) (Queue.newHeap (edgelessAllocated size))
    (edgelessQueued size source) (edgelessFinal size source) 0 1 source size 0
    (edgeless_graph_valid size) (edgeless_graph_size size) sourceNonnegative sourceBound
    (Queue.new_heap_summary (edgelessAllocated size)) (by change 0 < 5; decide)
    (edgeless_insertion_summary size source)
  intro state located
  exact final_extraction_summary state (edgelessQueued size source) (edgelessPopped size source)
    0 0 1 1 source 0 located (edgeless_queued_layout size source).readSize
    (edgeless_extraction_summary size source) (by change 1 < 5; decide) (by change 0 < 5; decide)
    (edgeless_final_queue_empty size source) (edgeless_final_graph_heads size source)
    (edgeless_final_no_edges size source source)

def edgelessDistances (source : Int) : Seq := fun vertex => if vertex = source then 0 else -1

theorem edgeless_final_distances (size source : Int) :
    (edgelessFinal size source).store 0 = edgelessDistances source := by
  funext vertex
  change (if 0 = 0 ∧ vertex = source then (0 : Int) else -1) = _
  simp [edgelessDistances]

def edgelessCosts : Clocks :=
  Clocks.add (Clocks.single "heap_swaps" 1) (Clocks.single "settlements" 1)

theorem edgeless_final_costs (size source : Int) :
    Heap.cost (edgelessGraph size) (edgelessFinal size source) = edgelessCosts := by
  funext name
  change ((if name = "settlements" then
    (if name = "heap_swaps" then 1 else 0) + 1 else
    (if name = "heap_swaps" then 1 else 0)) - 0) = _
  by_cases settlement : name = "settlements" <;> by_cases swap : name = "heap_swaps" <;>
    simp [edgelessCosts, Clocks.add, Clocks.single, settlement, swap]

/-- Exactly one vertex is settled, no edge is scanned, and singleton extraction
    performs exactly one heap swap. All other named costs are zero. -/
theorem edgeless_output_with_cost (size source : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    dijkstra.ReturnsWithCost (edgelessGraph size, 0, source)
      (edgelessDistances source) edgelessCosts := by
  have summary := edgeless_summary size source sourceNonnegative sourceBound
  exact ⟨edgelessFinal size source, 0, ⟨summary.1, summary.2.root⟩,
    edgeless_final_distances size source, edgeless_final_costs size source⟩

theorem edgeless_output (size source : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    dijkstra.Returns (edgelessGraph size, 0, source) (edgelessDistances source) :=
  (edgeless_output_with_cost size source sourceNonnegative sourceBound).returns

/-- The graph-theoretic meaning of the edgeless output: only the source has a
    route, consisting of zero edges and having total cost zero. -/
theorem edgeless_path_iff (source vertex cost : Int) :
    Path (fun _ _ _ => False) source vertex cost ↔ vertex = source ∧ cost = 0 := by
  constructor
  · intro path
    cases path with
    | empty => exact ⟨rfl, rfl⟩
    | extend _ impossible => contradiction
  · rintro ⟨rfl, rfl⟩
    exact Path.empty

theorem edgeless_source_shortest (source : Int) :
    IsShortest (fun _ _ _ => False) source source (edgelessDistances source source) := by
  refine ⟨by simpa [edgelessDistances] using (Path.empty (edge := fun _ _ _ => False) (source := source)), ?_⟩
  intro cost path
  have empty := (edgeless_path_iff source source cost).1 path
  simp [edgelessDistances, empty.2]

theorem edgeless_others_unreachable (source vertex : Int) (different : vertex ≠ source) :
    edgelessDistances source vertex = -1 ∧ ∀ cost, ¬ Path (fun _ _ _ => False) source vertex cost := by
  refine ⟨by simp [edgelessDistances, different], ?_⟩
  intro cost path
  exact different ((edgeless_path_iff source vertex cost).1 path).1

/-- Compiled output, exact runtime, attained shortest source distance, and
    unreachable remaining vertices all refer to the same edgeless family. -/
theorem edgeless_correct (size source : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    dijkstra.ReturnsWithCost (edgelessGraph size, 0, source)
      (edgelessDistances source) edgelessCosts ∧
    IsShortest (fun _ _ _ => False) source source (edgelessDistances source source) ∧
    ∀ vertex, vertex ≠ source → edgelessDistances source vertex = -1 ∧
      ∀ cost, ¬ Path (fun _ _ _ => False) source vertex cost := by
  exact ⟨edgeless_output_with_cost size source sourceNonnegative sourceBound,
    edgeless_source_shortest source, fun vertex different => edgeless_others_unreachable source vertex different⟩

/-! A finite adjacency-list representation and the checked graph builder. -/

/-- A finite linked list of edges, with bounded endpoints and nonnegative
    weights. The inductive list rules out an infinite or cyclic next chain. -/
abbrev AdjacencyChain := @GraphAnalysis.AdjacencyChain
abbrev AdjacencyChain.empty := @GraphAnalysis.AdjacencyChain.empty
abbrev AdjacencyChain.cons := @GraphAnalysis.AdjacencyChain.cons


/-- The public graph fields represent one finite adjacency list per vertex.
    Parallel edges, zero weights, self-loops, and shared suffixes are allowed. -/
abbrev GraphRep := @GraphAnalysis.GraphRep

theorem AdjacencyChain.head_valid {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges) :
    ∀ ref ∈ head, is_Edge heap ref := by
  apply GraphAnalysis.AdjacencyChain.head_valid <;> assumption


/-- The generated input-data helper also describes the executed constructor's
    exact effect; the proof follows the three field assignments once. -/
theorem edge_constructor_summary (heap : Heap) (target weight : Int) (next : Option Ref_Edge)
    (nextValid : ∀ ref ∈ next, is_Edge heap ref) :
    Edge.Call heap (target, weight, next) (create_Edge heap target weight next).1
      (create_Edge heap target weight next).2 := by
  exact GraphIntoDijkstra.summary_Edge
    (GraphAnalysis.edge_constructor_summary heap target weight next nextValid)

theorem create_edge_preserves_fields (heap : Heap) (target weight : Int) (next : Option Ref_Edge)
    (ref : ObjectRef) (old : ref < heap.nextObject) :
    (create_Edge heap target weight next).1.objectClass ref = heap.objectClass ref ∧
    ∀ field, (create_Edge heap target weight next).1.readField ref field = heap.readField ref field := by
  apply GraphAnalysis.create_edge_preserves_fields <;> assumption

theorem create_edge_preserves_graph (heap : Heap) (target weight : Int) (next : Option Ref_Edge)
    (graph : Ref_Graph) (valid : is_Graph heap graph) :
    is_Graph (create_Edge heap target weight next).1 graph ∧
    field_Graph_size (create_Edge heap target weight next).1 graph = field_Graph_size heap graph ∧
    field_Graph_heads (create_Edge heap target weight next).1 graph = field_Graph_heads heap graph := by
  apply GraphAnalysis.create_edge_preserves_graph <;> assumption

def addedEdgeHeap (heap : Heap) (heads : CollectionRef) (source target weight : Int)
    (next : Option Ref_Edge) : Heap :=
  let edge := create_Edge heap target weight next
  seq_Edge_optional.set edge.1 heads source (some edge.2)


/-- Valid insertion prepends one fresh edge; the exact summary is reusable by
    graph-building callers without inspecting constructor transitions. -/
theorem add_edge_summary (heap : Heap) (graph : Ref_Graph) (size : Int) (heads : CollectionRef)
    (source target weight : Int) (next : Option Ref_Edge)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (readHeads : field_Graph_heads heap graph = some heads)
    (headsValid : seq_Edge_optional.valid heap heads)
    (readNext : seq_Edge_optional.get heap heads source = some next)
    (nextValid : ∀ ref ∈ next, is_Edge heap ref)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (targetNonnegative : 0 ≤ target) (targetBound : target < size)
    (weightNonnegative : 0 ≤ weight) :
    Graph.add_edge.Call heap (graph, source, target, weight)
      (addedEdgeHeap heap heads source target weight next) true := by
  exact GraphIntoDijkstra.summary_Graph_add_edge
    (GraphAnalysis.add_edge_summary heap graph size heads source target weight next valid readSize
      readHeads headsValid readNext nextValid sourceNonnegative sourceBound targetNonnegative targetBound weightNonnegative)


/-- Existing edge identities and all three observable fields are preserved. -/
def EdgeFieldsUnchanged (before after : Heap) : Prop :=
  ∀ ref, is_Edge before ref → is_Edge after ref ∧
    field_Edge_target after ref = field_Edge_target before ref ∧
    field_Edge_weight after ref = field_Edge_weight before ref ∧
    field_Edge_next after ref = field_Edge_next before ref

theorem create_edge_preserves_edges (heap : Heap) (target weight : Int) (next : Option Ref_Edge) :
    EdgeFieldsUnchanged heap (create_Edge heap target weight next).1 := by
  apply GraphAnalysis.create_edge_preserves_edges <;> assumption

theorem added_edge_preserves_edges (heap : Heap) (heads : CollectionRef) (source target weight : Int)
    (next : Option Ref_Edge) :
    EdgeFieldsUnchanged heap (addedEdgeHeap heap heads source target weight next) := by
  apply GraphAnalysis.added_edge_preserves_edges <;> assumption

theorem AdjacencyChain.preserved {before after : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain before size head edges)
    (unchanged : EdgeFieldsUnchanged before after) : AdjacencyChain after size head edges := by
  apply GraphAnalysis.AdjacencyChain.preserved <;> assumption

theorem created_edge_fields (heap : Heap) (target weight : Int) (next : Option Ref_Edge) :
    is_Edge (create_Edge heap target weight next).1 heap.nextObject ∧
    field_Edge_target (create_Edge heap target weight next).1 heap.nextObject = some target ∧
    field_Edge_weight (create_Edge heap target weight next).1 heap.nextObject = some weight ∧
    field_Edge_next (create_Edge heap target weight next).1 heap.nextObject = some next := by
  apply GraphAnalysis.created_edge_fields <;> assumption

def prependEdge (adjacency : Adjacency) (source target weight : Int) : Adjacency :=
  fun vertex => if vertex = source then (target, weight) :: adjacency vertex else adjacency vertex


/-- Inserting an edge preserves finite adjacency chains and exactly prepends
    the new mathematical edge at its source. No other list is changed. -/
theorem add_edge_preserves_representation (heap : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (source target weight : Int)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (targetNonnegative : 0 ≤ target) (targetBound : target < size)
    (weightNonnegative : 0 ≤ weight) :
    ∃ after, Graph.add_edge.Call heap (graph, source, target, weight) after true ∧
      GraphRep after graph size heads (prependEdge adjacency source target weight) ∧
      Heap.cost heap after = (fun _ => 0) := by
  obtain ⟨after, execution, representation, cost⟩ := GraphAnalysis.add_edge_preserves_representation
    heap graph size heads adjacency source target weight representation sourceNonnegative sourceBound
    targetNonnegative targetBound weightNonnegative
  exact ⟨after, GraphIntoDijkstra.summary_Graph_add_edge execution, representation, cost⟩

theorem edgeless_representation (size : Int) (nonnegative : 0 ≤ size) :
    GraphRep (edgelessGraph size) 0 size 0 (fun _ => []) := by
  refine ⟨edgeless_graph_valid size, nonnegative, edgeless_graph_size size,
    edgeless_graph_heads size, ?_, ?_⟩
  · change 0 < 1 ∧ some "Edge?" = some "Edge?"
    decide
  · intro vertex _ _
    exact ⟨none, edgeless_graph_no_edges size vertex, .empty⟩

theorem AdjacencyChain.member_valid {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges)
    (target weight : Int) (member : (target, weight) ∈ edges) :
    0 ≤ target ∧ target < size ∧ 0 ≤ weight := by
  apply GraphAnalysis.AdjacencyChain.member_valid <;> assumption

theorem GraphRep.nonnegative_edges {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) :
    NonnegativeEdges (representedEdges size adjacency) := by
  apply GraphAnalysis.GraphRep.nonnegative_edges <;> assumption

theorem GraphRep.edge_endpoints {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency)
    (source target weight : Int) (connection : representedEdges size adjacency source target weight) :
    0 ≤ source ∧ source < size ∧ 0 ≤ target ∧ target < size := by
  apply GraphAnalysis.GraphRep.edge_endpoints <;> assumption


/-- Rejected endpoints and negative weights return `false` without allocating
    an edge, modifying the adjacency lists, or changing a clock. -/
theorem add_invalid_edge_summary (heap : Heap) (graph : Ref_Graph) (size source target weight : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source ∨ target < 0 ∨ size ≤ target ∨ weight < 0) :
    Graph.add_edge.Call heap (graph, source, target, weight) heap false := by
  exact GraphIntoDijkstra.summary_Graph_add_edge
    (GraphAnalysis.add_invalid_edge_summary heap graph size source target weight valid readSize invalid)

theorem add_invalid_edge_output_with_cost (heap : Heap) (graph : Ref_Graph)
    (size source target weight : Int) (valid : is_Graph heap graph)
    (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source ∨ target < 0 ∨ size ≤ target ∨ weight < 0) :
    Graph.add_edge.ReturnsWithCost (heap, graph, source, target, weight) false (fun _ => 0) := by
  have summary := add_invalid_edge_summary heap graph size source target weight valid readSize invalid
  exact ⟨heap, ⟨summary.1, summary.2.root⟩, by funext name; simp [Heap.cost, Graph.add_edge.load]⟩

/-! The graph constructor normalizes its size and preserves caller storage. -/

def sizedGraphHeap (heap : Heap) (graph : Ref_Graph) (size : Int) : Heap :=
  let sized := set_Graph_size heap graph size
  if size < 0 then set_Graph_size sized graph 0 else sized

def initializedGraphHeap (heap : Heap) (graph : Ref_Graph) (size : Int) : Heap :=
  let sized := sizedGraphHeap heap graph size
  let heads := seq_Edge_optional.const sized none
  set_Graph_heads heads.1 graph heads.2

def newGraphHeap (heap : Heap) (size : Int) : Heap :=
  initializedGraphHeap (heap.allocateObject "Graph") heap.nextObject size

@[simp] theorem optional_edges_class (heap : Heap) (ref : ObjectRef) :
    (seq_Edge_optional.const heap none).1.objectClass ref = heap.objectClass ref := by
  apply GraphAnalysis.optional_edges_class <;> assumption

@[simp] theorem optional_edges_field (heap : Heap) (ref : ObjectRef) (field : String) :
    (seq_Edge_optional.const heap none).1.readField ref field = heap.readField ref field := by
  apply GraphAnalysis.optional_edges_field <;> assumption

@[simp] theorem optional_edges_next_object (heap : Heap) :
    (seq_Edge_optional.const heap none).1.nextObject = heap.nextObject := by
  apply GraphAnalysis.optional_edges_next_object <;> assumption

@[simp] theorem sized_graph_next_collection (heap : Heap) (graph : Ref_Graph) (size : Int) :
    (sizedGraphHeap heap graph size).nextCollection = heap.nextCollection := by
  apply GraphAnalysis.sized_graph_next_collection <;> assumption

@[simp] theorem optional_edges_valid_write_field (heap : Heap) (object : ObjectRef)
    (field : String) (value : ObjectValue) (heads : CollectionRef) :
    seq_Edge_optional.valid (heap.writeField object field value) heads ↔ seq_Edge_optional.valid heap heads := by
  apply GraphAnalysis.optional_edges_valid_write_field <;> assumption

@[simp] theorem optional_edges_get_write_field (heap : Heap) (object : ObjectRef)
    (field : String) (value : ObjectValue) (heads : CollectionRef) (index : Int) :
    seq_Edge_optional.get (heap.writeField object field value) heads index =
      seq_Edge_optional.get heap heads index := by
  apply GraphAnalysis.optional_edges_get_write_field <;> assumption

theorem initialized_graph_valid (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) : is_Graph (initializedGraphHeap heap graph size) graph := by
  apply GraphAnalysis.initialized_graph_valid <;> assumption

theorem graph_initialization_summary (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) :
    Graph.__init__.Call heap (graph, size) (initializedGraphHeap heap graph size) () := by
  exact GraphIntoDijkstra.summary_Graph___init__
    (GraphAnalysis.graph_initialization_summary heap graph size valid)

theorem graph_constructor_summary (heap : Heap) (size : Int) :
    Graph.Call heap size (newGraphHeap heap size) heap.nextObject := by
  exact GraphIntoDijkstra.summary_Graph
    (GraphAnalysis.graph_constructor_summary heap size)

theorem initialized_graph_size (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) :
    field_Graph_size (initializedGraphHeap heap graph size) graph = some (max 0 size) := by
  apply GraphAnalysis.initialized_graph_size <;> assumption

theorem initialized_graph_heads (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) :
    field_Graph_heads (initializedGraphHeap heap graph size) graph = some heap.nextCollection := by
  apply GraphAnalysis.initialized_graph_heads <;> assumption

theorem initialized_graph_empty (heap : Heap) (graph : Ref_Graph) (size : Int) :
    seq_Edge_optional.valid (initializedGraphHeap heap graph size) heap.nextCollection ∧
    ∀ vertex, seq_Edge_optional.get (initializedGraphHeap heap graph size) heap.nextCollection vertex = some none := by
  apply GraphAnalysis.initialized_graph_empty <;> assumption

theorem graph_constructor_representation (heap : Heap) (size : Int) :
    GraphRep (newGraphHeap heap size) heap.nextObject (max 0 size) heap.nextCollection (fun _ => []) := by
  apply GraphAnalysis.graph_constructor_representation <;> assumption


/-- Construction allocates one graph and one heads collection. Existing
    integer sequences, objects, collections, and every clock are preserved. -/
theorem graph_constructor_preserves_storage (heap : Heap) (size : Int) :
    (newGraphHeap heap size).store = heap.store ∧
    (∀ ref, ref < heap.nextObject → (newGraphHeap heap size).objects ref = heap.objects ref) ∧
    (∀ ref, ref < heap.nextCollection → (newGraphHeap heap size).collections ref = heap.collections ref) ∧
    (newGraphHeap heap size).clocks = heap.clocks := by
  apply GraphAnalysis.graph_constructor_preserves_storage <;> assumption

theorem graph_constructor_verified (heap : Heap) (size : Int) :
    Graph.Call heap size (newGraphHeap heap size) heap.nextObject ∧
    GraphRep (newGraphHeap heap size) heap.nextObject (max 0 size) heap.nextCollection (fun _ => []) ∧
    Heap.cost heap (newGraphHeap heap size) = (fun _ => 0) := by
  obtain ⟨execution, representation, cost⟩ := GraphAnalysis.graph_constructor_verified heap size
  exact ⟨GraphIntoDijkstra.summary_Graph execution, representation, cost⟩


/-- A frame condition for graph reasoning: only graph fields, adjacency heads,
    and existing edge fields matter. Distances, queue arrays, and clocks may
    change freely when these observations are preserved. -/
abbrev GraphFrame := @GraphAnalysis.GraphFrame

theorem GraphFrame.refl (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef) :
    GraphFrame heap heap graph heads := by
  apply GraphAnalysis.GraphFrame.refl <;> assumption

theorem GraphFrame.trans {first middle last : Heap} {graph : Ref_Graph} {heads : CollectionRef}
    (one : GraphFrame first middle graph heads) (two : GraphFrame middle last graph heads) :
    GraphFrame first last graph heads := by
  apply GraphAnalysis.GraphFrame.trans <;> assumption

theorem GraphRep.preserved {before after : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep before graph size heads adjacency)
    (frame : GraphFrame before after graph heads) : GraphRep after graph size heads adjacency := by
  apply GraphAnalysis.GraphRep.preserved <;> assumption

theorem graph_frame_write (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (ref : SeqRef) (index value : Int) : GraphFrame heap (heap.write ref index value) graph heads := by
  apply GraphAnalysis.graph_frame_write <;> assumption

theorem graph_frame_allocate (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (values : Seq) : GraphFrame heap (heap.allocate values) graph heads := by
  apply GraphAnalysis.graph_frame_allocate <;> assumption

theorem graph_frame_tick (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (clock : String) (amount : Nat) : GraphFrame heap (heap.tick clock amount) graph heads := by
  apply GraphAnalysis.graph_frame_tick <;> assumption


/-- A queue object's fields cannot alias a Graph or Edge object: their class
    tags differ. This is the only separation needed for a queue field write. -/
theorem graph_frame_queue_field (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (queue : Ref_MinHeap) (validQueue : is_MinHeap heap queue) (field : String) (value : ObjectValue) :
    GraphFrame heap (heap.writeField queue field value) graph heads := by
  exact GraphAnalysis.graph_frame_foreign_field heap graph heads queue "MinHeap" validQueue.2
    (by decide) (by decide) field value

theorem graph_frame_queue_swap (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (layout : Queue.Layout) (i j : Int) : GraphFrame heap (Queue.swapHeap heap layout i j) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

theorem graph_frame_queue_insert (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (queue : Ref_MinHeap) (validQueue : is_MinHeap heap queue) (layout : Queue.Layout) (vertex key : Int) :
    GraphFrame heap (Queue.insertedHeap heap queue layout vertex key) graph heads := by
  let arrays := ((heap.write layout.keys vertex key).write layout.vertices 0 vertex).write layout.positions vertex 0
  have first : GraphFrame heap arrays graph heads := by
    exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩
  exact first.trans (graph_frame_queue_field arrays graph heads queue validQueue "size" (.intValue 1))

theorem graph_frame_queue_pop (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (queue : Ref_MinHeap) (validQueue : is_MinHeap heap queue) (layout : Queue.Layout) :
    GraphFrame heap (Queue.poppedHeap heap queue layout) graph heads := by
  have swapped := graph_frame_queue_swap heap graph heads layout 0 0
  have resized := graph_frame_queue_field (Queue.swapHeap heap layout 0 0) graph heads queue validQueue "size" (.intValue 0)
  exact (swapped.trans resized).trans (graph_frame_write _ graph heads layout.positions
    (heap.read layout.vertices 0) (-1))

/-- A nonempty adjacency observation exposes one edge and a strictly shorter
    tail. These are the facts needed for an edge-loop induction. -/
theorem AdjacencyChain.uncons {heap : Heap} {size : Int} {edge : Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size (some edge) edges) :
    ∃ target weight next tail, edges = (target, weight) :: tail ∧
      field_Edge_target heap edge = some target ∧ field_Edge_weight heap edge = some weight ∧
      field_Edge_next heap edge = some next ∧ 0 ≤ target ∧ target < size ∧ 0 ≤ weight ∧
      AdjacencyChain heap size next tail ∧ tail.length < edges.length := by
  apply GraphAnalysis.AdjacencyChain.uncons <;> assumption

theorem AdjacencyChain.empty_iff {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges) :
    head = none ↔ edges = [] := by
  apply GraphAnalysis.AdjacencyChain.empty_iff <;> assumption


/-- An adjacency snapshot determines one mathematical list, despite allowing
    shared tails. Proofs can therefore reuse the same finite-length measure. -/
theorem AdjacencyChain.unique {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {first second : List (Int × Int)} (one : AdjacencyChain heap size head first)
    (two : AdjacencyChain heap size head second) : first = second := by
  apply GraphAnalysis.AdjacencyChain.unique <;> assumption


/-! Local loop contracts for a successful relaxation and the next extraction. -/

def AtEdges (state : Configuration) (heap : Heap) (graph : Ref_Graph)
    (distance settled : SeqRef) (queue : Ref_MinHeap) (vertex : Int) (edge : Option Ref_Edge) : Prop :=
  dijkstra.At.edge_loop state ∧ state.heap = heap ∧
  dijkstra.Local.graph state = some graph ∧ dijkstra.Local.distance state = some distance ∧
  dijkstra.Local.settled state = some settled ∧ dijkstra.Local.queue state = some queue ∧
  dijkstra.Local.vertex state = some vertex ∧ dijkstra.Local.edge state = some edge

theorem extraction_to_edges (state : Configuration) (heap poppedHeap finalHeap : Heap)
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_MinHeap)
    (vertex size : Int) (heads : CollectionRef) (edge : Option Ref_Edge)
    (located : AtExtraction state heap graph distance settled queue)
    (queueSize : field_MinHeap_size heap queue = some size)
    (nonempty : 0 < size)
    (pop : MinHeap.pop_min.Call heap queue poppedHeap vertex)
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
  apply Reaches.prepend (Step.dijkstra_pc27 _ _ _ (by simpa [readQueue] using! pop.1))
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
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_MinHeap) (vertex : Int)
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
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_MinHeap)
    (vertex target weight : Int) (edge : Ref_Edge) (nextEdge : Option Ref_Edge)
    (located : AtEdges state heap graph distance settled queue vertex (some edge))
    (distanceAllocated : distance < heap.nextRef) (settledAllocated : settled < heap.nextRef)
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (unsettled : heap.read settled target = 0)
    (better : heap.read distance target < 0 ∨ heap.read distance vertex + weight < heap.read distance target)
    (insertion : MinHeap.push_or_decrease.Call
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
    (by simpa [relaxationHeap, readQueue] using! insertion.1))
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
    (graph : Ref_Graph) (distance settled : SeqRef) (queue : Ref_MinHeap)
    (located : AtExtraction state heap graph distance settled queue)
    (queueEmpty : field_MinHeap_size heap queue = some 0)
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
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_MinHeap)
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
    (graph : Ref_Graph) (distance settled result : SeqRef) (queue : Ref_MinHeap)
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


/-! A complete one-edge execution family. The queue never exceeds one vertex. -/

def singleEdgeGraph (size source target weight : Int) : Heap :=
  addedEdgeHeap (edgelessGraph size) 0 source target weight none

theorem single_edge_graph_valid (size source target weight : Int) :
    is_Graph (singleEdgeGraph size source target weight) 0 := by
  exact (create_edge_preserves_graph (edgelessGraph size) target weight none 0 (edgeless_graph_valid size)).1

theorem single_edge_graph_size (size source target weight : Int) :
    field_Graph_size (singleEdgeGraph size source target weight) 0 = some size := by
  rfl

theorem single_edge_graph_head (size source target weight : Int) :
    seq_Edge_optional.get (singleEdgeGraph size source target weight) 0 source = some (some 1) := by
  exact seq_Edge_optional.get_set_same _ 0 source (some 1)
    (by change 0 < 1 ∧ some "Edge?" = some "Edge?"; decide)

theorem single_edge_graph_other_head (size source target weight vertex : Int) (different : vertex ≠ source) :
    seq_Edge_optional.get (singleEdgeGraph size source target weight) 0 vertex = some none := by
  unfold singleEdgeGraph addedEdgeHeap
  rw [seq_Edge_optional.get_set_other_index _ 0 vertex source _ different]
  rfl

def singleAllocated (size source target weight : Int) : Heap :=
  ((singleEdgeGraph size source target weight).allocate (fun _ => -1)).allocate (fun _ => 0)

def singlePrepared (size source target weight : Int) : Heap :=
  (Queue.newHeap (singleAllocated size source target weight)).write 0 source 0

def singleQueued (size source target weight : Int) : Heap :=
  Queue.insertedHeap (singlePrepared size source target weight) 2 edgelessLayout source 0

def singlePopped (size source target weight : Int) : Heap :=
  Queue.poppedHeap (singleQueued size source target weight) 2 { edgelessLayout with size := 1 }

def singleAtEdge (size source target weight : Int) : Heap :=
  settleHeap (singlePopped size source target weight) 1 source

def singleRelaxed (size source target weight : Int) : Heap :=
  relaxationHeap (singleAtEdge size source target weight) 0 target weight

def singleRequeued (size source target weight : Int) : Heap :=
  Queue.insertedHeap (singleRelaxed size source target weight) 2 edgelessLayout target weight

def singleImproved (size source target weight : Int) : Heap :=
  (singleRequeued size source target weight).tick "improvements"

def singleFinalPopped (size source target weight : Int) : Heap :=
  Queue.poppedHeap (singleImproved size source target weight) 2 { edgelessLayout with size := 1 }

def singleFinal (size source target weight : Int) : Heap :=
  settleHeap (singleFinalPopped size source target weight) 1 target

theorem single_prepared_layout (size source target weight : Int) :
    edgelessLayout.Valid (singlePrepared size source target weight) 2 := by
  have valid := Queue.new_heap_layout (singleAllocated size source target weight)
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem single_prepared_positions (size source target weight vertex : Int) :
    (singlePrepared size source target weight).read 3 vertex = -1 := by
  change ((Queue.newHeap (singleAllocated size source target weight)).write 0 source 0).read 3 vertex = -1
  simp only [Heap.read_write_other_ref _ 3 0 vertex source 0 (by decide)]
  exact Queue.new_heap_positions (singleAllocated size source target weight) vertex

theorem single_insertion_summary (size source target weight : Int) :
    MinHeap.push_or_decrease.Call (singlePrepared size source target weight) (2, source, 0)
      (singleQueued size source target weight) () := by
  exact Queue.insert_empty_summary _ _ _ (single_prepared_layout size source target weight) rfl source 0
    (by change (singlePrepared size source target weight).read 3 source < 0
        rw [single_prepared_positions]; omega)

theorem single_queued_layout (size source target weight : Int) :
    { edgelessLayout with size := 1 }.Valid (singleQueued size source target weight) 2 := by
  exact Queue.inserted_layout _ _ _ (single_prepared_layout size source target weight) source 0

theorem single_queued_vertex (size source target weight : Int) :
    (singleQueued size source target weight).read 2 0 = source := by
  exact Queue.inserted_vertex _ _ edgelessLayout source 0 (by decide)

theorem single_extraction_summary (size source target weight : Int) :
    MinHeap.pop_min.Call (singleQueued size source target weight) 2
      (singlePopped size source target weight) source := by
  simpa only [edgelessLayout, single_queued_vertex] using! Queue.pop_singleton_summary _ _ _
    (single_queued_layout size source target weight) rfl

theorem single_relaxed_layout (size source target weight : Int) :
    edgelessLayout.Valid (singleRelaxed size source target weight) 2 := by
  have valid := Queue.popped_layout _ _ _ (single_queued_layout size source target weight)
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem single_relaxed_target_absent (size source target weight : Int) (different : target ≠ source) :
    (singleRelaxed size source target weight).read 3 target = -1 := by
  change (if 3 = 0 ∧ target = target then weight else
    if 3 = 1 ∧ target = source then 1 else
    if 3 = 3 ∧ target = source then -1 else
    if 3 = 3 ∧ target = source then 0 else
    if 3 = 3 ∧ target = source then 0 else
    if 3 = 2 ∧ target = 0 then source else
    if 3 = 2 ∧ target = 0 then source else
    if 3 = 3 ∧ target = source then 0 else
    if 3 = 2 ∧ target = 0 then source else
    if 3 = 4 ∧ target = source then 0 else
    if 3 = 0 ∧ target = source then 0 else -1) = -1
  simp [different]

theorem single_reinsertion_summary (size source target weight : Int) (different : target ≠ source) :
    MinHeap.push_or_decrease.Call (singleRelaxed size source target weight) (2, target, weight)
      (singleRequeued size source target weight) () := by
  exact Queue.insert_empty_summary _ _ _ (single_relaxed_layout size source target weight) rfl target weight
    (by change (singleRelaxed size source target weight).read 3 target < 0
        rw [single_relaxed_target_absent size source target weight different]; omega)

theorem single_requeued_layout (size source target weight : Int) :
    { edgelessLayout with size := 1 }.Valid (singleImproved size source target weight) 2 := by
  have valid := Queue.inserted_layout _ _ _ (single_relaxed_layout size source target weight) target weight
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem single_requeued_vertex (size source target weight : Int) :
    (singleImproved size source target weight).read 2 0 = target := by
  exact Queue.inserted_vertex (singleRelaxed size source target weight) 2 edgelessLayout target weight (by decide)

theorem single_final_extraction_summary (size source target weight : Int) :
    MinHeap.pop_min.Call (singleImproved size source target weight) 2
      (singleFinalPopped size source target weight) target := by
  simpa only [edgelessLayout, single_requeued_vertex] using! Queue.pop_singleton_summary _ _ _
    (single_requeued_layout size source target weight) rfl

theorem single_source_distance (size source target weight : Int) :
    (singleAtEdge size source target weight).read 0 source = 0 := by
  change (if 0 = 0 ∧ source = source then (0 : Int) else -1) = 0
  simp

theorem single_target_distance (size source target weight : Int) (different : target ≠ source) :
    (singleAtEdge size source target weight).read 0 target = -1 := by
  change (if 0 = 0 ∧ target = source then (0 : Int) else -1) = -1
  simp [different]

theorem single_target_unsettled (size source target weight : Int) (different : target ≠ source) :
    (singleAtEdge size source target weight).read 1 target = 0 := by
  change (if 1 = 1 ∧ target = source then (1 : Int) else 0) = 0
  simp [different]

theorem single_final_empty (size source target weight : Int) :
    field_MinHeap_size (singleFinal size source target weight) 2 = some 0 := by
  exact (Queue.popped_layout _ _ _ (single_requeued_layout size source target weight)).readSize

/-- Two singleton extractions and one relaxation give a completed call. Each
    queue operation is reused through its checked summary contract. -/
theorem single_edge_summary (size source target weight : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) (different : target ≠ source) :
    dijkstra.Call (singleEdgeGraph size source target weight) (0, source)
      (singleFinal size source target weight) 0 := by
  apply initialize_summary (singleEdgeGraph size source target weight)
    (Queue.newHeap (singleAllocated size source target weight))
    (singleQueued size source target weight) (singleFinal size source target weight)
    0 2 source size 0 (single_edge_graph_valid size source target weight)
    (single_edge_graph_size size source target weight) sourceNonnegative sourceBound
    (Queue.new_heap_summary (singleAllocated size source target weight)) (by change 0 < 5; decide)
    (single_insertion_summary size source target weight)
  intro state located
  apply extraction_to_edges state (singleQueued size source target weight)
    (singlePopped size source target weight) (singleFinal size source target weight)
    0 0 1 0 2 source 1 0 (some 1) located (single_queued_layout size source target weight).readSize
    (by decide) (single_extraction_summary size source target weight) (by change 1 < 5; decide)
    (by rfl) (single_edge_graph_head size source target weight)
  intro atEdge edgeLocated
  apply improve_edge_continue atEdge (singleAtEdge size source target weight)
    (singleRequeued size source target weight) (singleFinal size source target weight)
    0 0 1 0 2 source target weight 1 none edgeLocated
    (by change 0 < 5; decide) (by change 1 < 5; decide) (by rfl) (by rfl)
    (single_target_unsettled size source target weight different)
    (Or.inl (by rw [single_target_distance size source target weight different]; omega))
    (by simpa only [single_source_distance, Int.zero_add] using!
      single_reinsertion_summary size source target weight different)
    (by rfl)
  intro afterEdge emptyLocated
  apply empty_edges_continue afterEdge (singleImproved size source target weight)
    (singleFinal size source target weight) 0 0 1 0 2 source emptyLocated
  intro last located
  exact final_extraction_summary last (singleImproved size source target weight)
    (singleFinalPopped size source target weight) 0 0 1 2 target 0 located
    (single_requeued_layout size source target weight).readSize
    (single_final_extraction_summary size source target weight)
    (by change 1 < 5; decide) (by change 0 < 5; decide)
    (single_final_empty size source target weight) (by rfl)
    (single_edge_graph_other_head size source target weight target different)

def singleEdgeDistances (source target weight : Int) : Seq :=
  fun vertex => if vertex = target then weight else if vertex = source then 0 else -1

def singleEdgeCosts : Clocks :=
  fun name => if name = "settlements" then 2 else if name = "heap_swaps" then 2
    else if name = "edges" then 1 else if name = "improvements" then 1 else 0

theorem single_final_distances (size source target weight : Int) :
    (singleFinal size source target weight).store 0 = singleEdgeDistances source target weight := by
  funext vertex
  change (if 0 = 0 ∧ vertex = target then weight else if 0 = 0 ∧ vertex = source then 0 else -1) = _
  simp [singleEdgeDistances]

theorem single_final_costs (size source target weight : Int) :
    Heap.cost (singleEdgeGraph size source target weight) (singleFinal size source target weight) = singleEdgeCosts := by
  funext name
  let first := (({} : Heap).tick "heap_swaps").tick "settlements"
  let second := ((first.tick "edges").tick "improvements").tick "heap_swaps"
  change (Heap.cost ({} : Heap) (second.tick "settlements")) name = _
  by_cases settlements : name = "settlements"
  · subst name; simp [Heap.cost, Heap.tick, singleEdgeCosts, first, second]
  · by_cases swaps : name = "heap_swaps"
    · subst name; simp [Heap.cost, Heap.tick, singleEdgeCosts, first, second]
    · by_cases edges : name = "edges"
      · subst name; simp [Heap.cost, Heap.tick, singleEdgeCosts, first, second]
      · by_cases improvements : name = "improvements"
        · subst name; simp [Heap.cost, Heap.tick, singleEdgeCosts, first, second]
        · simp [Heap.cost, Heap.tick, singleEdgeCosts, first, second, settlements, swaps, edges, improvements]

theorem single_edge_output_with_cost (size source target weight : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) (different : target ≠ source) :
    dijkstra.ReturnsWithCost (singleEdgeGraph size source target weight, 0, source)
      (singleEdgeDistances source target weight) singleEdgeCosts := by
  have summary := single_edge_summary size source target weight sourceNonnegative sourceBound different
  exact ⟨singleFinal size source target weight, 0, ⟨summary.1, summary.2.root⟩,
    single_final_distances size source target weight, single_final_costs size source target weight⟩

def singleAdjacency (source target weight : Int) : Adjacency :=
  fun vertex => if vertex = source then [(target, weight)] else []

theorem single_edge_representation (size source target weight : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (targetNonnegative : 0 ≤ target) (targetBound : target < size) (weightNonnegative : 0 ≤ weight) :
    GraphRep (singleEdgeGraph size source target weight) 0 size 0 (singleAdjacency source target weight) := by
  refine ⟨single_edge_graph_valid size source target weight, by omega,
    single_edge_graph_size size source target weight, rfl, ?_, ?_⟩
  · exact (seq_Edge_optional.valid_set _ 0 0 source (some 1)).2
      (by change 0 < 1 ∧ some "Edge?" = some "Edge?"; decide)
  · intro vertex nonnegative bound
    by_cases same : vertex = source
    · subst vertex
      refine ⟨some 1, single_edge_graph_head size source target weight, ?_⟩
      obtain ⟨valid, readTarget, readWeight, readNext⟩ := created_edge_fields (edgelessGraph size) target weight none
      simpa [singleAdjacency] using
        AdjacencyChain.cons (heap := singleEdgeGraph size source target weight)
          1 target weight none [] valid readTarget readWeight readNext
          targetNonnegative targetBound weightNonnegative .empty
    · exact ⟨none, single_edge_graph_other_head size source target weight vertex same,
        by simpa [singleAdjacency, same] using (AdjacencyChain.empty
          (heap := singleEdgeGraph size source target weight) (size := size))⟩

def singleEdges (source target weight : Int) : Edges :=
  fun u v w => u = source ∧ v = target ∧ w = weight

theorem single_edge_relation (size source target weight : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    representedEdges size (singleAdjacency source target weight) = singleEdges source target weight := by
  funext u v w
  apply propext
  by_cases same : u = source
  · subst u
    simp [representedEdges, singleAdjacency, singleEdges, sourceNonnegative, sourceBound]
  · simp [representedEdges, singleAdjacency, singleEdges, same]

/-- With distinct endpoints, every route is either empty or traverses the
    sole edge once. This also covers a zero-weight edge. -/
theorem single_edge_path_iff (source target weight vertex cost : Int) (different : target ≠ source) :
    Path (singleEdges source target weight) source vertex cost ↔
      (vertex = source ∧ cost = 0) ∨ (vertex = target ∧ cost = weight) := by
  constructor
  · intro path
    induction path with
    | empty => exact Or.inl ⟨rfl, rfl⟩
    | @extend previous vertex prefixCost edgeWeight route connection ih =>
      rcases connection with ⟨rfl, rfl, rfl⟩
      rcases ih with ⟨_, rfl⟩ | ⟨impossible, _⟩
      · exact Or.inr ⟨rfl, Int.zero_add _⟩
      · exact False.elim (different impossible.symm)
  · intro route
    rcases route with ⟨atSource, zero⟩ | ⟨atTarget, edgeCost⟩
    · rw [atSource, zero]
      exact Path.empty
    · rw [atTarget, edgeCost]
      simpa using Path.extend (Path.empty (edge := singleEdges source target weight) (source := source))
        (show singleEdges source target weight source target weight from ⟨rfl, rfl, rfl⟩)

theorem single_source_shortest (source target weight : Int) (different : target ≠ source) :
    IsShortest (singleEdges source target weight) source source (singleEdgeDistances source target weight source) := by
  have value : singleEdgeDistances source target weight source = 0 := by
    simp [singleEdgeDistances, Ne.symm different]
  rw [value]
  refine ⟨Path.empty, ?_⟩
  intro cost path
  rcases (single_edge_path_iff source target weight source cost different).1 path with ⟨_, rfl⟩ | ⟨same, _⟩
  · omega
  · exact False.elim (different same.symm)

theorem single_target_shortest (source target weight : Int) (different : target ≠ source) :
    IsShortest (singleEdges source target weight) source target (singleEdgeDistances source target weight target) := by
  have value : singleEdgeDistances source target weight target = weight := by simp [singleEdgeDistances]
  rw [value]
  refine ⟨(single_edge_path_iff source target weight target weight different).2 (Or.inr ⟨rfl, rfl⟩), ?_⟩
  intro cost path
  rcases (single_edge_path_iff source target weight target cost different).1 path with ⟨same, _⟩ | ⟨_, rfl⟩
  · exact False.elim (different same)
  · omega

theorem single_others_unreachable (source target weight vertex : Int) (different : target ≠ source)
    (notSource : vertex ≠ source) (notTarget : vertex ≠ target) :
    singleEdgeDistances source target weight vertex = -1 ∧
      ∀ cost, ¬ Path (singleEdges source target weight) source vertex cost := by
  refine ⟨by simp [singleEdgeDistances, notSource, notTarget], ?_⟩
  intro cost path
  rcases (single_edge_path_iff source target weight vertex cost different).1 path with ⟨same, _⟩ | ⟨same, _⟩
  · exact notSource same
  · exact notTarget same

/-- The actual compiled run on a valid one-edge graph has shortest distances
    and exact costs: two settlements, two swaps, one edge, one improvement,
    and zero comparisons. All other vertices remain unreachable. -/
theorem single_edge_correct (size source target weight : Int)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (targetNonnegative : 0 ≤ target) (targetBound : target < size)
    (weightNonnegative : 0 ≤ weight) (different : target ≠ source) :
    GraphRep (singleEdgeGraph size source target weight) 0 size 0 (singleAdjacency source target weight) ∧
    dijkstra.ReturnsWithCost (singleEdgeGraph size source target weight, 0, source)
      (singleEdgeDistances source target weight) singleEdgeCosts ∧
    IsShortest (representedEdges size (singleAdjacency source target weight)) source source
      (singleEdgeDistances source target weight source) ∧
    IsShortest (representedEdges size (singleAdjacency source target weight)) source target
      (singleEdgeDistances source target weight target) ∧
    ∀ vertex, vertex ≠ source → vertex ≠ target → singleEdgeDistances source target weight vertex = -1 ∧
      ∀ cost, ¬ Path (representedEdges size (singleAdjacency source target weight)) source vertex cost := by
  rw [single_edge_relation size source target weight sourceNonnegative sourceBound]
  exact ⟨single_edge_representation size source target weight sourceNonnegative sourceBound
      targetNonnegative targetBound weightNonnegative,
    single_edge_output_with_cost size source target weight sourceNonnegative sourceBound different,
    single_source_shortest source target weight different,
    single_target_shortest source target weight different,
    fun vertex notSource notTarget => single_others_unreachable source target weight vertex different notSource notTarget⟩


/-- Every completed Dijkstra execution, including its constructor and heap
    calls, preserves or increases every clock from its arbitrary initial value. -/
theorem execution_clocks_monotone (heap after : Heap) (graph : Ref_Graph)
    (source : Int) (result : SeqRef)
    (execution : dijkstra.Run heap (graph, source) after result) :
    ∀ name, heap.clocks name ≤ after.clocks name := by
  intro name
  have resumeHeap (h : Heap) (result : Result) (stack : Stack) :
      (resumeConfig h result stack).heap = h := by
    cases stack <;> rfl
  have stepClock (before after : Configuration) (transition : Step before after) :
      before.heap.clocks name ≤ after.heap.clocks name := by
    cases transition <;> first
      | exact Nat.le_refl _
      | exact Heap.clocks_le_tick ..
      | rw [resumeHeap]; exact Nat.le_refl _
  exact execution.2.invariant (fun state => heap.clocks name ≤ state.heap.clocks name)
    (Nat.le_refl _) (fun before after transition bound => Nat.le_trans bound (stepClock before after transition))

/-- Consecutive completed calls have additive costs even when the initial
    counters are nonzero. Monotonicity justifies natural-number subtraction. -/
theorem consecutive_execution_costs (initial middle finalHeap : Heap)
    (firstGraph secondGraph : Ref_Graph) (firstSource secondSource : Int)
    (firstResult secondResult : SeqRef)
    (first : dijkstra.Run initial (firstGraph, firstSource) middle firstResult)
    (second : dijkstra.Run middle (secondGraph, secondSource) finalHeap secondResult) :
    Heap.cost initial finalHeap = Clocks.add (Heap.cost initial middle) (Heap.cost middle finalHeap) := by
  funext name
  exact Heap.cost_add initial middle finalHeap name
    (execution_clocks_monotone initial middle firstGraph firstSource firstResult first name)
    (execution_clocks_monotone middle finalHeap secondGraph secondSource secondResult second name)


/-- Preserving the object and typed-collection stores preserves every graph
    observation, independently of changes to integer arrays and clocks. -/
theorem GraphFrame.from_storage {before after : Heap}
    (storage : Queue.OtherStoragePreserved before after)
    (graph : Ref_Graph) (heads : CollectionRef) : GraphFrame before after graph heads := by
  rcases before with ⟨nr, values, no, objects, clocks, nc, collections⟩
  rcases after with ⟨nr', values', no', objects', clocks', nc', collections'⟩
  rcases storage with ⟨sameRef, sameObject, sameObjects, sameCollection, sameCollections⟩
  dsimp at sameRef sameObject sameObjects sameCollection sameCollections
  subst nr' no' objects' nc' collections'
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

namespace Queue

/-- Ticking changes no priority-queue data. -/
theorem QueueRep.tick {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (name : String) (amount : Nat := 1) :
    QueueRep (heap.tick name amount) queue layout := by
  exact ⟨representation.valid.tick name amount, representation.nonnegative,
    representation.indexed, representation.ordered⟩

/-- Updating a client's separate array leaves the priority queue represented. -/
theorem QueueRep.write_other {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (ref : SeqRef) (index value : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions)
    (notKeys : ref ≠ layout.keys) : QueueRep (heap.write ref index value) queue layout := by
  refine ⟨representation.valid.write ref index value, representation.nonnegative, ?_, ?_⟩
  · have vertices : (heap.write ref index value).read layout.vertices = heap.read layout.vertices := by
      funext position
      simp [Heap.read, Heap.write, Ne.symm notVertices]
    have positions : (heap.write ref index value).read layout.positions = heap.read layout.positions := by
      funext position
      simp [Heap.read, Heap.write, Ne.symm notPositions]
    rw [vertices, positions]
    exact representation.indexed
  · simpa [Heap.read, Heap.write, Ne.symm notVertices, Ne.symm notKeys] using representation.ordered

/-- The common successful insertion/decrease contract. Its membership and key
    maps describe the abstract update, while its frame clauses protect clients. -/
structure Updated (before after : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (vertex key newSize : Int) : Prop where
  representation : QueueRep after queue { layout with size := newSize }
  size : newSize = if 0 ≤ before.read layout.positions vertex then layout.size else layout.size + 1
  membership : ∀ value, 0 ≤ after.read layout.positions value ↔
    value = vertex ∨ 0 ≤ before.read layout.positions value
  keys : ∀ value, after.read layout.keys value =
    if value = vertex then key else before.read layout.keys value
  comparisons : Heap.cost before after "heap_comparisons" ≤ depth layout.size + 1
  swaps : Heap.cost before after "heap_swaps" ≤ depth layout.size
  otherArrays : ∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
    ∀ index, after.read ref index = before.read ref index
  otherClocks : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name
  nextRef : after.nextRef = before.nextRef
  graph : ∀ graph heads, GraphFrame before after graph heads
  footprint : before.Footprint after layout.refs [queue] []

/-- Extraction changes only the queue's owned arrays and object. -/
theorem Extracted.footprint {before after : Heap} {queue : Ref_MinHeap}
    {layout : Layout} {vertex : Int} (effect : Extracted before after queue layout vertex) :
    before.Footprint after layout.refs [queue] [] := by
  have changed := (Heap.Footprint.refl before layout.refs [queue] []).writeField queue
    "size" (.intValue (layout.size - 1)) (by simp)
  apply changed.trans
  exact (effect.otherStorage.footprint layout.refs (by
    intro ref outside; simp only [Layout.refs, List.mem_cons, List.mem_nil_iff, or_false, not_or] at outside
    funext index; exact effect.otherArrays ref outside.1 outside.2.1 index)).weaken
      (by simp) (by simp) (by simp)

/-- Insert an absent vertex or lower its present key. Both branches reuse the
    proved compiled queue contracts, including their termination witnesses. -/
theorem push_better_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (improves : 0 ≤ heap.read layout.positions vertex → key < heap.read layout.keys vertex) :
    ∃ after newSize, MinHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      Updated heap after queue layout vertex key newSize := by
  by_cases present : 0 ≤ heap.read layout.positions vertex
  · obtain ⟨after, run, represented, membership, keys, comparisons, swaps, arrays, clocks, storage⟩ :=
      decrease_correct heap queue layout representation vertex key present (improves present)
    have depthBound : depth (heap.read layout.positions vertex) ≤ depth layout.size :=
      depth_mono (Int.le_of_lt (representation.indexed.backward vertex present).1)
    refine ⟨after, layout.size, run, ?_⟩
    refine ⟨represented, by simp [present], ?_, keys, by omega, by omega,
      arrays, clocks, storage.nextRef, fun graph heads => GraphFrame.from_storage storage graph heads, ?_⟩
    · intro value
      rw [membership value]
      constructor
      · exact Or.inr
      · rintro (rfl | old)
        · exact present
        · exact old
    · exact (storage.footprint layout.refs (by
        intro ref outside; simp only [Layout.refs, List.mem_cons, List.mem_nil_iff, or_false, not_or] at outside
        funext index; exact arrays ref outside.1 outside.2.1 outside.2.2 index)).weaken
          (by simp) (by simp) (by simp)
  · have absent : heap.read layout.positions vertex = -1 :=
      representation.indexed.absent vertex (by omega)
    obtain ⟨after, run, represented, membership, keys, comparisons, swaps, arrays, clocks, storage⟩ :=
      insert_correct heap queue layout representation vertex key absent
    refine ⟨after, layout.size + 1, run, represented, by simp [present], membership,
      keys, by omega, swaps, arrays, clocks, storage.nextRef, ?_, ?_⟩
    · intro graph heads
      exact (graph_frame_queue_field heap graph heads queue representation.valid.object
        "size" (.intValue (layout.size + 1))).trans (GraphFrame.from_storage storage graph heads)
    · have changed := (Heap.Footprint.refl heap layout.refs [queue] []).writeField queue
        "size" (.intValue (layout.size + 1)) (by simp)
      apply changed.trans
      exact (storage.footprint layout.refs (by
        intro ref outside; simp only [Layout.refs, List.mem_cons, List.mem_nil_iff, or_false, not_or] at outside
        funext index; exact arrays ref outside.1 outside.2.1 outside.2.2 index)).weaken
          (by simp) (by simp) (by simp)

/-- The successful update adds at most one active vertex. -/
theorem Updated.size_bounds {before after : Heap} {queue : Ref_MinHeap} {layout : Layout}
    {vertex key newSize : Int} (updated : Updated before after queue layout vertex key newSize) :
    layout.size ≤ newSize ∧ newSize ≤ layout.size + 1 := by
  rw [updated.size]
  split <;> omega

/-- A common graph-size bound gives one logarithmic budget for either branch. -/
theorem Updated.cost_bounds {before after : Heap} {queue : Ref_MinHeap} {layout : Layout}
    {vertex key newSize : Int} (updated : Updated before after queue layout vertex key newSize)
    (maximumSize : Int) (bounded : layout.size ≤ maximumSize) :
    Heap.cost before after "heap_comparisons" ≤ depth maximumSize + 1 ∧
    Heap.cost before after "heap_swaps" ≤ depth maximumSize := by
  have monotone := depth_mono bounded
  have comparisons := updated.comparisons
  have swaps := updated.swaps
  omega

end Queue

/-- Constructing a fresh queue preserves an existing graph, its adjacency
    sequence, and all existing edge objects. -/
theorem graph_frame_queue_constructor (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (valid : is_Graph heap graph) : GraphFrame heap (Queue.newHeap heap) graph heads := by
  have oldObject (ref : ObjectRef) (old : ref < heap.nextObject) :
      (Queue.newHeap heap).objects ref = heap.objects ref := by
    simp [Queue.newHeap, Queue.initializedHeap, set_MinHeap_vertices, set_MinHeap_positions,
      set_MinHeap_keys, set_MinHeap_size, Heap.writeField, Heap.allocateObject, Heap.allocate,
      Nat.ne_of_lt old]
  have newValid : is_Graph (Queue.newHeap heap) graph := by
    refine ⟨Nat.lt_trans valid.1 (Nat.lt_succ_self _), ?_⟩
    simpa only [Heap.objectClass, oldObject graph valid.1] using valid.2
  refine ⟨fun _ => newValid, ?_, ?_, id, fun _ => rfl, ?_⟩
  · change field_Graph_size (Queue.newHeap heap) graph = field_Graph_size heap graph
    simp [field_Graph_size, valid, newValid, Heap.readField, oldObject graph valid.1]
  · change field_Graph_heads (Queue.newHeap heap) graph = field_Graph_heads heap graph
    simp [field_Graph_heads, valid, newValid, Heap.readField, oldObject graph valid.1]
  · intro ref oldValid
    change is_Edge heap ref at oldValid
    have edgeValid : is_Edge (Queue.newHeap heap) ref := by
      refine ⟨Nat.lt_trans oldValid.1 (Nat.lt_succ_self _), ?_⟩
      simpa only [Heap.objectClass, oldObject ref oldValid.1] using oldValid.2
    refine ⟨edgeValid, ?_, ?_, ?_⟩
    · change field_Edge_target (Queue.newHeap heap) ref = field_Edge_target heap ref
      simp [field_Edge_target, oldValid, edgeValid, Heap.readField, oldObject ref oldValid.1]
    · change field_Edge_weight (Queue.newHeap heap) ref = field_Edge_weight heap ref
      simp [field_Edge_weight, oldValid, edgeValid, Heap.readField, oldObject ref oldValid.1]
    · change field_Edge_next (Queue.newHeap heap) ref = field_Edge_next heap ref
      simp [field_Edge_next, oldValid, edgeValid, Heap.readField, oldObject ref oldValid.1]

/-- Constructor correctness and the caller's graph representation compose
    without inspecting the queue initializer's transitions. -/
theorem graph_rep_queue_constructor {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) :
    GraphRep (Queue.newHeap heap) graph size heads adjacency :=
  representation.preserved (graph_frame_queue_constructor heap graph heads representation.valid)


/-- The queue's inverse map supplies the finite cardinality bound needed by
    logarithmic bounds on insertion, decrease-key, and minimum extraction. -/
theorem queue_size_bound (heap : Heap) (queue : Ref_MinHeap) (layout : Queue.Layout)
    (representation : Queue.QueueRep heap queue layout) (remaining : List Int)
    (contained : ∀ vertex, 0 ≤ heap.read layout.positions vertex → vertex ∈ remaining) :
    layout.size ≤ (remaining.length : Int) := by
  apply active_prefix_bound (heap.read layout.vertices) (heap.read layout.positions) layout.size
    representation.nonnegative representation.indexed.forward remaining
  intro index nonnegative bound
  apply contained
  rw [representation.indexed.forward index nonnegative bound]
  exact nonnegative

theorem queue_depth_bound (heap : Heap) (queue : Ref_MinHeap) (layout : Queue.Layout)
    (representation : Queue.QueueRep heap queue layout) (size : Int)
    (contained : ∀ vertex, 0 ≤ heap.read layout.positions vertex → 0 ≤ vertex ∧ vertex < size) :
    layout.size ≤ size.toNat ∧ Queue.depth layout.size ≤ Queue.depth size := by
  have bound := queue_size_bound heap queue layout representation (vertexRange size)
    (by intro vertex present; exact (vertexRange_member size vertex).mpr (contained vertex present))
  simp only [vertexRange_length] at bound
  have nonnegativeSize := representation.nonnegative
  refine ⟨bound, ?_⟩
  by_cases nonnegative : 0 ≤ size
  · apply Queue.depth_mono
    omega
  · have empty : layout.size = 0 := by omega
    simp [Queue.depth, empty, Int.toNat_eq_zero.mpr (by omega : size ≤ 0)]

/-- The two client arrays are allocated before the independent priority queue. -/
def allocatedForDijkstra (heap : Heap) : Heap :=
  (heap.allocate (fun _ => -1)).allocate (fun _ => 0)

def queueForDijkstra (heap : Heap) : Heap := Queue.newHeap (allocatedForDijkstra heap)

def layoutForDijkstra (heap : Heap) : Queue.Layout := Queue.emptyLayout (allocatedForDijkstra heap)

def preparedForDijkstra (heap : Heap) (source : Int) : Heap :=
  (queueForDijkstra heap).write heap.nextRef source 0

def queuedForDijkstra (heap : Heap) (source : Int) : Heap :=
  Queue.insertedHeap (preparedForDijkstra heap source) heap.nextObject (layoutForDijkstra heap) source 0

/-- Initialization allocates every writable location freshly, preserving all
    storage that was already present in the caller's heap. -/
theorem initialization_footprint (heap : Heap) (source : Int) :
    heap.Footprint (queuedForDijkstra heap source) [] [] [] := by
  unfold queuedForDijkstra preparedForDijkstra queueForDijkstra allocatedForDijkstra
    Queue.newHeap Queue.initializedHeap Queue.insertedHeap
    set_MinHeap_vertices set_MinHeap_positions set_MinHeap_keys set_MinHeap_size
  repeat first
    | apply Heap.Footprint.writeField
    | apply Heap.Footprint.write
    | apply Heap.Footprint.allocate
    | apply Heap.Footprint.allocateObject
    | exact Heap.Footprint.refl _ _ _ _
    | (apply Or.inr; dsimp [layoutForDijkstra, Queue.emptyLayout, allocatedForDijkstra, Heap.allocate]; omega)
  all_goals first
    | (apply Or.inr; dsimp [layoutForDijkstra, Queue.emptyLayout, allocatedForDijkstra, Heap.allocate]; omega)
    | simp
    | (try simp only [Heap.allocate]; omega)

theorem prepared_queue_rep (heap : Heap) (source : Int) :
    Queue.QueueRep (preparedForDijkstra heap source) heap.nextObject (layoutForDijkstra heap) := by
  exact (Queue.new_heap_rep (allocatedForDijkstra heap)).write_other heap.nextRef source 0
    (by change heap.nextRef ≠ heap.nextRef + 1 + 1; omega)
    (by change heap.nextRef ≠ heap.nextRef + 1 + 1 + 1; omega)
    (by change heap.nextRef ≠ heap.nextRef + 1 + 1 + 2; omega)

theorem prepared_queue_positions (heap : Heap) (source vertex : Int) :
    (preparedForDijkstra heap source).read (layoutForDijkstra heap).positions vertex = -1 :=
  (prepared_queue_rep heap source).empty_positions rfl vertex

theorem initial_queue_insertion (heap : Heap) (source : Int) :
    MinHeap.push_or_decrease.Call (preparedForDijkstra heap source)
      (heap.nextObject, source, 0) (queuedForDijkstra heap source) () := by
  exact Queue.insert_empty_summary _ _ _ (prepared_queue_rep heap source).valid rfl source 0
    (by rw [prepared_queue_positions]; omega)

/-- The source is the queue's only member after the first insertion. -/
theorem initial_queue_positions (heap : Heap) (source vertex : Int) :
    (queuedForDijkstra heap source).read (layoutForDijkstra heap).positions vertex =
      if vertex = source then 0 else -1 := by
  change (Queue.appendedHeap (preparedForDijkstra heap source) heap.nextObject
    (layoutForDijkstra heap) source 0).read (layoutForDijkstra heap).positions vertex = _
  rw [Queue.appended_positions _ _ _ (prepared_queue_rep heap source).valid,
    prepared_queue_positions]
  rfl

theorem initial_queue_rep (heap : Heap) (source : Int) :
    Queue.QueueRep (queuedForDijkstra heap source) heap.nextObject
      { layoutForDijkstra heap with size := 1 } := by
  have prepared := prepared_queue_rep heap source
  refine ⟨Queue.inserted_layout _ _ _ prepared.valid source 0, by change (0 : Int) ≤ 1; decide, ?_, ?_⟩
  · exact Queue.appended_indexed _ _ _ prepared.valid prepared.indexed prepared.nonnegative
      source 0 (prepared_queue_positions heap source source)
  · intro child positive bounded
    change child < 1 at bounded
    omega

theorem initial_distance_values (heap : Heap) (source vertex : Int) :
    (queuedForDijkstra heap source).read heap.nextRef vertex =
      if vertex = source then 0 else -1 := by
  rw [queuedForDijkstra, Queue.inserted_read_other _ _ _ _ _ _ _
    (by change heap.nextRef ≠ heap.nextRef + 1 + 1; omega)
    (by change heap.nextRef ≠ heap.nextRef + 1 + 1 + 1; omega)
    (by change heap.nextRef ≠ heap.nextRef + 1 + 1 + 2; omega)]
  change ((Queue.newHeap (allocatedForDijkstra heap)).write heap.nextRef source 0).read heap.nextRef vertex = _
  by_cases same : vertex = source
  · simp [same]
  · rw [Heap.read_write_other_index _ _ _ _ _ same,
      Queue.new_heap_read_old _ _ _ (by change heap.nextRef < heap.nextRef + 1 + 1; omega)]
    simp [allocatedForDijkstra, Heap.read, Heap.allocate, same]

theorem initial_settled_values (heap : Heap) (source vertex : Int) :
    (queuedForDijkstra heap source).read (heap.nextRef + 1) vertex = 0 := by
  rw [queuedForDijkstra, Queue.inserted_read_other _ _ _ _ _ _ _
    (by change heap.nextRef + 1 ≠ heap.nextRef + 1 + 1; omega)
    (by change heap.nextRef + 1 ≠ heap.nextRef + 1 + 1 + 1; omega)
    (by change heap.nextRef + 1 ≠ heap.nextRef + 1 + 1 + 2; omega)]
  change ((Queue.newHeap (allocatedForDijkstra heap)).write heap.nextRef source 0).read (heap.nextRef + 1) vertex = _
  rw [Heap.read_write_other_ref _ _ _ _ _ _ (show heap.nextRef + 1 ≠ heap.nextRef by omega),
    Queue.new_heap_read_old _ _ _ (by change heap.nextRef + 1 < heap.nextRef + 1 + 1; omega)]
  simp [allocatedForDijkstra, Heap.read, Heap.allocate]

/-- The initial source key is zero; unreachable vertices are not queued. -/
theorem initial_source_key (heap : Heap) (source : Int) :
    (queuedForDijkstra heap source).read (layoutForDijkstra heap).keys source = 0 := by
  exact Queue.inserted_key _ _ _ source 0 (prepared_queue_rep heap source).valid.verticesKeys
    (prepared_queue_rep heap source).valid.positionsKeys

theorem initial_graph_preserved {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) (source : Int) :
    GraphRep (queuedForDijkstra heap source) graph size heads adjacency := by
  have arrays : GraphRep (allocatedForDijkstra heap) graph size heads adjacency :=
    (representation.preserved (graph_frame_allocate heap graph heads (fun _ => -1))).preserved
      (graph_frame_allocate _ graph heads (fun _ => 0))
  have queue := graph_rep_queue_constructor arrays
  have prepared : GraphRep (preparedForDijkstra heap source) graph size heads adjacency :=
    queue.preserved (graph_frame_write _ graph heads heap.nextRef source 0)
  exact prepared.preserved (graph_frame_queue_insert _ graph heads heap.nextObject
    (prepared_queue_rep heap source).valid.object (layoutForDijkstra heap) source 0)

/-- Everything the extraction-loop proof needs after source initialization.
    Client and queue arrays are disjoint, and initialization charges no ticks. -/
structure Initialized (before after : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (source : Int) (layout : Queue.Layout) : Prop where
  constructor : MinHeap.Call (allocatedForDijkstra before) () (queueForDijkstra before) before.nextObject
  beforeInsertionAllocated : before.nextRef < (queueForDijkstra before).nextRef
  insertion : MinHeap.push_or_decrease.Call (preparedForDijkstra before source)
    (before.nextObject, source, 0) after ()
  graph : GraphRep after graph size heads adjacency
  queue : Queue.QueueRep after before.nextObject layout
  sizeOne : layout.size = 1
  distances : ∀ vertex, after.read before.nextRef vertex = if vertex = source then 0 else -1
  settled : ∀ vertex, after.read (before.nextRef + 1) vertex = 0
  membership : ∀ vertex, 0 ≤ after.read layout.positions vertex ↔ vertex = source
  key : after.read layout.keys source = 0
  distanceAllocated : before.nextRef < after.nextRef
  settledAllocated : before.nextRef + 1 < after.nextRef
  clientsSeparate : before.nextRef ≠ before.nextRef + 1
  distanceVertices : before.nextRef ≠ layout.vertices
  distancePositions : before.nextRef ≠ layout.positions
  distanceKeys : before.nextRef ≠ layout.keys
  settledVertices : before.nextRef + 1 ≠ layout.vertices
  settledPositions : before.nextRef + 1 ≠ layout.positions
  settledKeys : before.nextRef + 1 ≠ layout.keys
  clocks : after.clocks = before.clocks

/-- A valid graph admits initialization with the exact source-only queue.
    Source bounds are required by the outer algorithm's guard, not this data construction. -/
theorem initialization_ready {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) (source : Int) :
    Initialized heap (queuedForDijkstra heap source) graph size heads adjacency source
      { layoutForDijkstra heap with size := 1 } := by
  refine ⟨Queue.new_heap_summary (allocatedForDijkstra heap), ?_, initial_queue_insertion heap source,
    initial_graph_preserved representation source, initial_queue_rep heap source, rfl,
    initial_distance_values heap source, initial_settled_values heap source, ?_,
    initial_source_key heap source, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · change heap.nextRef < heap.nextRef + 1 + 1 + 1 + 1 + 1
    omega
  · intro vertex
    change 0 ≤ (queuedForDijkstra heap source).read (layoutForDijkstra heap).positions vertex ↔ _
    rw [initial_queue_positions]
    by_cases same : vertex = source <;> simp [same]
  · change heap.nextRef < heap.nextRef + 1 + 1 + 1 + 1 + 1
    omega
  · change heap.nextRef + 1 < heap.nextRef + 1 + 1 + 1 + 1 + 1
    omega
  · omega
  · change heap.nextRef ≠ heap.nextRef + 1 + 1
    omega
  · change heap.nextRef ≠ heap.nextRef + 1 + 1 + 1
    omega
  · change heap.nextRef ≠ heap.nextRef + 1 + 1 + 2
    omega
  · change heap.nextRef + 1 ≠ heap.nextRef + 1 + 1
    omega
  · change heap.nextRef + 1 ≠ heap.nextRef + 1 + 1 + 1
    omega
  · change heap.nextRef + 1 ≠ heap.nextRef + 1 + 1 + 2
    omega


private theorem segment_clocks_monotone {before after : Configuration}
    (segment : Reaches Step before after) :
    ∀ name, before.heap.clocks name ≤ after.heap.clocks name := by
  intro name
  have resumeHeap (h : Heap) (result : Result) (stack : Stack) :
      (resumeConfig h result stack).heap = h := by
    cases stack <;> rfl
  have stepClock (before after : Configuration) (transition : Step before after) :
      before.heap.clocks name ≤ after.heap.clocks name := by
    cases transition <;> first
      | exact Nat.le_refl _
      | exact Heap.clocks_le_tick ..
      | rw [resumeHeap]; exact Nat.le_refl _
  exact segment.invariant (fun state => before.heap.clocks name ≤ state.heap.clocks name)
    (Nat.le_refl _) (fun first second transition bound =>
      Nat.le_trans bound (stepClock first second transition))

/-- Queue calls can start with any existing counters, including counters
    maintained by an enclosing Dijkstra execution. -/
theorem push_clocks_monotone (heap after : Heap) (queue : Ref_MinHeap) (vertex key : Int)
    (summary : MinHeap.push_or_decrease.Call heap (queue, vertex, key) after ()) :
    ∀ name, heap.clocks name ≤ after.clocks name :=
  segment_clocks_monotone summary.2.root

theorem pop_clocks_monotone (heap after : Heap) (queue : Ref_MinHeap) (vertex : Int)
    (summary : MinHeap.pop_min.Call heap queue after vertex) :
    ∀ name, heap.clocks name ≤ after.clocks name :=
  segment_clocks_monotone summary.2.root

/-- The remainder of a Dijkstra call is monotone from its supplied local
    configuration; no entry reachability assumption is necessary. -/
theorem dijkstra_remaining_clocks_monotone (state : Configuration) (after : Heap) (result : SeqRef)
    (summary : dijkstra.CallFrom state after result) :
    ∀ name, state.heap.clocks name ≤ after.clocks name := by
  cases state with
  | done => cases summary
  | active heap frame stack =>
    cases frame <;> try (cases summary)
    exact segment_clocks_monotone summary.root

/-- Upper bounds on natural clock deltas are equivalent to bounds on the
    final counter, even without a separate monotonicity hypothesis. -/
theorem cost_bound_iff (before after : Heap) (name : String) (budget : Nat) :
    Heap.cost before after name ≤ budget ↔ after.clocks name ≤ before.clocks name + budget := by
  unfold Heap.cost
  omega

/-- Compose a local operation bound with the budget for the remaining run. -/
theorem cost_bound_compose (before middle after : Heap) (name : String) (localCost restCost : Nat)
    (localBound : Heap.cost before middle name ≤ localCost)
    (restBound : Heap.cost middle after name ≤ restCost) :
    Heap.cost before after name ≤ localCost + restCost := by
  unfold Heap.cost at *
  omega

/-- A tick and a queue call form one accounting segment. Unlike an upper
    bound, this exact identity uses the call's proved counter monotonicity. -/
theorem tick_push_cost (before after : Heap) (queue : Ref_MinHeap) (vertex key : Int)
    (clock : String) (amount : Nat)
    (summary : MinHeap.push_or_decrease.Call (before.tick clock amount)
      (queue, vertex, key) after ()) (name : String) :
    Heap.cost before after name = Clocks.single clock amount name +
      Heap.cost (before.tick clock amount) after name := by
  rw [Heap.cost_add before (before.tick clock amount) after name
    (Heap.clocks_le_tick before clock name amount)
    (push_clocks_monotone _ _ queue vertex key summary name)]
  congr 1
  by_cases same : name = clock <;> simp [Clocks.single, same]



/-- The priority queue contains exactly the finite unsettled distances, with
    each queued key equal to that vertex's current tentative distance. -/
structure QueueMatches (heap : Heap) (layout : Queue.Layout) (distance settled : SeqRef) : Prop where
  membership : ∀ vertex, 0 ≤ heap.read layout.positions vertex ↔
    heap.read settled vertex = 0 ∧ 0 ≤ heap.read distance vertex
  keys : ∀ vertex, 0 ≤ heap.read layout.positions vertex →
    heap.read layout.keys vertex = heap.read distance vertex

theorem QueueMatches.tick {heap : Heap} {layout : Queue.Layout} {distance settled : SeqRef}
    (matching : QueueMatches heap layout distance settled) (clock : String) (amount : Nat := 1) :
    QueueMatches (heap.tick clock amount) layout distance settled :=
  ⟨matching.membership, matching.keys⟩

/-- Empty queue plus the inverse map means that no unsettled finite distance remains. -/
theorem QueueMatches.exhausted {heap : Heap} {queue : Ref_MinHeap} {layout : Queue.Layout}
    {distance settled : SeqRef} (matching : QueueMatches heap layout distance settled)
    (representation : Queue.QueueRep heap queue layout) (empty : layout.size = 0) :
    ∀ vertex, heap.read settled vertex = 0 → heap.read distance vertex < 0 := by
  intro vertex unsettled
  have absent := representation.empty_positions empty vertex
  by_cases finite : 0 ≤ heap.read distance vertex
  · have present := (matching.membership vertex).mpr ⟨unsettled, finite⟩
    omega
  · omega

/-- Minimum extraction is the mathematical greedy choice through the client
    invariant, with no array positions in the conclusion. -/
theorem QueueMatches.selected {before after : Heap} {queue : Ref_MinHeap}
    {layout : Queue.Layout} {distance settled : SeqRef} {vertex : Int}
    (matching : QueueMatches before layout distance settled)
    (extracted : Queue.Extracted before after queue layout vertex) :
    before.read settled vertex = 0 ∧ 0 ≤ before.read distance vertex ∧
      ∀ other, before.read settled other = 0 → 0 ≤ before.read distance other →
        before.read distance vertex ≤ before.read distance other := by
  obtain ⟨unsettled, finite⟩ := (matching.membership vertex).mp extracted.wasPresent
  refine ⟨unsettled, finite, ?_⟩
  intro other otherUnsettled otherFinite
  have present := (matching.membership other).mpr ⟨otherUnsettled, otherFinite⟩
  have minimum := extracted.minimum other present
  rw [matching.keys vertex extracted.wasPresent, matching.keys other present] at minimum
  exact minimum

/-- Extraction followed by settling removes exactly the selected vertex from
    both descriptions of the queue and leaves all other tentative keys aligned. -/
theorem QueueMatches.extract_and_settle {before after : Heap} {queue : Ref_MinHeap}
    {layout : Queue.Layout} {distance settled : SeqRef} {vertex : Int}
    (matching : QueueMatches before layout distance settled)
    (extracted : Queue.Extracted before after queue layout vertex)
    (different : distance ≠ settled)
    (distanceVertices : distance ≠ layout.vertices) (distancePositions : distance ≠ layout.positions)
    (settledVertices : settled ≠ layout.vertices) (settledPositions : settled ≠ layout.positions)
    (settledKeys : settled ≠ layout.keys) :
    QueueMatches (settleHeap after settled vertex) {layout with size := layout.size - 1}
      distance settled := by
  have distanceSame (v : Int) : after.read distance v = before.read distance v :=
    extracted.otherArrays distance distanceVertices distancePositions v
  have settledSame (v : Int) : after.read settled v = before.read settled v :=
    extracted.otherArrays settled settledVertices settledPositions v
  have positionsSame (v : Int) :
      (settleHeap after settled vertex).read layout.positions v = after.read layout.positions v := by
    simp [settleHeap, Heap.read, Heap.write, Ne.symm settledPositions]
  have keysSame (v : Int) :
      (settleHeap after settled vertex).read layout.keys v = before.read layout.keys v := by
    simpa [settleHeap, Heap.read, Heap.write, Ne.symm settledKeys] using extracted.keys v
  have distanceFinal (v : Int) :
      (settleHeap after settled vertex).read distance v = before.read distance v := by
    simpa [settleHeap, Heap.read, Heap.write, different] using distanceSame v
  have settledFinal (v : Int) : (settleHeap after settled vertex).read settled v =
      if v = vertex then 1 else before.read settled v := by
    simpa [settleHeap, Heap.read, Heap.write] using
      congrArg (fun value => if v = vertex then 1 else value) (settledSame v)
  constructor
  · intro value
    change 0 ≤ (settleHeap after settled vertex).read layout.positions value ↔ _
    rw [positionsSame, extracted.membership, matching.membership,
      distanceFinal, settledFinal]
    by_cases same : value = vertex <;> simp [same]
  · intro value present
    change (settleHeap after settled vertex).read layout.keys value = _
    rw [keysSame, distanceFinal]
    apply matching.keys
    change 0 ≤ (settleHeap after settled vertex).read layout.positions value at present
    rw [positionsSame] at present
    exact ((extracted.membership value).mp present).1



/-- Storage validity is separate from the shortest-path invariant. Client
    arrays are allocated and cannot alias the queue's three internal arrays. -/
structure StorageInvariant (heap : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (layout : Queue.Layout) : Prop where
  graph : GraphRep heap graph size heads adjacency
  queue : Queue.QueueRep heap queue layout
  distanceAllocated : distance < heap.nextRef
  settledAllocated : settled < heap.nextRef
  clientsSeparate : distance ≠ settled
  distanceVertices : distance ≠ layout.vertices
  distancePositions : distance ≠ layout.positions
  distanceKeys : distance ≠ layout.keys
  settledVertices : settled ≠ layout.vertices
  settledPositions : settled ≠ layout.positions
  settledKeys : settled ≠ layout.keys

namespace StorageInvariant

variable {heap : Heap} {graph : Ref_Graph} {size : Int} {heads : CollectionRef}
    {adjacency : Adjacency} {distance settled : SeqRef} {queue : Ref_MinHeap} {layout : Queue.Layout}

/-- A tick changes no storage observation or allocation bound. -/
theorem tick (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (name : String) (amount : Nat := 1) :
    StorageInvariant (heap.tick name amount) graph size heads adjacency distance settled queue layout := by
  exact ⟨storage.graph.preserved (graph_frame_tick heap graph heads name amount),
    storage.queue.tick name amount, storage.distanceAllocated, storage.settledAllocated,
    storage.clientsSeparate, storage.distanceVertices, storage.distancePositions, storage.distanceKeys,
    storage.settledVertices, storage.settledPositions, storage.settledKeys⟩

/-- A separate client array may be written without touching graph or queue storage. -/
theorem write_client (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (ref : SeqRef) (index value : Int) (notVertices : ref ≠ layout.vertices)
    (notPositions : ref ≠ layout.positions) (notKeys : ref ≠ layout.keys) :
    StorageInvariant (heap.write ref index value) graph size heads adjacency distance settled queue layout := by
  exact ⟨storage.graph.preserved (graph_frame_write heap graph heads ref index value),
    storage.queue.write_other ref index value notVertices notPositions notKeys,
    storage.distanceAllocated, storage.settledAllocated,
    storage.clientsSeparate, storage.distanceVertices, storage.distancePositions, storage.distanceKeys,
    storage.settledVertices, storage.settledPositions, storage.settledKeys⟩

theorem write_distance (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (vertex value : Int) :
    StorageInvariant (heap.write distance vertex value) graph size heads adjacency distance settled queue layout :=
  storage.write_client distance vertex value storage.distanceVertices storage.distancePositions storage.distanceKeys

theorem write_settled (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (vertex value : Int) :
    StorageInvariant (heap.write settled vertex value) graph size heads adjacency distance settled queue layout :=
  storage.write_client settled vertex value storage.settledVertices storage.settledPositions storage.settledKeys

theorem settle (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (vertex : Int) :
    StorageInvariant (settleHeap heap settled vertex) graph size heads adjacency distance settled queue layout :=
  (storage.write_settled vertex 1).tick "settlements"

theorem relaxation (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (target candidate : Int) :
    StorageInvariant (relaxationHeap heap distance target candidate)
      graph size heads adjacency distance settled queue layout :=
  (storage.tick "edges").write_distance target candidate

/-- Minimum extraction preserves all graph storage and client allocations;
    its queue contract provides the shortened representation. -/
theorem extracted (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    {after : Heap} {vertex : Int} (effect : Queue.Extracted heap after queue layout vertex) :
    StorageInvariant after graph size heads adjacency distance settled queue
      { layout with size := layout.size - 1 } := by
  have frame : GraphFrame heap after graph heads :=
    (graph_frame_queue_field heap graph heads queue storage.queue.valid.object
      "size" (.intValue (layout.size - 1))).trans (GraphFrame.from_storage effect.otherStorage graph heads)
  have allocation : after.nextRef = heap.nextRef := effect.otherStorage.nextRef
  exact ⟨storage.graph.preserved frame, effect.representation,
    by rw [allocation]; exact storage.distanceAllocated,
    by rw [allocation]; exact storage.settledAllocated,
    storage.clientsSeparate, storage.distanceVertices, storage.distancePositions, storage.distanceKeys,
    storage.settledVertices, storage.settledPositions, storage.settledKeys⟩

theorem pop_settle (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    {after : Heap} {vertex : Int} (effect : Queue.Extracted heap after queue layout vertex) :
    StorageInvariant (settleHeap after settled vertex) graph size heads adjacency distance settled queue
      { layout with size := layout.size - 1 } :=
  (storage.extracted effect).settle vertex

/-- Successful push/decrease preserves the client's storage while replacing
    the queue representation with the size given by the update contract. -/
theorem updated (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    {after : Heap} {vertex key newSize : Int}
    (effect : Queue.Updated heap after queue layout vertex key newSize) :
    StorageInvariant after graph size heads adjacency distance settled queue
      { layout with size := newSize } := by
  exact ⟨storage.graph.preserved (effect.graph graph heads), effect.representation,
    by rw [effect.nextRef]; exact storage.distanceAllocated,
    by rw [effect.nextRef]; exact storage.settledAllocated,
    storage.clientsSeparate, storage.distanceVertices, storage.distancePositions, storage.distanceKeys,
    storage.settledVertices, storage.settledPositions, storage.settledKeys⟩

/-- A complete successful relaxation preserves storage through its edge tick,
    distance update, queue call, and final improvement tick. -/
theorem improved (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    {after : Heap} {target candidate newSize : Int}
    (effect : Queue.Updated (relaxationHeap heap distance target candidate) after
      queue layout target candidate newSize) :
    StorageInvariant (after.tick "improvements") graph size heads adjacency distance settled queue
      { layout with size := newSize } :=
  ((storage.relaxation target candidate).updated effect).tick "improvements"

end StorageInvariant

/-- The exact initialization bundle supplies the storage invariant used by
    every subsequent extraction and adjacency-loop iteration. -/
theorem Initialized.storage {before after : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency} {source : Int} {layout : Queue.Layout}
    (initialized : Initialized before after graph size heads adjacency source layout) :
    StorageInvariant after graph size heads adjacency before.nextRef (before.nextRef + 1)
      before.nextObject layout :=
  ⟨initialized.graph, initialized.queue, initialized.distanceAllocated, initialized.settledAllocated,
    initialized.clientsSeparate, initialized.distanceVertices, initialized.distancePositions, initialized.distanceKeys,
    initialized.settledVertices, initialized.settledPositions, initialized.settledKeys⟩



/-- Successful relaxation changes exactly the target distance; the queue call
    and final tick preserve the client's separate distance array. -/
theorem Queue.Updated.distance_updated
    {before after : Heap} {graph : Ref_Graph} {size : Int} {heads : CollectionRef}
    {adjacency : Adjacency} {distance settled : SeqRef} {queue : Ref_MinHeap}
    {layout : Queue.Layout} {target candidate newSize : Int}
    (effect : Queue.Updated (relaxationHeap before distance target candidate) after
      queue layout target candidate newSize)
    (storage : StorageInvariant before graph size heads adjacency distance settled queue layout)
    (vertex : Int) :
    (after.tick "improvements").read distance vertex =
      if vertex = target then candidate else before.read distance vertex := by
  rw [Heap.read_tick, effect.otherArrays distance storage.distanceVertices storage.distancePositions storage.distanceKeys]
  simp [relaxationHeap, Heap.read, Heap.write]

/-- Successful relaxation leaves every settled flag unchanged. -/
theorem Queue.Updated.settled_updated
    {before after : Heap} {graph : Ref_Graph} {size : Int} {heads : CollectionRef}
    {adjacency : Adjacency} {distance settled : SeqRef} {queue : Ref_MinHeap}
    {layout : Queue.Layout} {target candidate newSize : Int}
    (effect : Queue.Updated (relaxationHeap before distance target candidate) after
      queue layout target candidate newSize)
    (storage : StorageInvariant before graph size heads adjacency distance settled queue layout)
    (vertex : Int) :
    (after.tick "improvements").read settled vertex = before.read settled vertex := by
  rw [Heap.read_tick, effect.otherArrays settled storage.settledVertices storage.settledPositions storage.settledKeys]
  simp [relaxationHeap, Heap.read, Heap.write, Ne.symm storage.clientsSeparate]

/-- The complete successful relaxation segment preserves graph observations,
    including existing edge objects and adjacency-list tails. -/
theorem Queue.Updated.graph_updated
    {before after : Heap} {distance : SeqRef} {queue : Ref_MinHeap}
    {layout : Queue.Layout} {target candidate newSize : Int}
    (effect : Queue.Updated (relaxationHeap before distance target candidate) after
      queue layout target candidate newSize) (graph : Ref_Graph) (heads : CollectionRef) :
    GraphFrame before (after.tick "improvements") graph heads := by
  have preparation : GraphFrame before (relaxationHeap before distance target candidate) graph heads :=
    (graph_frame_tick before graph heads "edges" 1).trans
      (graph_frame_write _ graph heads distance target candidate)
  exact (preparation.trans (effect.graph graph heads)).trans
    (graph_frame_tick after graph heads "improvements" 1)

/-- Inserting or decreasing an unsettled target keeps queue membership and
    priorities aligned with the updated tentative distances. -/
theorem QueueMatches.improved
    {before after : Heap} {graph : Ref_Graph} {size : Int} {heads : CollectionRef}
    {adjacency : Adjacency} {distance settled : SeqRef} {queue : Ref_MinHeap}
    {layout : Queue.Layout} {target candidate newSize : Int}
    (matching : QueueMatches before layout distance settled)
    (storage : StorageInvariant before graph size heads adjacency distance settled queue layout)
    (effect : Queue.Updated (relaxationHeap before distance target candidate) after
      queue layout target candidate newSize)
    (unsettled : before.read settled target = 0) (nonnegative : 0 ≤ candidate) :
    QueueMatches (after.tick "improvements") {layout with size := newSize} distance settled := by
  have membership (vertex : Int) :
      0 ≤ (after.tick "improvements").read layout.positions vertex ↔
        vertex = target ∨ 0 ≤ before.read layout.positions vertex := by
    simpa [relaxationHeap, Heap.read, Heap.write, Ne.symm storage.distancePositions] using
      effect.membership vertex
  have keys (vertex : Int) : (after.tick "improvements").read layout.keys vertex =
      if vertex = target then candidate else before.read layout.keys vertex := by
    rw [Heap.read_tick, effect.keys]
    simp [relaxationHeap, Heap.read, Heap.write, Ne.symm storage.distanceKeys]
  constructor
  · intro vertex
    change 0 ≤ (after.tick "improvements").read layout.positions vertex ↔ _
    rw [membership, effect.distance_updated storage, effect.settled_updated storage, matching.membership]
    by_cases same : vertex = target <;> simp [same, unsettled, nonnegative]
  · intro vertex present
    change (after.tick "improvements").read layout.keys vertex = _
    rw [keys, effect.distance_updated storage]
    by_cases same : vertex = target
    · simp [same]
    · simp only [if_neg same]
      apply matching.keys
      change 0 ≤ (after.tick "improvements").read layout.positions vertex at present
      exact ((membership vertex).mp present).resolve_left same


/-- The extraction-loop invariant separates storage, queue contents, shortest
    paths, and the finite set of vertices that may still be settled. -/
structure LoopInvariant (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (layout : Queue.Layout) (remaining : List Int) : Prop where
  storage : StorageInvariant heap graph size heads adjacency distance settled queue layout
  matching : QueueMatches heap layout distance settled
  paths : SearchInvariant (representedEdges size adjacency) source (heap.read distance)
    (fun vertex => heap.read settled vertex ≠ 0)
  finiteInRange : ∀ vertex, 0 ≤ heap.read distance vertex → 0 ≤ vertex ∧ vertex < size
  unique : remaining.Nodup
  members : ∀ vertex, vertex ∈ remaining ↔
    0 ≤ vertex ∧ vertex < size ∧ heap.read settled vertex = 0

/-- Initialization gives the full loop invariant, including its finite measure. -/
theorem Initialized.invariant {before after : Heap} {graph : Ref_Graph} {size source : Int}
    {heads : CollectionRef} {adjacency : Adjacency} {layout : Queue.Layout}
    (initialized : Initialized before after graph size heads adjacency source layout)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    LoopInvariant after graph size source heads adjacency before.nextRef (before.nextRef + 1)
      before.nextObject layout (vertexRange size) := by
  have distances : after.read before.nextRef = initialDistances source := by
    funext vertex
    exact initialized.distances vertex
  have settled : (fun vertex => after.read (before.nextRef + 1) vertex ≠ 0) = (fun _ => False) := by
    funext vertex
    simp [initialized.settled]
  refine ⟨initialized.storage, ?_, ?_, ?_, vertexRange_nodup size, ?_⟩
  · constructor
    · intro vertex
      rw [initialized.membership, initialized.settled, initialized.distances]
      by_cases same : vertex = source <;> simp [same]
    · intro vertex present
      have same := (initialized.membership vertex).mp present
      subst vertex
      rw [initialized.key, initialized.distances]
      simp
  · rw [distances, settled]
    exact initial_search_invariant _ source
  · intro vertex finite
    rw [initialized.distances] at finite
    by_cases same : vertex = source
    · subst vertex
      exact ⟨sourceNonnegative, sourceBound⟩
    · simp [same] at finite
  · intro vertex
    simp [initialized.settled]

/-- Queue exhaustion supplies the ordinary shortest-distance specification. -/
theorem LoopInvariant.finished {heap : Heap} {graph : Ref_Graph} {size source : Int}
    {heads : CollectionRef} {adjacency : Adjacency} {distance settled : SeqRef}
    {queue : Ref_MinHeap} {layout : Queue.Layout} {remaining : List Int}
    (invariant : LoopInvariant heap graph size source heads adjacency distance settled queue layout remaining)
    (empty : layout.size = 0) :
    ∀ vertex,
      (heap.read distance vertex = -1 ↔ ∀ cost, ¬ Path (representedEdges size adjacency) source vertex cost) ∧
      (0 ≤ heap.read distance vertex →
        IsShortest (representedEdges size adjacency) source vertex (heap.read distance vertex)) := by
  apply exhausted_distances_correct _ source _ _ invariant.paths
  intro vertex unsettled
  exact invariant.matching.exhausted invariant.storage.queue empty vertex (by simpa using unsettled)

/-- Every popped vertex belongs to the remaining list, so removing it strictly
    decreases the outer-loop termination measure. -/
theorem LoopInvariant.selected_member {before after : Heap} {graph : Ref_Graph} {size source : Int}
    {heads : CollectionRef} {adjacency : Adjacency} {distance settled : SeqRef}
    {queue : Ref_MinHeap} {layout : Queue.Layout} {remaining : List Int} {vertex : Int}
    (invariant : LoopInvariant before graph size source heads adjacency distance settled queue layout remaining)
    (extracted : Queue.Extracted before after queue layout vertex) : vertex ∈ remaining := by
  obtain ⟨unsettled, finite, _⟩ := invariant.matching.selected extracted
  obtain ⟨lower, upper⟩ := invariant.finiteInRange vertex finite
  exact (invariant.members vertex).mpr ⟨lower, upper, unsettled⟩


/-- Immediately after extraction, the selected vertex is settled but its
    outgoing frontier still needs to be restored by the adjacency scan. -/
structure ScanInvariant (heap : Heap) (graph : Ref_Graph) (size source selected : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (layout : Queue.Layout) (remaining : List Int) : Prop where
  storage : StorageInvariant heap graph size heads adjacency distance settled queue layout
  matching : QueueMatches heap layout distance settled
  paths : RelaxationInvariant (representedEdges size adjacency) source (heap.read distance)
    (fun vertex => heap.read settled vertex ≠ 0) selected []
  finiteInRange : ∀ vertex, 0 ≤ heap.read distance vertex → 0 ≤ vertex ∧ vertex < size
  unique : remaining.Nodup
  members : ∀ vertex, vertex ∈ remaining ↔
    0 ≤ vertex ∧ vertex < size ∧ heap.read settled vertex = 0

/-- The compiled minimum extraction realizes the greedy settlement step. -/
theorem LoopInvariant.begin_scan {before after : Heap} {graph : Ref_Graph} {size source : Int}
    {heads : CollectionRef} {adjacency : Adjacency} {distance settled : SeqRef}
    {queue : Ref_MinHeap} {layout : Queue.Layout} {remaining : List Int} {vertex : Int}
    (invariant : LoopInvariant before graph size source heads adjacency distance settled queue layout remaining)
    (extracted : Queue.Extracted before after queue layout vertex) :
    ScanInvariant (settleHeap after settled vertex) graph size source vertex heads adjacency
      distance settled queue {layout with size := layout.size - 1} (remaining.erase vertex) := by
  have distanceSame : (settleHeap after settled vertex).read distance = before.read distance := by
    funext value
    simpa [settleHeap, Heap.read, Heap.write, invariant.storage.clientsSeparate] using
      extracted.otherArrays distance invariant.storage.distanceVertices invariant.storage.distancePositions value
  have settledSame (value : Int) : (settleHeap after settled vertex).read settled value =
      if value = vertex then 1 else before.read settled value := by
    simpa [settleHeap, Heap.read, Heap.write] using
      congrArg (fun x => if value = vertex then 1 else x)
        (extracted.otherArrays settled invariant.storage.settledVertices invariant.storage.settledPositions value)
  have settledPredicate : (fun value => (settleHeap after settled vertex).read settled value ≠ 0) =
      settleVertex (fun value => before.read settled value ≠ 0) vertex := by
    funext value
    rw [settledSame]
    apply propext
    by_cases same : value = vertex <;> simp [settleVertex, same]
  obtain ⟨unsettled, finite, minimum⟩ := invariant.matching.selected extracted
  refine ⟨invariant.storage.pop_settle extracted,
    invariant.matching.extract_and_settle extracted invariant.storage.clientsSeparate
      invariant.storage.distanceVertices invariant.storage.distancePositions
      invariant.storage.settledVertices invariant.storage.settledPositions invariant.storage.settledKeys,
    ?_, ?_, invariant.unique.erase vertex, ?_⟩
  · rw [distanceSame, settledPredicate]
    exact start_relaxation _ source vertex _ _ invariant.storage.graph.nonnegative_edges
      invariant.paths (by simp [unsettled]) finite (by simpa using minimum)
  · rw [distanceSame]
    exact invariant.finiteInRange
  · intro value
    rw [invariant.unique.mem_erase_iff, invariant.members, settledSame]
    by_cases same : value = vertex <;> simp [same]

/-- The adjacency scan restores the frontier without changing which vertices
    are settled, so the shortened remaining list is ready for the next extraction. -/
theorem ScanInvariant.finish {before after : Heap} {graph : Ref_Graph} {size source selected : Int}
    {heads : CollectionRef} {adjacency : Adjacency} {distance settled : SeqRef}
    {queue : Ref_MinHeap} {layout newLayout : Queue.Layout} {remaining : List Int}
    (invariant : ScanInvariant before graph size source selected heads adjacency distance settled queue layout remaining)
    (selectedNonnegative : 0 ≤ selected) (selectedBound : selected < size)
    (storage : StorageInvariant after graph size heads adjacency distance settled queue newLayout)
    (matching : QueueMatches after newLayout distance settled)
    (settledSame : ∀ vertex, after.read settled vertex = before.read settled vertex)
    (finiteInRange : ∀ vertex, 0 ≤ after.read distance vertex → 0 ≤ vertex ∧ vertex < size)
    (scan : RelaxScan (fun vertex => before.read settled vertex ≠ 0) selected (adjacency selected)
      (before.read distance) (after.read distance)) :
    LoopInvariant after graph size source heads adjacency distance settled queue newLayout remaining := by
  have settledFunctions : after.read settled = before.read settled := funext settledSame
  refine ⟨storage, matching, ?_, finiteInRange, invariant.unique, ?_⟩
  · rw [settledFunctions]
    exact scan.restores_frontier _ source selected _ (adjacency selected) _ _
      invariant.storage.graph.nonnegative_edges
      (by intro target weight; simp [representedEdges, selectedNonnegative, selectedBound]) invariant.paths
  · intro vertex
    rw [settledSame]
    exact invariant.members vertex




/-- A compositional budget for the five explicitly instrumented operations.
    `height` uniformly bounds the queue's binary-tree depth during the segment. -/
structure CostBounds (before after : Heap) (settlementBudget edgeBudget height : Nat) : Prop where
  settlements : Heap.cost before after "settlements" ≤ settlementBudget
  edges : Heap.cost before after "edges" ≤ edgeBudget
  improvements : Heap.cost before after "improvements" ≤ edgeBudget
  comparisons : Heap.cost before after "heap_comparisons" ≤
    2 * height * settlementBudget + (height + 1) * edgeBudget
  swaps : Heap.cost before after "heap_swaps" ≤
    (height + 1) * settlementBudget + height * edgeBudget
  otherClocks : ∀ name, name ≠ "settlements" → name ≠ "edges" → name ≠ "improvements" →
    name ≠ "heap_comparisons" → name ≠ "heap_swaps" → after.clocks name = before.clocks name

theorem CostBounds.refl (heap : Heap) (height : Nat) : CostBounds heap heap 0 0 height := by
  constructor <;> simp [Heap.cost]

/-- Initialization and bookkeeping writes may change storage without charging
    any operation counter. Their exact clock preservation supplies a zero budget. -/
theorem CostBounds.of_clocks_eq {before after : Heap} (same : after.clocks = before.clocks)
    (height : Nat) : CostBounds before after 0 0 height := by
  constructor <;> simp [Heap.cost, same]

/-- Upper bounds compose even though the delta representation uses natural
    subtraction. No clock-monotonicity side premise is needed here. -/
theorem CostBounds.trans {before middle after : Heap} {firstSettlements firstEdges secondSettlements secondEdges height : Nat}
    (first : CostBounds before middle firstSettlements firstEdges height)
    (second : CostBounds middle after secondSettlements secondEdges height) :
    CostBounds before after (firstSettlements + secondSettlements) (firstEdges + secondEdges) height := by
  constructor
  · exact cost_bound_compose _ _ _ _ _ _ first.settlements second.settlements
  · exact cost_bound_compose _ _ _ _ _ _ first.edges second.edges
  · exact cost_bound_compose _ _ _ _ _ _ first.improvements second.improvements
  · have bound := cost_bound_compose _ _ _ _ _ _ first.comparisons second.comparisons
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound
  · have bound := cost_bound_compose _ _ _ _ _ _ first.swaps second.swaps
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound
  · intro name notSettlements notEdges notImprovements notComparisons notSwaps
    exact (second.otherClocks name notSettlements notEdges notImprovements notComparisons notSwaps).trans
      (first.otherClocks name notSettlements notEdges notImprovements notComparisons notSwaps)

theorem CostBounds.weaken {before after : Heap} {settlements edges largerSettlements largerEdges height : Nat}
    (bound : CostBounds before after settlements edges height)
    (moreSettlements : settlements ≤ largerSettlements) (moreEdges : edges ≤ largerEdges) :
    CostBounds before after largerSettlements largerEdges height := by
  refine ⟨Nat.le_trans bound.settlements moreSettlements, Nat.le_trans bound.edges moreEdges,
    Nat.le_trans bound.improvements moreEdges, ?_, ?_, bound.otherClocks⟩
  · exact Nat.le_trans bound.comparisons (Nat.add_le_add
      (Nat.mul_le_mul_left _ moreSettlements) (Nat.mul_le_mul_left _ moreEdges))
  · exact Nat.le_trans bound.swaps (Nat.add_le_add
      (Nat.mul_le_mul_left _ moreSettlements) (Nat.mul_le_mul_left _ moreEdges))

/-- An inspected edge that does not improve a distance charges only one visit. -/
theorem skip_edge_cost (heap : Heap) (height : Nat) :
    CostBounds heap (heap.tick "edges") 0 1 height := by
  constructor
  · simp [Heap.cost, Heap.tick]
  · simp [Heap.cost, Heap.tick]
  · simp [Heap.cost, Heap.tick]
  · simp [Heap.cost, Heap.tick]
  · simp [Heap.cost, Heap.tick]
  · intro name _ notEdges _ _ _
    simp [Heap.tick, notEdges]

/-- A successful edge inspection includes its visit, distance write, proved
    insertion/decrease operation, and the final improvement tick. -/
theorem improved_edge_cost (heap after : Heap) (queue : Ref_MinHeap) (layout : Queue.Layout)
    (distance : SeqRef) (target candidate newSize maximum : Int)
    (updated : Queue.Updated (relaxationHeap heap distance target candidate) after
      queue layout target candidate newSize) (sizeBound : layout.size ≤ maximum) :
    CostBounds heap (after.tick "improvements") 0 1 (Queue.depth maximum) := by
  have depthBound := Queue.depth_mono sizeBound
  have comparisons := updated.comparisons
  have swaps := updated.swaps
  have settlements := updated.otherClocks "settlements" (by decide) (by decide)
  have edges := updated.otherClocks "edges" (by decide) (by decide)
  have improvements := updated.otherClocks "improvements" (by decide) (by decide)
  constructor
  · simp [Heap.cost, Heap.tick, settlements, relaxationHeap, Heap.write]
  · simp [Heap.cost, Heap.tick, edges, relaxationHeap, Heap.write]
  · simp [Heap.cost, Heap.tick, improvements, relaxationHeap, Heap.write]
  · simp [Heap.cost, relaxationHeap, Heap.tick, Heap.write] at comparisons ⊢
    omega
  · simp [Heap.cost, relaxationHeap, Heap.tick, Heap.write] at swaps ⊢
    omega
  · intro name _ notEdges notImprovements notComparisons notSwaps
    have same := updated.otherClocks name notComparisons notSwaps
    simp [Heap.tick, same, relaxationHeap, Heap.write, notEdges, notImprovements]

/-- Extraction and marking its returned vertex settled consume one vertex
    budget. The swap count includes the initial root/last exchange. -/
theorem extracted_settled_cost (heap after : Heap) (queue : Ref_MinHeap) (layout : Queue.Layout)
    (settled : SeqRef) (vertex maximum : Int)
    (extracted : Queue.Extracted heap after queue layout vertex) (sizeBound : layout.size ≤ maximum) :
    CostBounds heap (settleHeap after settled vertex) 1 0 (Queue.depth maximum) := by
  have depthBound : Queue.depth (layout.size - 2) ≤ Queue.depth maximum := Queue.depth_mono (by omega)
  have comparisons := extracted.comparisons
  have swaps := extracted.swaps
  have settlements := extracted.otherClocks "settlements" (by decide) (by decide)
  have edges := extracted.otherClocks "edges" (by decide) (by decide)
  have improvements := extracted.otherClocks "improvements" (by decide) (by decide)
  constructor
  · simp [Heap.cost, settleHeap, Heap.tick, Heap.write, settlements]
  · simp [Heap.cost, settleHeap, Heap.tick, Heap.write, edges]
  · simp [Heap.cost, settleHeap, Heap.tick, Heap.write, improvements]
  · simp [Heap.cost, settleHeap, Heap.tick, Heap.write] at comparisons ⊢
    omega
  · simp [Heap.cost, settleHeap, Heap.tick, Heap.write] at swaps ⊢
    omega
  · intro name notSettlements _ _ notComparisons notSwaps
    have same := extracted.otherClocks name notComparisons notSwaps
    simp [settleHeap, Heap.tick, Heap.write, same, notSettlements]



/-! A general finite adjacency scan, composed from source-level edge branches. -/

/-- Execution through one edge is reusable with any continuation at the next
    edge. It does not assume that the enclosing algorithm has already run. -/
def EdgeStepSummary (before after : Heap) (graph : Ref_Graph)
    (distance settled : SeqRef) (queue : Ref_MinHeap) (selected : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge) : Prop :=
  ∀ finalHeap result,
    (∀ state, AtEdges state after graph distance settled queue selected next →
      dijkstra.CallFrom state finalHeap result) →
    ∀ state, AtEdges state before graph distance settled queue selected (some edge) →
      dijkstra.CallFrom state finalHeap result

/-- A complete adjacency scan can continue at the outer extraction loop. -/
def EdgeScanSummary (before after : Heap) (graph : Ref_Graph)
    (distance settled : SeqRef) (queue : Ref_MinHeap) (selected : Int)
    (head : Option Ref_Edge) : Prop :=
  ∀ finalHeap result,
    (∀ state, AtExtraction state after graph distance settled queue →
      dijkstra.CallFrom state finalHeap result) →
    ∀ state, AtEdges state before graph distance settled queue selected head →
      dijkstra.CallFrom state finalHeap result

/-- The loop owns two client arrays and the three queue arrays. Queue sizes
    may change, but these sequence identities stay fixed throughout the run. -/
structure PrivateFrame (before after : Heap) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (initial final : Queue.Layout) : Prop where
  footprint : before.Footprint after (distance :: settled :: initial.refs) [queue] []
  refs : final.refs = initial.refs

namespace PrivateFrame

theorem refl (heap : Heap) (distance settled : SeqRef) (queue : Ref_MinHeap)
    (layout : Queue.Layout) : PrivateFrame heap heap distance settled queue layout layout :=
  ⟨Heap.Footprint.refl _ _ _ _, rfl⟩

theorem trans {before middle after : Heap} {distance settled : SeqRef}
    {queue : Ref_MinHeap} {first second third : Queue.Layout}
    (left : PrivateFrame before middle distance settled queue first second)
    (right : PrivateFrame middle after distance settled queue second third) :
    PrivateFrame before after distance settled queue first third := by
  refine ⟨left.footprint.trans ?_, right.refs.trans left.refs⟩
  simpa only [left.refs] using right.footprint

theorem queue {before after : Heap} {distance settled : SeqRef} {queue : Ref_MinHeap}
    {layout : Queue.Layout} (frame : before.Footprint after layout.refs [queue] [])
    (size : Int) : PrivateFrame before after distance settled queue layout {layout with size := size} :=
  ⟨frame.weaken (by intro ref member; simp [member]) (by simp) (by simp), rfl⟩

end PrivateFrame

/-- The logical and storage guarantees from one source edge. -/
structure EdgeAdvanced (before after : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (initialLayout layout : Queue.Layout) (selected target weight : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge) : Prop where
  storage : StorageInvariant after graph size heads adjacency distance settled queue layout
  matching : QueueMatches after layout distance settled
  settledSame : after.read settled = before.read settled
  finiteInRange : ∀ vertex, 0 ≤ after.read distance vertex → 0 ≤ vertex ∧ vertex < size
  scan : RelaxScan (fun vertex => before.read settled vertex ≠ 0) selected [(target, weight)]
    (before.read distance) (after.read distance)
  costs : CostBounds before after 0 1 (Queue.depth size)
  frame : GraphFrame before after graph heads
  execution : EdgeStepSummary before after graph distance settled queue selected edge next
  privateFrame : PrivateFrame before after distance settled queue initialLayout layout

/-- The completed scan preserves every invariant needed by the next extraction. -/
structure AdjacencyScanned (before after : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (initialLayout layout : Queue.Layout) (selected : Int)
    (head : Option Ref_Edge) (edges : List (Int × Int)) : Prop where
  storage : StorageInvariant after graph size heads adjacency distance settled queue layout
  matching : QueueMatches after layout distance settled
  settledSame : after.read settled = before.read settled
  finiteInRange : ∀ vertex, 0 ≤ after.read distance vertex → 0 ≤ vertex ∧ vertex < size
  scan : RelaxScan (fun vertex => before.read settled vertex ≠ 0) selected edges
    (before.read distance) (after.read distance)
  costs : CostBounds before after 0 edges.length (Queue.depth size)
  frame : GraphFrame before after graph heads
  execution : EdgeScanSummary before after graph distance settled queue selected head
  privateFrame : PrivateFrame before after distance settled queue initialLayout layout

/-- A queue whose finite distances stay within the graph has at most `size`
    active vertices, regardless of the values stored outside its active prefix. -/
theorem queue_bound_of_matching {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency} {distance settled : SeqRef}
    {queue : Ref_MinHeap} {layout : Queue.Layout}
    (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (matching : QueueMatches heap layout distance settled)
    (finiteInRange : ∀ vertex, 0 ≤ heap.read distance vertex → 0 ≤ vertex ∧ vertex < size) :
    layout.size ≤ size := by
  have bound := (queue_depth_bound heap queue layout storage.queue size
    (fun vertex present => finiteInRange vertex ((matching.membership vertex).mp present).2)).1
  have sizeNonnegative := storage.graph.sizeNonnegative
  omega

/-- Every edge branch terminates, preserves queue membership, and consumes
    one edge budget. A successful branch reuses the actual proved queue call. -/
theorem advance_edge (heap : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (layout : Queue.Layout) (selected target weight : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge)
    (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (matching : QueueMatches heap layout distance settled)
    (finiteInRange : ∀ vertex, 0 ≤ heap.read distance vertex → 0 ≤ vertex ∧ vertex < size)
    (selectedFinite : 0 ≤ heap.read distance selected)
    (validEdge : is_Edge heap edge)
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (readNext : field_Edge_next heap edge = some next)
    (targetLower : 0 ≤ target) (targetUpper : target < size) (weightLower : 0 ≤ weight) :
    ∃ after finalLayout, EdgeAdvanced heap after graph size heads adjacency distance settled
      queue layout finalLayout selected target weight edge next := by
  by_cases unsettled : heap.read settled target = 0
  · by_cases better : heap.read distance target < 0 ∨
        heap.read distance selected + weight < heap.read distance target
    · let candidate := heap.read distance selected + weight
      have candidateNonnegative : 0 ≤ candidate := by dsimp [candidate]; omega
      have relaxedStorage := storage.relaxation target candidate
      obtain ⟨after, newSize, insertion, updated⟩ := Queue.push_better_correct
        (relaxationHeap heap distance target candidate) queue layout relaxedStorage.queue target candidate (by
          intro present
          have oldPresent : 0 ≤ heap.read layout.positions target := by
            simpa [relaxationHeap, Heap.read, Heap.write, Ne.symm storage.distancePositions] using present
          have oldFinite := ((matching.membership target).mp oldPresent).2
          have oldKey := matching.keys target oldPresent
          have sameKey : (relaxationHeap heap distance target candidate).read layout.keys target =
              heap.read layout.keys target := by
            simp [relaxationHeap, Heap.read, Heap.write, Ne.symm storage.distanceKeys]
          rw [sameKey, oldKey]
          dsimp [candidate]
          omega)
      have distanceFinal : (after.tick "improvements").read distance =
          updateDistance (heap.read distance) target candidate := by
        funext vertex
        exact updated.distance_updated storage vertex
      have settledFinal : (after.tick "improvements").read settled = heap.read settled := by
        funext vertex
        exact updated.settled_updated storage vertex
      have frame := updated.graph_updated graph heads
      refine ⟨after.tick "improvements", { layout with size := newSize },
        storage.improved updated, matching.improved storage updated unsettled candidateNonnegative,
        settledFinal, ?_, ?_, ?_, frame, ?_, ?_⟩
      · intro vertex finite
        rw [distanceFinal] at finite
        by_cases same : vertex = target
        · simpa [same] using And.intro targetLower targetUpper
        · apply finiteInRange vertex
          simpa [updateDistance, same] using finite
      · rw [distanceFinal, ← relax_distance_improves (heap.read distance) target candidate better]
        exact .relax (by simpa using unsettled) (.empty _)
      · exact improved_edge_cost heap after queue layout distance target candidate newSize size
          updated (queue_bound_of_matching storage matching finiteInRange)
      · intro finalHeap result continuation state located
        apply improve_edge_continue state heap after finalHeap graph distance settled result queue
          selected target weight edge next located storage.distanceAllocated storage.settledAllocated
          readTarget readWeight unsettled better insertion
        · exact ((frame.edges edge validEdge).2.2.2).trans readNext
        · exact continuation
      · refine ⟨?_, rfl⟩
        have initial := ((Heap.Footprint.refl heap (distance :: settled :: layout.refs) [queue] []).tick
          "edges").write distance target candidate (by simp)
        exact (initial.trans (updated.footprint.weaken (by intro ref member; simp [member]) (by simp) (by simp))).tick "improvements"
    · have finite : 0 ≤ heap.read distance target := by omega
      have noBetter : heap.read distance target ≤ heap.read distance selected + weight := by omega
      refine ⟨heap.tick "edges", layout, storage.tick "edges", matching.tick "edges",
        rfl, finiteInRange, ?_, skip_edge_cost heap (Queue.depth size),
        graph_frame_tick heap graph heads "edges" 1, ?_,
        ⟨(Heap.Footprint.refl heap _ _ _).tick "edges", rfl⟩⟩
      · have scan : RelaxScan (fun vertex => heap.read settled vertex ≠ 0) selected [(target, weight)]
          (heap.read distance) (heap.read distance) := by
          apply RelaxScan.relax (by simpa using unsettled)
          rw [relax_distance_unchanged (heap.read distance) target
            (heap.read distance selected + weight) finite noBetter]
          exact .empty _
        exact scan
      · intro finalHeap result continuation state located
        exact unimproved_edge_continue state heap finalHeap graph distance settled result queue
          selected target weight edge next located storage.distanceAllocated storage.settledAllocated
          readTarget readWeight unsettled finite noBetter readNext continuation
  · refine ⟨heap.tick "edges", layout, storage.tick "edges", matching.tick "edges",
      rfl, finiteInRange, RelaxScan.skip unsettled (.empty _), skip_edge_cost heap (Queue.depth size),
      graph_frame_tick heap graph heads "edges" 1, ?_,
        ⟨(Heap.Footprint.refl heap _ _ _).tick "edges", rfl⟩⟩
    intro finalHeap result continuation state located
    exact settled_edge_continue state heap finalHeap graph distance settled result queue
      selected target edge next located storage.settledAllocated readTarget unsettled readNext continuation

/-- Every finite represented adjacency list admits a complete compiled scan.
    The theorem handles represented queues, graph sharing, and prior clock values. -/
theorem scan_adjacency (heap : Heap) (graph : Ref_Graph) (size : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (layout : Queue.Layout) (selected : Int)
    (head : Option Ref_Edge) (edges : List (Int × Int))
    (storage : StorageInvariant heap graph size heads adjacency distance settled queue layout)
    (matching : QueueMatches heap layout distance settled)
    (finiteInRange : ∀ vertex, 0 ≤ heap.read distance vertex → 0 ≤ vertex ∧ vertex < size)
    (selectedSettled : heap.read settled selected ≠ 0)
    (selectedFinite : 0 ≤ heap.read distance selected)
    (chain : AdjacencyChain heap size head edges) :
    ∃ after finalLayout, AdjacencyScanned heap after graph size heads adjacency distance settled
      queue layout finalLayout selected head edges := by
  induction edges generalizing heap head layout with
  | nil =>
    have empty := chain.empty_iff.mpr rfl
    subst head
    refine ⟨heap, layout, storage, matching, rfl, finiteInRange,
      RelaxScan.empty _, CostBounds.refl heap (Queue.depth size), GraphFrame.refl heap graph heads, ?_,
      PrivateFrame.refl heap distance settled queue layout⟩
    intro finalHeap result continuation state located
    exact empty_edges_continue state heap finalHeap graph distance settled result queue selected located continuation
  | cons pair rest ih =>
    cases chain with
    | cons edge target weight next tail valid readTarget readWeight readNext lower upper nonnegative remaining =>
      obtain ⟨middle, middleLayout, advanced⟩ := advance_edge heap graph size heads adjacency distance settled queue
        layout selected target weight edge next storage matching finiteInRange selectedFinite
        valid readTarget readWeight readNext lower upper nonnegative
      have selectedSame := RelaxScan.selected_unchanged _ selected [(target, weight)]
        (heap.read distance) (middle.read distance) selectedSettled advanced.scan
      obtain ⟨after, finalLayout, scanned⟩ := ih middle middleLayout next advanced.storage advanced.matching
        advanced.finiteInRange (by rw [advanced.settledSame]; exact selectedSettled)
        (by rw [selectedSame]; exact selectedFinite) (remaining.preserved advanced.frame.edges)
      refine ⟨after, finalLayout, scanned.storage, scanned.matching,
        scanned.settledSame.trans advanced.settledSame, scanned.finiteInRange, ?_, ?_,
        advanced.frame.trans scanned.frame, ?_, advanced.privateFrame.trans scanned.privateFrame⟩
      · have tailScan := scanned.scan
        rw [advanced.settledSame] at tailScan
        exact advanced.scan.append tailScan
      · simpa [Nat.add_comm] using advanced.costs.trans scanned.costs
      · intro finalHeap result continuation state located
        apply advanced.execution finalHeap result _ state located
        intro nextState nextLocated
        exact scanned.execution finalHeap result continuation nextState nextLocated



/-- The complete remainder of an extraction loop, with a mathematical result,
    a finite work budget, and an execution summary usable under any caller. -/
structure ExtractionCompleted (before after : Heap) (graphRef : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (remaining : List Int) (layout : Queue.Layout) : Prop where
  graph : GraphRep after graphRef size heads adjacency
  search : ∃ vertices,
    SearchRun (representedEdges size adjacency) adjacency (before.read distance)
      (fun vertex => before.read settled vertex ≠ 0) (after.read distance) vertices ∧
    ∀ vertex ∈ vertices, vertex ∈ remaining
  canonical : ∀ vertex, after.read distance vertex < 0 → after.read distance vertex = -1
  finiteInRange : ∀ vertex, 0 ≤ after.read distance vertex → 0 ≤ vertex ∧ vertex < size
  costs : CostBounds before after remaining.length (edgeBudget adjacency remaining) (Queue.depth size)
  execution : ∀ state, AtExtraction state before graphRef distance settled queue →
    dijkstra.CallFrom state after distance
  footprint : before.Footprint after (distance :: settled :: layout.refs) [queue] []

/-- General correctness, termination, and runtime of the actual extraction
    loop. Each nonempty iteration consumes one remaining graph vertex. -/
theorem extraction_loop_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (distance settled : SeqRef)
    (queue : Ref_MinHeap) (layout : Queue.Layout) (remaining : List Int)
    (invariant : LoopInvariant heap graph size source heads adjacency distance settled queue layout remaining) :
    ∃ after, ExtractionCompleted heap after graph size source heads adjacency distance settled queue remaining layout := by
  let api : Algo2Lean.Dijkstra.Execution.Interface (Heap × Queue.Layout) := {
    distance := fun state => state.1.read distance
    settled := fun state vertex => state.1.read settled vertex ≠ 0
    invariant := fun state pending => LoopInvariant state.1 graph size source heads adjacency
      distance settled queue state.2 pending
    completion := fun before after => ∀ state,
      AtExtraction state before.1 graph distance settled queue →
      dijkstra.CallFrom state after.1 distance
    accounting := fun before after vertices edges =>
      CostBounds before.1 after.1 vertices edges (Queue.depth size) ∧
        PrivateFrame before.1 after.1 distance settled queue before.2 after.2
    zero := fun state => ⟨CostBounds.refl state.1 (Queue.depth size),
      PrivateFrame.refl state.1 distance settled queue state.2⟩
    compose := fun first second => ⟨first.1.trans second.1, first.2.trans second.2⟩
    weaken := fun costs vertices edges => ⟨costs.1.weaken vertices edges, costs.2⟩ }
  have progress : ∀ state pending, api.invariant state pending →
      Algo2Lean.Dijkstra.Execution.Progress api (representedEdges size adjacency) adjacency state pending := by
    rintro ⟨before, current⟩ pending invariant
    change LoopInvariant before graph size source heads adjacency distance settled queue current pending
      at invariant
    by_cases empty : current.size = 0
    · apply Algo2Lean.Dijkstra.Execution.Progress.done
      · intro vertex unsettled
        exact invariant.matching.exhausted invariant.storage.queue empty vertex (by simpa [api] using unsettled)
      · intro state located
        apply extraction_done state before graph distance settled queue located
        · simpa [empty] using invariant.storage.queue.valid.readSize
        · exact invariant.storage.distanceAllocated
    · have positive : 0 < current.size := by
        have nonnegative := invariant.storage.queue.nonnegative
        omega
      obtain ⟨popped, pop, extracted⟩ := Queue.pop_correct before queue current invariant.storage.queue positive
      let selected := before.read current.vertices 0
      have selectedMember : selected ∈ pending := invariant.selected_member extracted
      have selectedFacts := invariant.matching.selected extracted
      obtain ⟨selectedLower, selectedUpper⟩ := invariant.finiteInRange selected selectedFacts.2.1
      have scanning := invariant.begin_scan extracted
      obtain ⟨head, readHead, chain⟩ := scanning.storage.graph.chains selected selectedLower selectedUpper
      obtain ⟨scanned, newLayout, scan⟩ := scan_adjacency (settleHeap popped settled selected)
        graph size heads adjacency distance settled queue {current with size := current.size - 1}
        selected head (adjacency selected) scanning.storage scanning.matching scanning.finiteInRange
        scanning.paths.selectedSettled (scanning.paths.settledFinite selected scanning.paths.selectedSettled) chain
      have next := scanning.finish selectedLower selectedUpper scan.storage scan.matching
        (fun vertex => congrFun scan.settledSame vertex) scan.finiteInRange scan.scan
      have sizeBound := queue_bound_of_matching invariant.storage invariant.matching invariant.finiteInRange
      have extractionCost := extracted_settled_cost before popped queue current settled selected size extracted sizeBound
      have distances : (settleHeap popped settled selected).read distance = before.read distance := by
        funext vertex
        simpa [settleHeap, Heap.read, Heap.write, invariant.storage.clientsSeparate] using
          extracted.otherArrays distance invariant.storage.distanceVertices invariant.storage.distancePositions vertex
      have settledValues (vertex : Int) : (settleHeap popped settled selected).read settled vertex =
          if vertex = selected then 1 else before.read settled vertex := by
        simpa [settleHeap, Heap.read, Heap.write] using
          congrArg (fun x => if vertex = selected then 1 else x)
            (extracted.otherArrays settled invariant.storage.settledVertices invariant.storage.settledPositions vertex)
      have settledPredicate : (fun vertex => (settleHeap popped settled selected).read settled vertex ≠ 0) =
          settleVertex (fun vertex => before.read settled vertex ≠ 0) selected := by
        funext vertex
        rw [settledValues]
        apply propext
        by_cases same : vertex = selected <;> simp [settleVertex, same]
      apply Algo2Lean.Dijkstra.Execution.Progress.next (after := (scanned, newLayout)) (selected := selected)
      refine ⟨selectedMember, next, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨by simpa [api] using selectedFacts.1, selectedFacts.2.1, by simpa [api] using selectedFacts.2.2⟩
      · intro target weight
        simp [representedEdges, selectedLower, selectedUpper]
      · have scannedRun := scan.scan
        rw [distances, settledPredicate] at scannedRun
        exact scannedRun
      · change (fun vertex => scanned.read settled vertex ≠ 0) = _
        rw [scan.settledSame, settledPredicate]
      · intro final continuation state located
        apply extraction_to_edges state before popped final.1 graph distance settled distance queue
          selected current.size heads head located invariant.storage.queue.valid.readSize positive pop
          (invariant.storage.extracted extracted).settledAllocated scanning.storage.graph.readHeads readHead
        intro edgeState edgeLocated
        exact scan.execution final.1 distance continuation edgeState edgeLocated
      · refine ⟨?_, ?_⟩
        · simpa using extractionCost.trans scan.costs
        · have poppedFrame : PrivateFrame before (settleHeap popped settled selected)
              distance settled queue current {current with size := current.size - 1} := by
            refine ⟨?_, rfl⟩
            exact ((extracted.footprint.weaken (by intro ref member; simp [member]) (by simp) (by simp)).write
              settled selected 1 (by simp)).tick "settlements"
          exact poppedFrame.trans scan.privateFrame
  obtain ⟨⟨after, finalLayout⟩, completed⟩ := Algo2Lean.Dijkstra.Execution.run api
    (representedEdges size adjacency) adjacency progress (heap, layout) remaining invariant
  obtain ⟨pending, finalInvariant⟩ := completed.invariant
  change LoopInvariant after graph size source heads adjacency distance settled queue finalLayout pending
    at finalInvariant
  exact ⟨after, finalInvariant.storage.graph, completed.search, finalInvariant.paths.unknown,
    finalInvariant.finiteInRange, completed.cost.1, completed.execution, completed.cost.2.footprint⟩


-- The private next-configuration function certifies determinism. The transition
-- theorem checks that every compiled instruction produces that configuration.
namespace Determinism
private def next_MinHeap___init__ (h : Heap) (s : State_MinHeap___init__) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap___init__ (s.t1)) stack)
  | 2 => (.active h (Frame.fn_MinHeap___init__ 1 { s with t1 := () }) stack)
  | 3 => (.active (set_MinHeap_size h (s.v0) ((0 : Int))) (Frame.fn_MinHeap___init__ 2 s) stack)
  | 4 => (.active (set_MinHeap_keys h (s.t3) (s.t2)) (Frame.fn_MinHeap___init__ 3 s) stack)
  | 5 => (.active h (Frame.fn_MinHeap___init__ 4 { s with t3 := s.v0 }) stack)
  | 6 => (.active (h.allocate (fun _ => s.t4)) (Frame.fn_MinHeap___init__ 5 { s with t2 := h.nextRef }) stack)
  | 7 => (.active h (Frame.fn_MinHeap___init__ 6 { s with t4 := (0 : Int) }) stack)
  | 8 => (.active (set_MinHeap_positions h (s.t6) (s.t5)) (Frame.fn_MinHeap___init__ 7 s) stack)
  | 9 => (.active h (Frame.fn_MinHeap___init__ 8 { s with t6 := s.v0 }) stack)
  | 10 => (.active (h.allocate (fun _ => s.t7)) (Frame.fn_MinHeap___init__ 9 { s with t5 := h.nextRef }) stack)
  | 11 => (.active h (Frame.fn_MinHeap___init__ 10 { s with t7 := (-(1 : Int)) }) stack)
  | 12 => (.active (set_MinHeap_vertices h (s.t9) (s.t8)) (Frame.fn_MinHeap___init__ 11 s) stack)
  | 13 => (.active h (Frame.fn_MinHeap___init__ 12 { s with t9 := s.v0 }) stack)
  | 14 => (.active (h.allocate (fun _ => s.t10)) (Frame.fn_MinHeap___init__ 13 { s with t8 := h.nextRef }) stack)
  | 15 => (.active h (Frame.fn_MinHeap___init__ 14 { s with t10 := (0 : Int) }) stack)
  | pc => .active h (.fn_MinHeap___init__ pc s) stack
private def next_MinHeap_swap (h : Heap) (s : State_MinHeap_swap) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_swap (s.t5)) stack)
  | 2 => (.active h (Frame.fn_MinHeap_swap 1 { s with t5 := () }) stack)
  | 3 => (.active (h.tick "heap_swaps" 1) (Frame.fn_MinHeap_swap 2 s) stack)
  | 4 => (.active (h.write ((field_MinHeap_positions h (s.v0)).getD 0) s.v4 s.v1) (Frame.fn_MinHeap_swap 3 s) stack)
  | 5 => (.active (h.write ((field_MinHeap_positions h (s.v0)).getD 0) s.v3 s.v2) (Frame.fn_MinHeap_swap 4 s) stack)
  | 6 => (.active (h.write ((field_MinHeap_vertices h (s.v0)).getD 0) s.v2 s.v3) (Frame.fn_MinHeap_swap 5 s) stack)
  | 7 => (.active (h.write ((field_MinHeap_vertices h (s.v0)).getD 0) s.v1 s.v4) (Frame.fn_MinHeap_swap 6 s) stack)
  | 8 => (.active h (Frame.fn_MinHeap_swap 7 { s with v4 := (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v2) }) stack)
  | 9 => (.active h (Frame.fn_MinHeap_swap 8 { s with v3 := (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v1) }) stack)
  | pc => .active h (.fn_MinHeap_swap pc s) stack
private def next_MinHeap_sift_up (h : Heap) (s : State_MinHeap_sift_up) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_sift_up (s.t3)) stack)
  | 2 => (.active h (Frame.fn_MinHeap_sift_up 1 { s with t3 := () }) stack)
  | 3 => if s.t4 then (.active h (Frame.fn_MinHeap_sift_up 16 s) stack) else (.active h (Frame.fn_MinHeap_sift_up 2 s) stack)
  | 4 => (.active h (Frame.fn_MinHeap_sift_up 3 { s with t4 := (decide ((s.v1 > (0 : Int)))) }) stack)
  | 5 => (.active h (Frame.fn_MinHeap_sift_up 4 { s with v1 := s.v2 }) stack)
  | 6 => (.active h (Frame.fn_MinHeap_swap 9 ({ v0 := (s.t6), v1 := s.t7, v2 := s.t8 } : State_MinHeap_swap)) ((fun value => match value with | .fn_MinHeap_swap result => (Frame.fn_MinHeap_sift_up 5 { s with t5 := result }) | _ => .invalid) :: stack))
  | 7 => (.active h (Frame.fn_MinHeap_sift_up 6 { s with t8 := s.v2 }) stack)
  | 8 => (.active h (Frame.fn_MinHeap_sift_up 7 { s with t7 := s.v1 }) stack)
  | 9 => (.active h (Frame.fn_MinHeap_sift_up 8 { s with t6 := s.t6 }) stack)
  | 10 => (.active h (Frame.fn_MinHeap_sift_up 9 { s with t6 := s.v0 }) stack)
  | 11 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_sift_up (s.t10)) stack)
  | 12 => (.active h (Frame.fn_MinHeap_sift_up 11 { s with t10 := () }) stack)
  | 13 => if s.t9 then (.active h (Frame.fn_MinHeap_sift_up 12 s) stack) else (.active h (Frame.fn_MinHeap_sift_up 10 s) stack)
  | 14 => (.active h (Frame.fn_MinHeap_sift_up 13 { s with t9 := (decide (((h.read ((field_MinHeap_keys h (s.v0)).getD 0) (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v2)) ≤ (h.read ((field_MinHeap_keys h (s.v0)).getD 0) (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v1))))) }) stack)
  | 15 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_MinHeap_sift_up 14 s) stack)
  | 16 => (.active h (Frame.fn_MinHeap_sift_up 15 { s with v2 := (Int.fdiv (s.v1 - (1 : Int)) (2 : Int)) }) stack)
  | pc => .active h (.fn_MinHeap_sift_up pc s) stack
private def next_MinHeap_sift_down (h : Heap) (s : State_MinHeap_sift_down) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_sift_down (s.t4)) stack)
  | 2 => (.active h (Frame.fn_MinHeap_sift_down 1 { s with t4 := () }) stack)
  | 3 => if s.t5 then (.active h (Frame.fn_MinHeap_sift_down 23 s) stack) else (.active h (Frame.fn_MinHeap_sift_down 2 s) stack)
  | 4 => (.active h (Frame.fn_MinHeap_sift_down 3 { s with t5 := (decide (((((2 : Int) * s.v1) + (1 : Int)) < ((field_MinHeap_size h (s.v0)).getD 0)))) }) stack)
  | 5 => (.active h (Frame.fn_MinHeap_sift_down 4 { s with v1 := s.v2 }) stack)
  | 6 => (.active h (Frame.fn_MinHeap_swap 9 ({ v0 := (s.t7), v1 := s.t8, v2 := s.t9 } : State_MinHeap_swap)) ((fun value => match value with | .fn_MinHeap_swap result => (Frame.fn_MinHeap_sift_down 5 { s with t6 := result }) | _ => .invalid) :: stack))
  | 7 => (.active h (Frame.fn_MinHeap_sift_down 6 { s with t9 := s.v2 }) stack)
  | 8 => (.active h (Frame.fn_MinHeap_sift_down 7 { s with t8 := s.v1 }) stack)
  | 9 => (.active h (Frame.fn_MinHeap_sift_down 8 { s with t7 := s.t7 }) stack)
  | 10 => (.active h (Frame.fn_MinHeap_sift_down 9 { s with t7 := s.v0 }) stack)
  | 11 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_sift_down (s.t11)) stack)
  | 12 => (.active h (Frame.fn_MinHeap_sift_down 11 { s with t11 := () }) stack)
  | 13 => if s.t10 then (.active h (Frame.fn_MinHeap_sift_down 12 s) stack) else (.active h (Frame.fn_MinHeap_sift_down 10 s) stack)
  | 14 => (.active h (Frame.fn_MinHeap_sift_down 13 { s with t10 := (decide (((h.read ((field_MinHeap_keys h (s.v0)).getD 0) (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v1)) ≤ (h.read ((field_MinHeap_keys h (s.v0)).getD 0) (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v2))))) }) stack)
  | 15 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_MinHeap_sift_down 14 s) stack)
  | 16 => (.active h (Frame.fn_MinHeap_sift_down 15 { s with v2 := s.v3 }) stack)
  | 17 => if s.t13 then (.active h (Frame.fn_MinHeap_sift_down 16 s) stack) else (.active h (Frame.fn_MinHeap_sift_down 15 s) stack)
  | 18 => (.active h (Frame.fn_MinHeap_sift_down 17 { s with t13 := (decide (((h.read ((field_MinHeap_keys h (s.v0)).getD 0) (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v3)) < (h.read ((field_MinHeap_keys h (s.v0)).getD 0) (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) s.v2))))) }) stack)
  | 19 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_MinHeap_sift_down 18 s) stack)
  | 20 => if s.t12 then (.active h (Frame.fn_MinHeap_sift_down 19 s) stack) else (.active h (Frame.fn_MinHeap_sift_down 15 s) stack)
  | 21 => (.active h (Frame.fn_MinHeap_sift_down 20 { s with t12 := (decide ((s.v3 < ((field_MinHeap_size h (s.v0)).getD 0)))) }) stack)
  | 22 => (.active h (Frame.fn_MinHeap_sift_down 21 { s with v3 := (s.v2 + (1 : Int)) }) stack)
  | 23 => (.active h (Frame.fn_MinHeap_sift_down 22 { s with v2 := (((2 : Int) * s.v1) + (1 : Int)) }) stack)
  | pc => .active h (.fn_MinHeap_sift_down pc s) stack
private def next_MinHeap_push_or_decrease (h : Heap) (s : State_MinHeap_push_or_decrease) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_push_or_decrease (s.t4)) stack)
  | 2 => (.active h (Frame.fn_MinHeap_push_or_decrease 1 { s with t4 := () }) stack)
  | 3 => (.active h (Frame.fn_MinHeap_sift_up 4 ({ v0 := (s.t7), v1 := s.t8 } : State_MinHeap_sift_up)) ((fun value => match value with | .fn_MinHeap_sift_up result => (Frame.fn_MinHeap_push_or_decrease 2 { s with t6 := result }) | _ => .invalid) :: stack))
  | 4 => (.active h (Frame.fn_MinHeap_push_or_decrease 3 { s with t8 := s.v3 }) stack)
  | 5 => (.active h (Frame.fn_MinHeap_push_or_decrease 4 { s with t7 := s.t7 }) stack)
  | 6 => (.active h (Frame.fn_MinHeap_push_or_decrease 5 { s with t7 := s.v0 }) stack)
  | 7 => (.active (set_MinHeap_size h (s.t9) ((s.t10 + s.t11))) (Frame.fn_MinHeap_push_or_decrease 6 s) stack)
  | 8 => (.active h (Frame.fn_MinHeap_push_or_decrease 7 { s with t11 := (1 : Int) }) stack)
  | 9 => (.active h (Frame.fn_MinHeap_push_or_decrease 8 { s with t10 := ((field_MinHeap_size h (s.t9)).getD 0) }) stack)
  | 10 => (.active h (Frame.fn_MinHeap_push_or_decrease 9 { s with t9 := s.v0 }) stack)
  | 11 => (.active (h.write ((field_MinHeap_positions h (s.v0)).getD 0) s.v1 s.v3) (Frame.fn_MinHeap_push_or_decrease 10 s) stack)
  | 12 => (.active (h.write ((field_MinHeap_vertices h (s.v0)).getD 0) s.v3 s.v1) (Frame.fn_MinHeap_push_or_decrease 11 s) stack)
  | 13 => (.active h (Frame.fn_MinHeap_push_or_decrease 12 { s with v3 := ((field_MinHeap_size h (s.v0)).getD 0) }) stack)
  | 14 => (.active (h.write ((field_MinHeap_keys h (s.v0)).getD 0) s.v1 s.v2) (Frame.fn_MinHeap_push_or_decrease 13 s) stack)
  | 15 => (.active h (Frame.fn_MinHeap_sift_up 4 ({ v0 := (s.t14), v1 := s.t15 } : State_MinHeap_sift_up)) ((fun value => match value with | .fn_MinHeap_sift_up result => (Frame.fn_MinHeap_push_or_decrease 2 { s with t13 := result }) | _ => .invalid) :: stack))
  | 16 => (.active h (Frame.fn_MinHeap_push_or_decrease 15 { s with t15 := s.v3 }) stack)
  | 17 => (.active h (Frame.fn_MinHeap_push_or_decrease 16 { s with t14 := s.t14 }) stack)
  | 18 => (.active h (Frame.fn_MinHeap_push_or_decrease 17 { s with t14 := s.v0 }) stack)
  | 19 => (.active (h.write ((field_MinHeap_keys h (s.v0)).getD 0) s.v1 s.v2) (Frame.fn_MinHeap_push_or_decrease 18 s) stack)
  | 20 => if s.t12 then (.active h (Frame.fn_MinHeap_push_or_decrease 19 s) stack) else (.active h (Frame.fn_MinHeap_push_or_decrease 2 s) stack)
  | 21 => (.active h (Frame.fn_MinHeap_push_or_decrease 20 { s with t12 := (decide ((s.v2 < (h.read ((field_MinHeap_keys h (s.v0)).getD 0) s.v1)))) }) stack)
  | 22 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_MinHeap_push_or_decrease 21 s) stack)
  | 23 => if s.t5 then (.active h (Frame.fn_MinHeap_push_or_decrease 14 s) stack) else (.active h (Frame.fn_MinHeap_push_or_decrease 22 s) stack)
  | 24 => (.active h (Frame.fn_MinHeap_push_or_decrease 23 { s with t5 := (decide ((s.v3 < (0 : Int)))) }) stack)
  | 25 => (.active h (Frame.fn_MinHeap_push_or_decrease 24 { s with v3 := (h.read ((field_MinHeap_positions h (s.v0)).getD 0) s.v1) }) stack)
  | pc => .active h (.fn_MinHeap_push_or_decrease pc s) stack
private def next_MinHeap_pop_min (h : Heap) (s : State_MinHeap_pop_min) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_pop_min (s.t3)) stack)
  | 2 => (.active h (Frame.fn_MinHeap_pop_min 1 { s with t3 := s.v1 }) stack)
  | 3 => (.active h (Frame.fn_MinHeap_sift_down 4 ({ v0 := (s.t6), v1 := s.t7 } : State_MinHeap_sift_down)) ((fun value => match value with | .fn_MinHeap_sift_down result => (Frame.fn_MinHeap_pop_min 2 { s with t5 := result }) | _ => .invalid) :: stack))
  | 4 => (.active h (Frame.fn_MinHeap_pop_min 3 { s with t7 := (0 : Int) }) stack)
  | 5 => (.active h (Frame.fn_MinHeap_pop_min 4 { s with t6 := s.t6 }) stack)
  | 6 => (.active h (Frame.fn_MinHeap_pop_min 5 { s with t6 := s.v0 }) stack)
  | 7 => if s.t4 then (.active h (Frame.fn_MinHeap_pop_min 6 s) stack) else (.active h (Frame.fn_MinHeap_pop_min 2 s) stack)
  | 8 => (.active h (Frame.fn_MinHeap_pop_min 7 { s with t4 := (decide ((s.v2 > (0 : Int)))) }) stack)
  | 9 => (.active (h.write ((field_MinHeap_positions h (s.v0)).getD 0) s.v1 (-(1 : Int))) (Frame.fn_MinHeap_pop_min 8 s) stack)
  | 10 => (.active (set_MinHeap_size h (s.v0) (s.v2)) (Frame.fn_MinHeap_pop_min 9 s) stack)
  | 11 => (.active h (Frame.fn_MinHeap_swap 9 ({ v0 := (s.t9), v1 := s.t10, v2 := s.t11 } : State_MinHeap_swap)) ((fun value => match value with | .fn_MinHeap_swap result => (Frame.fn_MinHeap_pop_min 10 { s with t8 := result }) | _ => .invalid) :: stack))
  | 12 => (.active h (Frame.fn_MinHeap_pop_min 11 { s with t11 := s.v2 }) stack)
  | 13 => (.active h (Frame.fn_MinHeap_pop_min 12 { s with t10 := (0 : Int) }) stack)
  | 14 => (.active h (Frame.fn_MinHeap_pop_min 13 { s with t9 := s.t9 }) stack)
  | 15 => (.active h (Frame.fn_MinHeap_pop_min 14 { s with t9 := s.v0 }) stack)
  | 16 => (.active h (Frame.fn_MinHeap_pop_min 15 { s with v2 := (((field_MinHeap_size h (s.v0)).getD 0) - (1 : Int)) }) stack)
  | 17 => (.active h (Frame.fn_MinHeap_pop_min 16 { s with v1 := (h.read ((field_MinHeap_vertices h (s.v0)).getD 0) (0 : Int)) }) stack)
  | 18 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap_pop_min (s.t13)) stack)
  | 19 => (.active h (Frame.fn_MinHeap_pop_min 18 { s with t13 := (-(1 : Int)) }) stack)
  | 20 => if s.t12 then (.active h (Frame.fn_MinHeap_pop_min 19 s) stack) else (.active h (Frame.fn_MinHeap_pop_min 17 s) stack)
  | 21 => (.active h (Frame.fn_MinHeap_pop_min 20 { s with t12 := (decide ((((field_MinHeap_size h (s.v0)).getD 0) ≤ (0 : Int)))) }) stack)
  | pc => .active h (.fn_MinHeap_pop_min pc s) stack
private def next_MinHeap_is_empty (h : Heap) (s : State_MinHeap_is_empty) (stack : Stack) : Nat → Configuration
  | 1 => resumeConfig h (.fn_MinHeap_is_empty s.t1) stack
  | 2 => .active h (.fn_MinHeap_is_empty 1 { s with t1 := decide ((field_MinHeap_size h s.v0).getD 0 ≤ 0) }) stack
  | pc => .active h (.fn_MinHeap_is_empty pc s) stack

private def next_Edge___init__ (h : Heap) (s : State_Edge___init__) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_Edge___init__ (s.t4)) stack)
  | 2 => (.active h (Frame.fn_Edge___init__ 1 { s with t4 := () }) stack)
  | 3 => (.active (set_Edge_next h (s.v0) (s.v3)) (Frame.fn_Edge___init__ 2 s) stack)
  | 4 => (.active (set_Edge_weight h (s.v0) (s.v2)) (Frame.fn_Edge___init__ 3 s) stack)
  | 5 => (.active (set_Edge_target h (s.v0) (s.v1)) (Frame.fn_Edge___init__ 4 s) stack)
  | pc => .active h (.fn_Edge___init__ pc s) stack
private def next_Graph___init__ (h : Heap) (s : State_Graph___init__) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_Graph___init__ (s.t2)) stack)
  | 2 => (.active h (Frame.fn_Graph___init__ 1 { s with t2 := () }) stack)
  | 3 => (.active (set_Graph_heads h (s.t4) (s.t3)) (Frame.fn_Graph___init__ 2 s) stack)
  | 4 => (.active h (Frame.fn_Graph___init__ 3 { s with t4 := s.v0 }) stack)
  | 5 => (.active (seq_Edge_optional.const h s.t5).1 (Frame.fn_Graph___init__ 4 { s with t3 := h.nextCollection }) stack)
  | 6 => (.active h (Frame.fn_Graph___init__ 5 { s with t5 := none }) stack)
  | 7 => (.active (set_Graph_size h (s.v0) ((0 : Int))) (Frame.fn_Graph___init__ 6 s) stack)
  | 8 => if s.t6 then (.active h (Frame.fn_Graph___init__ 7 s) stack) else (.active h (Frame.fn_Graph___init__ 6 s) stack)
  | 9 => (.active h (Frame.fn_Graph___init__ 8 { s with t6 := (decide ((s.v1 < (0 : Int)))) }) stack)
  | 10 => (.active (set_Graph_size h (s.v0) (s.v1)) (Frame.fn_Graph___init__ 9 s) stack)
  | pc => .active h (.fn_Graph___init__ pc s) stack
private def next_Graph_add_edge (h : Heap) (s : State_Graph_add_edge) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_Graph_add_edge (s.t4)) stack)
  | 2 => (.active h (Frame.fn_Graph_add_edge 1 { s with t4 := true }) stack)
  | 3 => (.active (seq_Edge_optional.set h s.t7 s.t6 s.t5) (Frame.fn_Graph_add_edge 2 s) stack)
  | 4 => (.active h (Frame.fn_Graph_add_edge 3 { s with t6 := s.v1 }) stack)
  | 5 => (.active h (Frame.fn_Graph_add_edge 4 { s with t7 := ((field_Graph_heads h (s.v0)).getD 0) }) stack)
  | 6 => (.active h (Frame.fn_Edge 9 ({ v0 := s.t8, v1 := s.t9, v2 := s.t10 } : State_Edge)) ((fun value => match value with | .fn_Edge result => (Frame.fn_Graph_add_edge 5 { s with t5 := (some result) }) | _ => .invalid) :: stack))
  | 7 => (.active h (Frame.fn_Graph_add_edge 6 { s with t10 := ((seq_Edge_optional.get h ((field_Graph_heads h (s.v0)).getD 0) s.v1).getD none) }) stack)
  | 8 => (.active h (Frame.fn_Graph_add_edge 7 { s with t9 := s.v3 }) stack)
  | 9 => (.active h (Frame.fn_Graph_add_edge 8 { s with t8 := s.v2 }) stack)
  | 10 => (Algo2LeanCore.resumeConfig h (Result.fn_Graph_add_edge (s.t12)) stack)
  | 11 => (.active h (Frame.fn_Graph_add_edge 10 { s with t12 := false }) stack)
  | 12 => if s.t11 then (.active h (Frame.fn_Graph_add_edge 11 s) stack) else (.active h (Frame.fn_Graph_add_edge 9 s) stack)
  | 13 => (.active h (Frame.fn_Graph_add_edge 12 { s with t11 := ((decide ((s.v1 < (0 : Int)))) || (decide ((s.v1 ≥ ((field_Graph_size h (s.v0)).getD 0)))) || (decide ((s.v2 < (0 : Int)))) || (decide ((s.v2 ≥ ((field_Graph_size h (s.v0)).getD 0)))) || (decide ((s.v3 < (0 : Int))))) }) stack)
  | pc => .active h (.fn_Graph_add_edge pc s) stack
private def next_dijkstra (h : Heap) (s : State_dijkstra) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_dijkstra (s.t9)) stack)
  | 2 => (.active h (Frame.fn_dijkstra 1 { s with t9 := s.v2 }) stack)
  | 3 => if s.t10 then (.active h (Frame.fn_dijkstra 28 s) stack) else (.active h (Frame.fn_dijkstra 2 s) stack)
  | 4 => (.active h (Frame.fn_dijkstra 3 { s with t10 := (decide ((((field_MinHeap_size h (s.v4)).getD 0) > (0 : Int)))) }) stack)
  | 5 => if s.t11 then (.active h (Frame.fn_dijkstra 21 s) stack) else (.active h (Frame.fn_dijkstra 4 s) stack)
  | 6 => (.active h (Frame.fn_dijkstra 5 { s with t11 := (decide ((s.v6 ≠ none))) }) stack)
  | 7 => (.active h (Frame.fn_dijkstra 6 { s with v6 := ((field_Edge_next h ((s.v6).getD 0)).getD none) }) stack)
  | 8 => (.active (h.tick "improvements" 1) (Frame.fn_dijkstra 7 s) stack)
  | 9 => (.active h (Frame.fn_MinHeap_push_or_decrease 25 ({ v0 := (s.t15), v1 := s.t16, v2 := s.t17 } : State_MinHeap_push_or_decrease)) ((fun value => match value with | .fn_MinHeap_push_or_decrease result => (Frame.fn_dijkstra 8 { s with t14 := result }) | _ => .invalid) :: stack))
  | 10 => (.active h (Frame.fn_dijkstra 9 { s with t17 := s.v8 }) stack)
  | 11 => (.active h (Frame.fn_dijkstra 10 { s with t16 := s.v7 }) stack)
  | 12 => (.active h (Frame.fn_dijkstra 11 { s with t15 := s.t15 }) stack)
  | 13 => (.active h (Frame.fn_dijkstra 12 { s with t15 := s.v4 }) stack)
  | 14 => (.active (h.write s.v2 s.v7 s.v8) (Frame.fn_dijkstra 13 s) stack)
  | 15 => if s.t13 then (.active h (Frame.fn_dijkstra 14 s) stack) else (.active h (Frame.fn_dijkstra 7 s) stack)
  | 16 => (.active h (Frame.fn_dijkstra 15 { s with t13 := ((decide (((h.read s.v2 s.v7) < (0 : Int)))) || (decide ((s.v8 < (h.read s.v2 s.v7))))) }) stack)
  | 17 => (.active h (Frame.fn_dijkstra 16 { s with v8 := ((h.read s.v2 s.v5) + ((field_Edge_weight h ((s.v6).getD 0)).getD 0)) }) stack)
  | 18 => if s.t12 then (.active h (Frame.fn_dijkstra 17 s) stack) else (.active h (Frame.fn_dijkstra 7 s) stack)
  | 19 => (.active h (Frame.fn_dijkstra 18 { s with t12 := (decide (((h.read s.v3 s.v7) = (0 : Int)))) }) stack)
  | 20 => (.active h (Frame.fn_dijkstra 19 { s with v7 := ((field_Edge_target h ((s.v6).getD 0)).getD 0) }) stack)
  | 21 => (.active (h.tick "edges" 1) (Frame.fn_dijkstra 20 s) stack)
  | 22 => (.active h (Frame.fn_dijkstra 6 { s with v6 := ((seq_Edge_optional.get h ((field_Graph_heads h (s.v0)).getD 0) s.v5).getD none) }) stack)
  | 23 => (.active (h.tick "settlements" 1) (Frame.fn_dijkstra 22 s) stack)
  | 24 => (.active (h.write s.v3 s.v5 (1 : Int)) (Frame.fn_dijkstra 23 s) stack)
  | 25 => (.active h (Frame.fn_dijkstra 24 { s with v5 := s.t18 }) stack)
  | 26 => (.active h (Frame.fn_MinHeap_pop_min 21 ({ v0 := (s.t19) } : State_MinHeap_pop_min)) ((fun value => match value with | .fn_MinHeap_pop_min result => (Frame.fn_dijkstra 25 { s with t18 := result }) | _ => .invalid) :: stack))
  | 27 => (.active h (Frame.fn_dijkstra 26 { s with t19 := s.t19 }) stack)
  | 28 => (.active h (Frame.fn_dijkstra 27 { s with t19 := s.v4 }) stack)
  | 29 => (.active h (Frame.fn_MinHeap_push_or_decrease 25 ({ v0 := (s.t21), v1 := s.t22, v2 := s.t23 } : State_MinHeap_push_or_decrease)) ((fun value => match value with | .fn_MinHeap_push_or_decrease result => (Frame.fn_dijkstra 4 { s with t20 := result }) | _ => .invalid) :: stack))
  | 30 => (.active h (Frame.fn_dijkstra 29 { s with t23 := (0 : Int) }) stack)
  | 31 => (.active h (Frame.fn_dijkstra 30 { s with t22 := s.v1 }) stack)
  | 32 => (.active h (Frame.fn_dijkstra 31 { s with t21 := s.t21 }) stack)
  | 33 => (.active h (Frame.fn_dijkstra 32 { s with t21 := s.v4 }) stack)
  | 34 => (.active (h.write s.v2 s.v1 (0 : Int)) (Frame.fn_dijkstra 33 s) stack)
  | 35 => (.active h (Frame.fn_dijkstra 34 { s with v4 := s.t24 }) stack)
  | 36 => (.active h (Frame.fn_MinHeap 6 ({  } : State_MinHeap)) ((fun value => match value with | .fn_MinHeap result => (Frame.fn_dijkstra 35 { s with t24 := result }) | _ => .invalid) :: stack))
  | 37 => (.active h (Frame.fn_dijkstra 36 { s with v3 := s.t25 }) stack)
  | 38 => (.active (h.allocate (fun _ => s.t26)) (Frame.fn_dijkstra 37 { s with t25 := h.nextRef }) stack)
  | 39 => (.active h (Frame.fn_dijkstra 38 { s with t26 := (0 : Int) }) stack)
  | 40 => (Algo2LeanCore.resumeConfig h (Result.fn_dijkstra (s.t28)) stack)
  | 41 => (.active h (Frame.fn_dijkstra 40 { s with t28 := s.v2 }) stack)
  | 42 => if s.t27 then (.active h (Frame.fn_dijkstra 41 s) stack) else (.active h (Frame.fn_dijkstra 39 s) stack)
  | 43 => (.active h (Frame.fn_dijkstra 42 { s with t27 := ((decide ((s.v1 < (0 : Int)))) || (decide ((s.v1 ≥ ((field_Graph_size h (s.v0)).getD 0))))) }) stack)
  | 44 => (.active h (Frame.fn_dijkstra 43 { s with v2 := s.t29 }) stack)
  | 45 => (.active (h.allocate (fun _ => s.t30)) (Frame.fn_dijkstra 44 { s with t29 := h.nextRef }) stack)
  | 46 => (.active h (Frame.fn_dijkstra 45 { s with t30 := (-(1 : Int)) }) stack)
  | pc => .active h (.fn_dijkstra pc s) stack
private def next_MinHeap (h : Heap) (s : State_MinHeap) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_MinHeap (s.t1)) stack)
  | 2 => (.active h (Frame.fn_MinHeap 1 { s with t1 := s.v0 }) stack)
  | 3 => (.active h (Frame.fn_MinHeap___init__ 15 ({ v0 := s.t3 } : State_MinHeap___init__)) ((fun value => match value with | .fn_MinHeap___init__ result => (Frame.fn_MinHeap 2 { s with t2 := result }) | _ => .invalid) :: stack))
  | 4 => (.active h (Frame.fn_MinHeap 3 { s with t3 := s.v0 }) stack)
  | 5 => (.active h (Frame.fn_MinHeap 4 { s with v0 := s.t4 }) stack)
  | 6 => (.active (h.allocateObject "MinHeap") (Frame.fn_MinHeap 5 { s with t4 := h.nextObject }) stack)
  | pc => .active h (.fn_MinHeap pc s) stack
private def next_Edge (h : Heap) (s : State_Edge) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_Edge (s.t4)) stack)
  | 2 => (.active h (Frame.fn_Edge 1 { s with t4 := s.v3 }) stack)
  | 3 => (.active h (Frame.fn_Edge___init__ 5 ({ v0 := s.t6, v1 := s.t7, v2 := s.t8, v3 := s.t9 } : State_Edge___init__)) ((fun value => match value with | .fn_Edge___init__ result => (Frame.fn_Edge 2 { s with t5 := result }) | _ => .invalid) :: stack))
  | 4 => (.active h (Frame.fn_Edge 3 { s with t9 := s.v2 }) stack)
  | 5 => (.active h (Frame.fn_Edge 4 { s with t8 := s.v1 }) stack)
  | 6 => (.active h (Frame.fn_Edge 5 { s with t7 := s.v0 }) stack)
  | 7 => (.active h (Frame.fn_Edge 6 { s with t6 := s.v3 }) stack)
  | 8 => (.active h (Frame.fn_Edge 7 { s with v3 := s.t10 }) stack)
  | 9 => (.active (h.allocateObject "Edge") (Frame.fn_Edge 8 { s with t10 := h.nextObject }) stack)
  | pc => .active h (.fn_Edge pc s) stack
private def next_Graph (h : Heap) (s : State_Graph) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_Graph (s.t2)) stack)
  | 2 => (.active h (Frame.fn_Graph 1 { s with t2 := s.v1 }) stack)
  | 3 => (.active h (Frame.fn_Graph___init__ 10 ({ v0 := s.t4, v1 := s.t5 } : State_Graph___init__)) ((fun value => match value with | .fn_Graph___init__ result => (Frame.fn_Graph 2 { s with t3 := result }) | _ => .invalid) :: stack))
  | 4 => (.active h (Frame.fn_Graph 3 { s with t5 := s.v0 }) stack)
  | 5 => (.active h (Frame.fn_Graph 4 { s with t4 := s.v1 }) stack)
  | 6 => (.active h (Frame.fn_Graph 5 { s with v1 := s.t6 }) stack)
  | 7 => (.active (h.allocateObject "Graph") (Frame.fn_Graph 6 { s with t6 := h.nextObject }) stack)
  | pc => .active h (.fn_Graph pc s) stack
private def next : Configuration → Configuration
  | .done h result => .done h result
  | .active h frame stack => match frame with
    | .invalid => .active h .invalid stack
    | .fn_MinHeap___init__ pc s => next_MinHeap___init__ h s stack pc
    | .fn_MinHeap_swap pc s => next_MinHeap_swap h s stack pc
    | .fn_MinHeap_sift_up pc s => next_MinHeap_sift_up h s stack pc
    | .fn_MinHeap_sift_down pc s => next_MinHeap_sift_down h s stack pc
    | .fn_MinHeap_push_or_decrease pc s => next_MinHeap_push_or_decrease h s stack pc
    | .fn_MinHeap_pop_min pc s => next_MinHeap_pop_min h s stack pc
    | .fn_MinHeap_is_empty pc s => next_MinHeap_is_empty h s stack pc
    | .fn_Edge___init__ pc s => next_Edge___init__ h s stack pc
    | .fn_Graph___init__ pc s => next_Graph___init__ h s stack pc
    | .fn_Graph_add_edge pc s => next_Graph_add_edge h s stack pc
    | .fn_dijkstra pc s => next_dijkstra h s stack pc
    | .fn_MinHeap pc s => next_MinHeap h s stack pc
    | .fn_Edge pc s => next_Edge h s stack pc
    | .fn_Graph pc s => next_Graph h s stack pc
private theorem step_next {before after : Configuration} (transition : Step before after) :
    next before = after := by
  cases transition <;> first | rfl | simp_all [next, next_MinHeap_sift_up, next_MinHeap_sift_down, next_MinHeap_push_or_decrease, next_MinHeap_pop_min, next_Graph___init__, next_Graph_add_edge, next_dijkstra]
private theorem step_deterministic : Deterministic Step := by
  intro before left right first second
  exact (step_next first).symm.trans (step_next second)

end Determinism

/-- Two completed runs from the same input have the same heap and returned reference. -/
theorem execution_unique {heap leftHeap rightHeap : Heap}
    {input : Ref_Graph × Int} {leftResult rightResult : SeqRef}
    (first : dijkstra.Run heap input leftHeap leftResult)
    (second : dijkstra.Run heap input rightHeap rightResult) :
    leftHeap = rightHeap ∧ leftResult = rightResult := by
  have same := Reaches.eq_of_terminal (step := Step) Determinism.step_deterministic first.2 second.2
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

/-- Every completed run produces the same ordinary sequence value. -/
theorem output_unique {input : Heap × (Ref_Graph × Int)} {firstOutput secondOutput : Seq}
    (first : dijkstra.Returns input firstOutput)
    (second : dijkstra.Returns input secondOutput) : firstOutput = secondOutput := by
  obtain ⟨firstHeap, firstResult, firstRun, firstValue⟩ := first
  obtain ⟨secondHeap, secondResult, secondRun, secondValue⟩ := second
  obtain ⟨rfl, rfl⟩ := execution_unique firstRun secondRun
  exact firstValue.symm.trans secondValue

/-- Outputs and all named clock increments are independent of the chosen transcript. -/
theorem output_with_cost_unique {input : Heap × (Ref_Graph × Int)}
    {firstOutput secondOutput : Seq} {firstCosts secondCosts : Clocks}
    (first : dijkstra.ReturnsWithCost input firstOutput firstCosts)
    (second : dijkstra.ReturnsWithCost input secondOutput secondCosts) :
    firstOutput = secondOutput ∧ firstCosts = secondCosts := by
  obtain ⟨firstHeap, firstResult, firstRun, firstValue, firstCost⟩ := first
  obtain ⟨secondHeap, secondResult, secondRun, secondValue, secondCost⟩ := second
  obtain ⟨rfl, rfl⟩ := execution_unique firstRun secondRun
  exact ⟨firstValue.symm.trans secondValue, firstCost.symm.trans secondCost⟩



/-! Ordinary-value specifications for the complete compiled algorithm. -/

/-- The public running-time contract counts actual source ticks. `V` counts
    vertices, `E` counts adjacency entries (including parallel edges), and
    `H = floor(log₂(V+1))` bounds the indexed heap's depth. -/
structure DijkstraRuntimeBound (costs : Clocks) (vertices edges : Nat) : Prop where
  settlements : costs "settlements" ≤ vertices
  edgeVisits : costs "edges" ≤ edges
  improvements : costs "improvements" ≤ edges
  comparisons : costs "heap_comparisons" ≤
    2 * (vertices + 1).log2 * vertices + ((vertices + 1).log2 + 1) * edges
  swaps : costs "heap_swaps" ≤
    ((vertices + 1).log2 + 1) * vertices + (vertices + 1).log2 * edges
  otherClocks : ∀ name, name ≠ "settlements" → name ≠ "edges" → name ≠ "improvements" →
    name ≠ "heap_comparisons" → name ≠ "heap_swaps" → costs name = 0

/-- Internal compositional budgets imply the ordinary clock-map contract. -/
theorem DijkstraRuntimeBound.of_costBounds {before after : Heap} {vertices edges : Nat}
    (bound : CostBounds before after vertices edges (vertices + 1).log2) :
    DijkstraRuntimeBound (Heap.cost before after) vertices edges := by
  refine ⟨bound.settlements, bound.edges, bound.improvements, bound.comparisons, bound.swaps, ?_⟩
  intro name notSettlements notEdges notImprovements notComparisons notSwaps
  unfold Heap.cost
  rw [bound.otherClocks name notSettlements notEdges notImprovements notComparisons notSwaps]
  omega

-- Main result: Correctness
/-- The reusable binary-heap Dijkstra contract preserves every caller-owned
    location, returns a fresh allocated distance sequence, proves shortest paths,
    and bounds actual clock increments from arbitrary initial counters. -/
theorem dijkstra_call_contract (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    ∃ after, dijkstra.Call heap (graph, source) after heap.nextRef ∧
      GraphRep after graph size heads adjacency ∧
      ShortestDistances (representedEdges size adjacency) source (after.read heap.nextRef) ∧
      DijkstraRuntimeBound (Heap.cost heap after) size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      (∀ vertex, vertex < 0 ∨ size ≤ vertex → after.read heap.nextRef vertex = -1) ∧
      heap.Footprint after [] [] [] ∧ heap.nextRef < after.nextRef ∧
      heap.Increments after (Heap.cost heap after) := by
  have initialized := initialization_ready representation source
  obtain ⟨after, completed⟩ := extraction_loop_correct
    (queuedForDijkstra heap source) graph size source heads adjacency heap.nextRef (heap.nextRef + 1)
    heap.nextObject { layoutForDijkstra heap with size := 1 } (vertexRange size)
    (initialized.invariant sourceNonnegative sourceBound)
  have summary := initialize_summary heap (queueForDijkstra heap) (queuedForDijkstra heap source) after
    graph heap.nextObject source size heap.nextRef representation.valid representation.readSize
    sourceNonnegative sourceBound initialized.constructor initialized.beforeInsertionAllocated
    initialized.insertion completed.execution
  have initializationCost : CostBounds heap (queuedForDijkstra heap source) 0 0 (Queue.depth size) :=
    CostBounds.of_clocks_eq initialized.clocks (Queue.depth size)
  have totalCost : CostBounds heap after size.toNat
      (edgeBudget adjacency (vertexRange size)) (Queue.depth size) := by
    simpa using initializationCost.trans completed.costs
  refine ⟨after, summary, completed.graph,
    completed.search.choose_spec.1.correct representation.nonnegative_edges
      (initialized.invariant sourceNonnegative sourceBound).paths,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact DijkstraRuntimeBound.of_costBounds totalCost
  · intro vertex outside
    apply completed.canonical vertex
    by_cases finite : 0 ≤ after.read heap.nextRef vertex
    · have inside := completed.finiteInRange vertex finite
      omega
    · omega

  · have prepared := initialization_footprint heap source
    have all := (prepared.weaken (by simp) (by simp) (by simp)).trans completed.footprint
    refine ⟨all.nextRef, all.nextObject, all.nextCollection, all.classes, all.types, ?_, ?_, ?_⟩
    · intro ref old _
      apply all.otherSequences ref old
      simp only [List.mem_cons, Queue.Layout.refs, layoutForDijkstra, Queue.emptyLayout,
        allocatedForDijkstra, Heap.allocate, List.mem_nil_iff, or_false]
      omega
    · intro ref old _
      apply all.otherObjects ref old
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      omega
    · exact all.otherCollections
  · have bound := completed.footprint.nextRef
    change heap.nextRef + 1 + 1 + 1 + 1 + 1 ≤ after.nextRef at bound
    omega
  · exact Heap.ClocksMonotone.increments
      (execution_clocks_monotone heap after graph source heap.nextRef summary.run)

/-- A compact compatibility view of the full reusable call contract. -/
theorem dijkstra_summary (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    ∃ after, dijkstra.Call heap (graph, source) after heap.nextRef ∧
      GraphRep after graph size heads adjacency ∧
      ShortestDistances (representedEdges size adjacency) source (after.read heap.nextRef) ∧
      DijkstraRuntimeBound (Heap.cost heap after) size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      ∀ vertex, vertex < 0 ∨ size ≤ vertex → after.read heap.nextRef vertex = -1 := by
  obtain ⟨after, call, graphRep, correct, runtime, outside, _⟩ :=
    dijkstra_call_contract heap graph size source heads adjacency representation sourceNonnegative sourceBound
  exact ⟨after, call, graphRep, correct, runtime, outside⟩

/-- Ordinary outputs and costs are a view of the same reusable call contract. -/
theorem dijkstra_correct_output_exists (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) :
    ∃ output costs,
      dijkstra.ReturnsWithCost (heap, graph, source) output costs ∧
      ShortestDistances (representedEdges size adjacency) source output ∧
      DijkstraRuntimeBound costs size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      ∀ vertex, vertex < 0 ∨ size ≤ vertex → output vertex = -1 := by
  obtain ⟨after, call, preserved, correct, costs, outside⟩ :=
    dijkstra_summary heap graph size source heads adjacency representation sourceNonnegative sourceBound
  exact ⟨after.read heap.nextRef, Heap.cost heap after,
    ⟨after, heap.nextRef, call.run, rfl, rfl⟩, correct, costs, outside⟩

-- Main result: Running time
/-- Every completed call satisfies the same bound on actual clock increments,
    so the runtime guarantee can be reused inside a larger compiled caller. -/
theorem dijkstra_call_running_time (heap after : Heap) (graph : Ref_Graph)
    (size source : Int) (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (result : SeqRef) (call : dijkstra.Call heap (graph, source) after result) :
    DijkstraRuntimeBound (Heap.cost heap after) size.toNat
      (edgeBudget adjacency (vertexRange size)) := by
  obtain ⟨verified, run, _, _, runtime, _⟩ :=
    dijkstra_call_contract heap graph size source heads adjacency representation sourceNonnegative sourceBound
  obtain ⟨rfl, rfl⟩ := execution_unique run.run call.run
  exact runtime

/-- The mathematical and runtime guarantees hold for every compiled output,
    not just the execution constructed by the termination proof. -/
theorem dijkstra_output_with_cost_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (output : Seq) (costs : Clocks)
    (run : dijkstra.ReturnsWithCost (heap, graph, source) output costs) :
    ShortestDistances (representedEdges size adjacency) source output ∧
      DijkstraRuntimeBound costs size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      ∀ vertex, vertex < 0 ∨ size ≤ vertex → output vertex = -1 := by
  obtain ⟨verifiedOutput, verifiedCosts, verified, correct, runtime, outside⟩ :=
    dijkstra_correct_output_exists heap graph size source heads adjacency representation
      sourceNonnegative sourceBound
  obtain ⟨sameOutput, sameCosts⟩ := output_with_cost_unique verified run
  subst output costs
  exact ⟨correct, runtime, outside⟩

/-- Ordinary output reasoning requires no clocks, local labels, or execution
    configurations: every generated output is a shortest-distance sequence. -/
theorem dijkstra_output_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size)
    (output : Seq) (run : dijkstra.Returns (heap, graph, source) output) :
    ShortestDistances (representedEdges size adjacency) source output := by
  obtain ⟨costs, withCost⟩ := run.withCost
  exact (dijkstra_output_with_cost_correct heap graph size source heads adjacency
    representation sourceNonnegative sourceBound output costs withCost).1

/-- A user may replace the compiler's output proposition by the usual
    mathematical shortest-distance specification in either direction. -/
theorem dijkstra_output_iff (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceNonnegative : 0 ≤ source) (sourceBound : source < size) (output : Seq) :
    dijkstra.Returns (heap, graph, source) output ↔
      ShortestDistances (representedEdges size adjacency) source output := by
  constructor
  · exact dijkstra_output_correct heap graph size source heads adjacency representation
      sourceNonnegative sourceBound output
  · intro correct
    obtain ⟨verifiedOutput, costs, verified, verifiedCorrect, _, _⟩ :=
      dijkstra_correct_output_exists heap graph size source heads adjacency representation
        sourceNonnegative sourceBound
    have same := verifiedCorrect.unique correct
    subst output
    exact verified.returns

/-- Every represented graph terminates for every integer source. Invalid
    sources return the existing all-`-1` result without charging any ticks. -/
theorem dijkstra_terminates (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency) :
    ∃ output costs, dijkstra.ReturnsWithCost (heap, graph, source) output costs := by
  by_cases valid : 0 ≤ source ∧ source < size
  · obtain ⟨output, costs, run, _⟩ := dijkstra_correct_output_exists heap graph size source heads adjacency
      representation valid.1 valid.2
    exact ⟨output, costs, run⟩
  · exact ⟨fun _ => -1, fun _ => 0,
      invalid_source_output_with_cost heap graph source size representation.valid representation.readSize (by omega)⟩


/-- Total work charged to the five clocks instrumented by Dijkstra and its heap. -/
def chargedWork (costs : Clocks) : Nat :=
  costs "settlements" + costs "edges" + costs "improvements" +
    costs "heap_comparisons" + costs "heap_swaps"

/-- For a nonempty graph, all source-instrumented work has a direct logarithmic bound. -/
theorem DijkstraRuntimeBound.total_logarithmic {costs : Clocks} {vertices edges : Nat}
    (bound : DijkstraRuntimeBound costs vertices edges) (positive : 0 < vertices) :
    chargedWork costs ≤ 5 * (vertices + 1).log2 * (vertices + edges) := by
  have heightPositive : 1 ≤ (vertices + 1).log2 :=
    (Nat.le_log2 (by omega)).mpr (by simpa using! positive)
  have vertexWork : vertices ≤ (vertices + 1).log2 * vertices := by
    simpa using Nat.mul_le_mul_right vertices heightPositive
  have edgeWork : edges ≤ (vertices + 1).log2 * edges := by
    simpa using Nat.mul_le_mul_right edges heightPositive
  have settlements := bound.settlements
  have edgeVisits := bound.edgeVisits
  have improvements := bound.improvements
  have comparisons := bound.comparisons
  have swaps := bound.swaps
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at comparisons swaps
  simp only [chargedWork, Nat.mul_add, Nat.mul_assoc]
  omega


end DijkstraAnalysis
