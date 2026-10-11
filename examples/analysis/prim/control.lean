import Algo.prim.prim.Generated
import Algo.prim.prim.Points
import Algo.prim.prim.Facts

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Local execution rules for Prim's two loops. Each lemma describes public
    named locations and source variables. Queue calls are supplied as contracts;
    their representation and balancing details do not enter these proofs. -/

namespace PrimControl

open Algo2LeanCore Algo2LeanGenerated
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim
open Algo.dijkstra.priority_queue

@[simp] theorem edge_target_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_target (heap.tick clock amount) edge = field_Edge_target heap edge := rfl
@[simp] theorem edge_weight_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_weight (heap.tick clock amount) edge = field_Edge_weight heap edge := rfl
@[simp] theorem edge_next_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_next (heap.tick clock amount) edge = field_Edge_next heap edge := rfl

variable (dependencies : Dependencies)

/-- The adjacency loop is described by its named source location and live variables.
    Temporary values from earlier iterations impose no obligations on the caller. -/
def AtScan (state : Algo.prim.prim.Algo2LeanGenerated.Configuration dependencies)
    (heap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex : Int) (edge : Option Ref_Edge) : Prop :=
  scan_edges.At.scan dependencies state ∧ state.heap = heap ∧
  scan_edges.Local.queue dependencies state = some queue ∧
  scan_edges.Local.key dependencies state = some key ∧
  scan_edges.Local.parent dependencies state = some parent ∧
  scan_edges.Local.selected dependencies state = some selected ∧
  scan_edges.Local.vertex dependencies state = some vertex ∧
  scan_edges.Local.edge dependencies state = some edge

/-- Finish the adjacency loop from any local state with these source variables. -/
def ScanLoop (heap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex : Int) (edge : Option Ref_Edge) (finalHeap : Heap) : Prop :=
  ∀ state, AtScan dependencies state heap queue key parent selected vertex edge →
    scan_edges.CallFrom dependencies state finalHeap ()

/-- The main loop needs only the graph, queue, and three client sequences. The
    initialized root and previous iteration's temporary values are irrelevant. -/
def AtExtract (state : Algo.prim.prim.Algo2LeanGenerated.Configuration dependencies)
    (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef) (key parent selected : SeqRef) : Prop :=
  prim.At.extract dependencies state ∧ state.heap = heap ∧
  prim.Local.graph dependencies state = some graph ∧
  prim.Local.queue dependencies state = some queue ∧
  prim.Local.key dependencies state = some key ∧
  prim.Local.parent dependencies state = some parent ∧
  prim.Local.selected dependencies state = some selected

/-- Finish the main loop after counting its next emptiness test. This local
    continuation is independent of the code that initialized the search. -/
def ExtractLoop (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef)
    (key parent selected : SeqRef) (finalHeap : Heap) : Prop :=
  ∀ state, AtExtract dependencies state (heap.tick "queue_empty_checks") graph queue key parent selected →
    prim.CallFrom dependencies state finalHeap parent

/-- An empty adjacency list exits the loop without changing the heap. -/
theorem scan_empty (heap : Heap) (queue : ObjectRef) (key parent selected : SeqRef) (vertex : Int) :
    ScanLoop dependencies heap queue key parent selected vertex none heap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_false _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc2 _ _ caller)
    exact Reaches.single (Step.scan_edges_pc1 _ _ caller)

/-- A selected target is skipped; the loop continues at the next adjacency cell. -/
theorem scan_selected (heap finalHeap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex target : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,key,parent,selected,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readNext : field_Edge_next heap edge = some next)
    (already : heap.read selected target ≠ 0)
    (tail : ScanLoop dependencies (heap.tick "edges") queue key parent selected vertex next finalHeap) :
    ScanLoop dependencies heap queue key parent selected vertex (some edge) finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc21 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller valid.2.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc18_false _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using already))
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller

/-- An unselected target whose edge key cannot improve leaves the queue unchanged. -/
theorem scan_unimproved (heap finalHeap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,key,parent,selected,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (readNext : field_Edge_next heap edge = some next)
    (unselected : heap.read selected target = 0)
    (discovered : 0 ≤ heap.read parent target)
    (notBetter : heap.read key target ≤ weight)
    (tail : ScanLoop dependencies (heap.tick "edges") queue key parent selected vertex next finalHeap) :
    ScanLoop dependencies heap queue key parent selected vertex (some edge) finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc21 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller valid.2.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc18_true _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using unselected))
    apply Reaches.prepend (Step.scan_edges_pc17 _ _ caller
      (by simp [field__a2l_import_0_Edge_weight, readWeight]))
    apply Reaches.prepend (Step.scan_edges_pc16 _ _ caller
      ⟨valid.2.2.1, fun _ => valid.2.1⟩)
    apply Reaches.prepend (Step.scan_edges_pc15_false _ _ caller
      (by simp [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight, readTarget, readWeight]; omega))
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller

/-- A successful key improvement reuses the abstract queue Call and then resumes the loop. -/
theorem scan_improved (heap queuedHeap finalHeap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,key,parent,selected,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (readNext : field_Edge_next queuedHeap edge = some next)
    (unselected : heap.read selected target = 0)
    (better : heap.read parent target < 0 ∨ weight < heap.read key target)
    (update : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue
      ((((heap.tick "edges").write key target weight).write parent target vertex).tick "queue_updates")
      (queue,target,weight) queuedHeap ())
    (tail : ScanLoop dependencies (queuedHeap.tick "improvements") queue key parent selected vertex next finalHeap) :
    ScanLoop dependencies heap queue key parent selected vertex (some edge) finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc21 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller valid.2.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc18_true _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using unselected))
    apply Reaches.prepend (Step.scan_edges_pc17 _ _ caller
      (by simp [field__a2l_import_0_Edge_weight, readWeight]))
    apply Reaches.prepend (Step.scan_edges_pc16 _ _ caller
      ⟨valid.2.2.1, fun _ => valid.2.1⟩)
    apply Reaches.prepend (Step.scan_edges_pc15_true _ _ caller
      (by simpa [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight, readTarget,readWeight] using better))
    simp only [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight,
      edge_target_tick, edge_weight_tick, readTarget, readWeight, Option.getD_some]
    apply Reaches.prepend (Step.scan_edges_pc14 _ _ caller valid.2.1)
    apply Reaches.prepend (Step.scan_edges_pc13 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc12 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc11 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc10 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue, Heap.read, Heap.tick] using update.1))
    apply Reaches.prepend (Step.scan_edges_pc9 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc8 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc7 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller update.2).trans
    apply Reaches.prepend (Step.scan_edges_pc6 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller

/-- A loop contract supplies the ordinary function Call at the entry location. -/
theorem scan_call (heap finalHeap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex : Int) (head : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,key,parent,selected,vertex,head))
    (loop : ScanLoop dependencies heap queue key parent selected vertex head finalHeap) :
    scan_edges.Call dependencies heap (queue,key,parent,selected,vertex,head) finalHeap () := by
  refine ⟨valid, loop (scan_edges.initial dependencies heap (queue,key,parent,selected,vertex,head)) ?_⟩
  simp [AtScan, scan_edges.initial, Algo2LeanCore.start, scan_edges.At.scan,
    scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
    scan_edges.Local.vertex, scan_edges.Local.edge, Config.heap]

/-- The final empty test returns the parent reference. -/
theorem extract_empty (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef) (key parent selected : SeqRef)
    (parentAllocated : parent < heap.nextRef)
    (empty : PriorityQueue.is_empty.Call dependencies.PriorityQueue
      (heap.tick "queue_empty_checks") queue (heap.tick "queue_empty_checks") true) :
    ExtractLoop dependencies heap graph queue key parent selected (heap.tick "queue_empty_checks") := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameGraph, sameQueue, sameKey, sameParent, sameSelected⟩ := located
    unfold prim.At.extract at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [prim.Local.graph, prim.Local.queue, prim.Local.key, prim.Local.parent,
      prim.Local.selected] at sameGraph sameQueue sameKey sameParent sameSelected
    subst_vars
    intro caller
    apply Reaches.prepend (Step.prim_pc7 _ _ caller)
    apply Reaches.prepend (Step.prim_pc6 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using empty.1))
    apply Reaches.prepend (Step.prim_pc5 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller empty.2).trans
    apply Reaches.prepend (Step.prim_pc4 _ _ caller)
    apply Reaches.prepend (Step.prim_pc3_false _ _ caller rfl)
    apply Reaches.prepend (Step.prim_pc2 _ _ caller)
    exact Reaches.single (Step.prim_pc1 _ _ caller parentAllocated)

/-- One extraction composes the queue contract, adjacency-loop contract, and
    next iteration. Caller frames and irrelevant locals remain encapsulated. -/
theorem extract_next (heap poppedHeap scannedHeap finalHeap : Heap)
    (graph : Ref_Graph) (queue : ObjectRef) (key parent selected : SeqRef) (vertex : Int)
    (heads : CollectionRef) (head : Option Ref_Edge)
    (empty : PriorityQueue.is_empty.Call dependencies.PriorityQueue
      (heap.tick "queue_empty_checks") queue (heap.tick "queue_empty_checks") false)
    (popped : PriorityQueue.pop_min.Call dependencies.PriorityQueue
      ((heap.tick "queue_empty_checks").tick "queue_pops") queue poppedHeap vertex)
    (selectedAllocated : selected < poppedHeap.nextRef)
    (readHeads : field_Graph_heads poppedHeap graph = some heads)
    (readHead : seq_Edge_optional.get poppedHeap heads vertex = some head)
    (scan : ScanLoop dependencies ((poppedHeap.write selected vertex 1).tick "settlements")
      queue key parent selected vertex head scannedHeap)
    (tail : ExtractLoop dependencies scannedHeap graph queue key parent selected finalHeap) :
    ExtractLoop dependencies heap graph queue key parent selected finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    have headsAfter : field__a2l_import_0_Graph_heads
        ((poppedHeap.write selected vertex 1).tick "settlements") graph = some heads := readHeads
    have headAfter : seq__a2l_import_0_Edge_optional.get
        ((poppedHeap.write selected vertex 1).tick "settlements") heads vertex = some head := readHead
    intro state located
    obtain ⟨named, sameHeap, sameGraph, sameQueue, sameKey, sameParent, sameSelected⟩ := located
    unfold prim.At.extract at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [prim.Local.graph, prim.Local.queue, prim.Local.key, prim.Local.parent,
      prim.Local.selected] at sameGraph sameQueue sameKey sameParent sameSelected
    subst_vars
    intro caller
    apply Reaches.prepend (Step.prim_pc7 _ _ caller)
    apply Reaches.prepend (Step.prim_pc6 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using empty.1))
    apply Reaches.prepend (Step.prim_pc5 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller empty.2).trans
    apply Reaches.prepend (Step.prim_pc4 _ _ caller)
    apply Reaches.prepend (Step.prim_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.prim_pc22 _ _ caller)
    apply Reaches.prepend (Step.prim_pc21 _ _ caller)
    apply Reaches.prepend (Step.prim_pc20 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using popped.1))
    apply Reaches.prepend (Step.prim_pc19 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller popped.2).trans
    apply Reaches.prepend (Step.prim_pc18 _ _ caller)
    apply Reaches.prepend (Step.prim_pc17 _ _ caller selectedAllocated)
    apply Reaches.prepend (Step.prim_pc16 _ _ caller)
    apply Reaches.prepend (Step.prim_pc15 _ _ caller)
    apply Reaches.prepend (Step.prim_pc14 _ _ caller)
    apply Reaches.prepend (Step.prim_pc13 _ _ caller)
    apply Reaches.prepend (Step.prim_pc12 _ _ caller)
    apply Reaches.prepend (Step.prim_pc11 _ _ caller)
    apply Reaches.prepend (Step.prim_pc10 _ _ caller (by simp [headsAfter,headAfter]))
    apply Reaches.prepend (Step.prim_pc9 _ _ caller)
    simp only [headsAfter,headAfter,Option.getD_some]
    apply Reaches.trans (scan (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge, Config.heap]) _)
    apply Reaches.prepend (Step.prim_pc8 _ _ caller)
    exact tail (.active _ (.fn_prim 7 _) [])
      (by simp [AtExtract, prim.At.extract, prim.Local.graph, prim.Local.queue,
        prim.Local.key, prim.Local.parent, prim.Local.selected, Config.heap]) caller

/-- Initialization adds the root once and enters the main loop. -/
theorem initialize_summary (heap queuedHeap finalHeap : Heap) (graph : Ref_Graph) (root : Int)
    (queue : ObjectRef) (key parent selected : SeqRef)
    (valid : prim.ValidInput dependencies heap (graph,root,queue,key,parent,selected))
    (inserted : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue
      ((heap.write key root 0).tick "queue_updates") (queue,root,0) queuedHeap ())
    (tail : ExtractLoop dependencies queuedHeap graph queue key parent selected finalHeap) :
    prim.Call dependencies heap (graph,root,queue,key,parent,selected) finalHeap parent := by
  open Algo.prim.prim.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.prim_pc30 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.prim_pc29 _ _ caller)
    apply Reaches.prepend (Step.prim_pc28 _ _ caller)
    apply Reaches.prepend (Step.prim_pc27 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using inserted.1))
    apply Reaches.prepend (Step.prim_pc26 _ _ caller)
    apply Reaches.prepend (Step.prim_pc25 _ _ caller)
    apply Reaches.prepend (Step.prim_pc24 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller inserted.2).trans
    apply Reaches.prepend (Step.prim_pc23 _ _ caller)
    exact tail (.active _ (.fn_prim 7 _) [])
      (by simp [AtExtract, prim.At.extract, prim.Local.graph, prim.Local.queue,
        prim.Local.key, prim.Local.parent, prim.Local.selected, Config.heap]) caller


end PrimControl
