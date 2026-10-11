import Algo.prim.support.Analysis
import Algo.prim.math.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Prim's adjacency scan preserves queue contents, parent pointers, and keys.
Every queue update uses only the imported operation contract. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo2Lean.Prim
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl

variable {dependencies : Dependencies} {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)
variable (contracts : Contracts model reservedClocks)
include contracts

structure EdgeAdvanced (before after : QueueState model)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge) : Prop where
  storage : Storage model after
  matching : QueueMatches model after
  selected : after.heap.read client.selected = before.heap.read client.selected
  scan : KeyScan (fun v => before.heap.read client.selected v ≠ 0) vertex
    [(target,weight)] (before.heap.read client.key) (before.heap.read client.parent)
    (after.heap.read client.key) (after.heap.read client.parent)
  costs : CostBounds model before after 0 1
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : ∀ finalHeap,
    ScanLoop dependencies after.heap client.queue client.key client.parent client.selected vertex next finalHeap →
    ScanLoop dependencies before.heap client.queue client.key client.parent client.selected vertex (some edge) finalHeap

structure AdjacencyScanned (before after : QueueState model)
    (vertex : Int) (head : Option Ref_Edge) (edges : List (Int × Int)) : Prop where
  storage : Storage model after
  matching : QueueMatches model after
  selected : after.heap.read client.selected = before.heap.read client.selected
  scan : KeyScan (fun v => before.heap.read client.selected v ≠ 0) vertex edges
    (before.heap.read client.key) (before.heap.read client.parent)
    (after.heap.read client.key) (after.heap.read client.parent)
  costs : CostBounds model before after 0 edges.length
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : ScanLoop dependencies before.heap client.queue client.key client.parent client.selected vertex head after.heap

/-- One adjacency cell is skipped or updates exactly one queue entry and parent. -/
theorem advance_edge (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (vertex target weight : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge)
    (storage : Storage model state) (matching : QueueMatches model state)
    (vertexLower : 0 ≤ vertex) (rootSelected : state.heap.read client.selected client.root ≠ 0)
    (validEdge : is_Edge state.heap edge)
    (readTarget : field_Edge_target state.heap edge = some target)
    (readWeight : field_Edge_weight state.heap edge = some weight)
    (readNext : field_Edge_next state.heap edge = some next)
    (targetLower : 0 ≤ target) (targetUpper : target < client.size) :
    ∃ after, EdgeAdvanced model state after vertex target weight edge next := by
  have inputs : scan_edges.ValidInput dependencies state.heap
      (client.queue,client.key,client.parent,client.selected,vertex,some edge) :=
    ⟨model.valid storage.queue,storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated,
      by
        intro ref member
        have same : edge = ref := by simpa using member
        simpa only [←same] using validEdge⟩
  by_cases unselected : state.heap.read client.selected target = 0
  · by_cases better : state.heap.read client.parent target < 0 ∨ weight < state.heap.read client.key target
    · let prepared := (((state.tick model "edges").write model client.key target weight).write model client.parent target vertex).tick model "queue_updates"
      have preparedStorage : Storage model prepared :=
        (((storage.tick model "edges").write model _ target weight (by simp [Client.protection])).write model _ target vertex (by simp [Client.protection])).tick model "queue_updates"
      obtain ⟨after, updated⟩ := queue_update model contracts prepared target weight preparedStorage targetLower
        (by omega) (by
          intro old member
          have entry := (matching target old).mp member
          have notRoot : target ≠ client.root := by intro same; subst target; exact rootSelected unselected
          rcases entry.2.1 with same | known
          · exact False.elim (notRoot same)
          · omega)
      have keyFinal : (after.tick model "improvements").heap.read client.key =
          assign (state.heap.read client.key) target weight := by
        rw [show (after.tick model "improvements").heap.read client.key = after.heap.read client.key from rfl, updated.key]
        funext v
        simp [prepared,QueueState.tick,QueueState.write,Heap.read,Heap.write,assign,storage.keyParent]
      have parentFinal : (after.tick model "improvements").heap.read client.parent =
          assign (state.heap.read client.parent) target vertex := by
        rw [show (after.tick model "improvements").heap.read client.parent = after.heap.read client.parent from rfl, updated.parent]
        funext v
        simp [prepared,QueueState.tick,QueueState.write,Heap.read,Heap.write,assign,Ne.symm storage.keyParent]
      have selectedFinal : (after.tick model "improvements").heap.read client.selected =
          state.heap.read client.selected := by
        rw [show (after.tick model "improvements").heap.read client.selected = after.heap.read client.selected from rfl, updated.selected]
        funext v
        simp [prepared,QueueState.tick,QueueState.write,Heap.read,Heap.write,Ne.symm storage.separate,Ne.symm storage.parentSelected]
      have frame : GraphFrame state.heap (after.tick model "improvements").heap client.graph client.heads :=
        ((((graph_frame_tick _ _ _ "edges" 1).trans
          (graph_frame_write _ _ _ client.key target weight)).trans
          (graph_frame_write _ _ _ client.parent target vertex)).trans
          (graph_frame_tick _ _ _ "queue_updates" 1)).trans
          (updated.frame.trans (graph_frame_tick _ _ _ "improvements" 1))
      refine ⟨after.tick model "improvements",updated.storage.tick model "improvements",?_,selectedFinal,?_,
        updated_edge_cost model contracts updated,frame,?_⟩
      · intro v k
        change (v,k) ∈ after.entries model ↔ _
        rw [updated.contents,keyFinal,parentFinal,selectedFinal]
        change (v = target ∧ k = weight) ∨ (v ≠ target ∧ (v,k) ∈ state.entries model) ↔ _
        rw [matching]
        by_cases same : v = target <;> simp [assign,same,unselected,vertexLower]
      · rw [keyFinal,parentFinal]
        exact KeyScan.improve (by simpa using unselected) better (.done _ _)
      · intro finalHeap tail
        exact scan_improved dependencies state.heap after.heap finalHeap client.queue client.key client.parent client.selected
          vertex target weight edge next inputs readTarget readWeight
          (((frame.edges edge validEdge).2.2.2).trans readNext) unselected better updated.execution tail
    · have known : 0 ≤ state.heap.read client.parent target := by omega
      have expensive : state.heap.read client.key target ≤ weight := by omega
      refine ⟨state.tick model "edges",storage.tick model "edges",matching,rfl,?_,
        skip_edge_cost model contracts state,graph_frame_tick _ _ _ "edges" 1,?_⟩
      · exact KeyScan.keep (by simpa using unselected) known expensive (.done _ _)
      · intro finalHeap tail
        exact scan_unimproved dependencies state.heap finalHeap client.queue client.key client.parent client.selected
          vertex target weight edge next inputs readTarget readWeight readNext unselected known expensive tail
  · refine ⟨state.tick model "edges",storage.tick model "edges",matching,rfl,
      KeyScan.skip unselected (.done _ _),skip_edge_cost model contracts state,graph_frame_tick _ _ _ "edges" 1,?_⟩
    intro finalHeap tail
    exact scan_selected dependencies state.heap finalHeap client.queue client.key client.parent client.selected
      vertex target edge next inputs readTarget readNext unselected tail

/-- Scanning a finite adjacency list composes its local updates and clock bounds. -/
theorem scan_adjacency (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (vertex : Int) (head : Option Ref_Edge) (edges : List (Int × Int))
    (storage : Storage model state) (matching : QueueMatches model state)
    (vertexLower : 0 ≤ vertex) (rootSelected : state.heap.read client.selected client.root ≠ 0)
    (chain : AdjacencyChain state.heap client.size head edges) :
    ∃ after, AdjacencyScanned model state after vertex head edges := by
  induction edges generalizing state head with
  | nil =>
    have empty : head = none := by cases chain; rfl
    subst head
    exact ⟨state,storage,matching,rfl,KeyScan.done _ _,CostBounds.refl model state,GraphFrame.refl _ _ _,
      scan_empty dependencies state.heap client.queue client.key client.parent client.selected vertex⟩
  | cons pair rest ih =>
    cases chain with
    | cons edge target weight next tail valid readTarget readWeight readNext lower upper remaining =>
      obtain ⟨middle,advanced⟩ := advance_edge model contracts capacity state vertex target weight edge next
        storage matching vertexLower rootSelected valid readTarget readWeight readNext lower upper
      obtain ⟨after,scanned⟩ := ih middle next advanced.storage advanced.matching
        (by rw [advanced.selected]; exact rootSelected) (remaining.preserved advanced.frame.edges)
      refine ⟨after,scanned.storage,scanned.matching,scanned.selected.trans advanced.selected,?_,?_,
        advanced.frame.trans scanned.frame,advanced.execution after.heap scanned.execution⟩
      · have tailScan := scanned.scan
        rw [advanced.selected] at tailScan
        exact advanced.scan.append tailScan
      · simpa [Nat.add_comm] using advanced.costs.trans model scanned.costs

end PrimAnalysis
