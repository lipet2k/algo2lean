import Algo.prim.control.Analysis
import Algo.prim.graph.Analysis
import Algo.dijkstra.priority_queue.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Queue storage and compositional clock accounting for Prim. The queue backend
is abstract, and its amortized potential is carried through actual calls. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl
variable (dependencies : Dependencies)

/-- The graph and initialized client sequences are supplied by the caller. -/
structure Client where
  graph : Ref_Graph
  size : Int
  heads : CollectionRef
  adjacency : Adjacency
  key : SeqRef
  parent : SeqRef
  root : Int
  selected : SeqRef
  queue : ObjectRef
  caller : Heap := {}

def Client.protection (client : Client) : Protected :=
  ⟨[client.key, client.parent, client.selected], ["prim.graph.Graph", "prim.graph.Edge"], [client.heads], client.caller⟩

def reservedClocks : List String :=
  ["queue_updates", "queue_pops", "queue_empty_checks", "edges", "improvements", "settlements"]

variable {dependencies}
variable {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)

structure QueueState where
  heap : Heap
  queueState : model.State

namespace QueueState

def tick (state : QueueState model) (name : String) : QueueState model :=
  {state with heap := state.heap.tick name}
def write (state : QueueState model) (ref : SeqRef) (index value : Int) : QueueState model :=
  {state with heap := state.heap.write ref index value}
abbrev entries (state : QueueState model) := model.entries state.queueState
abbrev potential (state : QueueState model) := model.potential state.queueState

end QueueState

structure Storage (state : QueueState model) : Prop where
  graph : GraphRep state.heap client.graph client.size client.heads client.adjacency
  queue : model.Rep state.heap state.queueState
  keyAllocated : client.key < state.heap.nextRef
  parentAllocated : client.parent < state.heap.nextRef
  selectedAllocated : client.selected < state.heap.nextRef
  keyParent : client.key ≠ client.parent
  parentSelected : client.parent ≠ client.selected
  separate : client.key ≠ client.selected

theorem Storage.tick {state : QueueState model} (storage : Storage model state) (name : String) :
    Storage model (state.tick model name) :=
  ⟨storage.graph.preserved (graph_frame_tick _ _ _ name 1),
    model.tick storage.queue name 1, storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated,storage.keyParent,storage.parentSelected,storage.separate⟩

theorem Storage.write {state : QueueState model} (storage : Storage model state)
    (ref : SeqRef) (index value : Int) (member : ref ∈ client.protection.sequences) :
    Storage model (state.write model ref index value) :=
  ⟨storage.graph.preserved (graph_frame_write _ _ _ ref index value),
    model.write storage.queue ref member index value,
    storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated,storage.keyParent,storage.parentSelected,storage.separate⟩

/-- The generic queue frame implies preservation of the imported graph. -/
theorem graph_frame_of_protected {before after : Heap}
    (representation : GraphRep before client.graph client.size client.heads client.adjacency)
    (frame : PriorityQueueAnalysis.Frame client.protection before after) :
    GraphFrame before after client.graph client.heads := by
  have validGraph : is_Graph after client.graph :=
    ⟨Nat.lt_of_lt_of_le representation.valid.1 frame.nextObject,
      (frame.classes _ representation.valid.1).trans representation.valid.2⟩
  have graphFields : after.objects client.graph = before.objects client.graph :=
    frame.objects _ "prim.graph.Graph" representation.valid.1 representation.valid.2 (by simp [Client.protection])
  have graphRead : ∀ field, after.readField client.graph field = before.readField client.graph field := by
    intro field
    simp [Heap.readField,graphFields]
  have oldHeads : client.heads < before.nextCollection := representation.headsValid.1
  have headsType : after.sequenceType client.heads = before.sequenceType client.heads := frame.types _ oldHeads
  have headsValid : seq_Edge_optional.valid after client.heads :=
    ⟨Nat.lt_of_lt_of_le oldHeads frame.nextCollection, headsType.trans representation.headsValid.2⟩
  have collections := frame.collections _ (by simp [Client.protection]) oldHeads
  have entries : ∀ vertex, seq_Edge_optional.get after client.heads vertex =
      seq_Edge_optional.get before client.heads vertex := by
    intro vertex
    simp [SequenceType.get,headsValid,representation.headsValid,Heap.readElement,collections]
  refine ⟨fun _ => validGraph, ?_, ?_, fun _ => headsValid, entries, ?_⟩
  · simp [field_Graph_size, validGraph,representation.valid,graphRead]
  · simp [field_Graph_heads, validGraph,representation.valid,graphRead]
  · intro ref valid
    have newValid : is_Edge after ref :=
      ⟨Nat.lt_of_lt_of_le valid.1 frame.nextObject, (frame.classes _ valid.1).trans valid.2⟩
    have fields := frame.objects ref "prim.graph.Edge" valid.1 valid.2 (by simp [Client.protection])
    have reads : ∀ field, after.readField ref field = before.readField ref field := by
      intro field
      simp [Heap.readField,fields]
    exact ⟨newValid, by simp [field_Edge_target,valid,newValid,reads],
      by simp [field_Edge_weight,valid,newValid,reads],
      by simp [field_Edge_next,valid,newValid,reads]⟩

theorem Storage.preserved {before after : QueueState model} (storage : Storage model before)
    (rep : model.Rep after.heap after.queueState)
    (frame : PriorityQueueAnalysis.Frame client.protection before.heap after.heap) :
    Storage model after :=
  ⟨storage.graph.preserved (graph_frame_of_protected storage.graph frame),rep,
    Nat.lt_of_lt_of_le storage.keyAllocated frame.nextRef,
    Nat.lt_of_lt_of_le storage.parentAllocated frame.nextRef,
    Nat.lt_of_lt_of_le storage.selectedAllocated frame.nextRef,storage.keyParent,storage.parentSelected,storage.separate⟩

def QueueMatches (state : QueueState model) : Prop :=
  ∀ vertex key, (vertex,key) ∈ state.entries model ↔
    state.heap.read client.selected vertex = 0 ∧
    (vertex = client.root ∨ 0 ≤ state.heap.read client.parent vertex) ∧ key = state.heap.read client.key vertex

/-- Weighted implementation-clock work is independent of the six client clocks. -/
def work (before after : Heap) : Nat := Clocks.weighted model.metric (Heap.cost before after)

theorem work_triangle (a b c : Heap) : work model a c ≤ work model a b + work model b c := by
  rw [work,work,work,← Clocks.weighted_add]
  apply Clocks.weighted_le
  intro name
  simp only [Heap.cost,Clocks.add]
  omega

structure CostBounds (before after : QueueState model) (vertices edges : Nat) : Prop where
  updates : Heap.cost before.heap after.heap "queue_updates" ≤ edges
  pops : Heap.cost before.heap after.heap "queue_pops" ≤ vertices
  checks : Heap.cost before.heap after.heap "queue_empty_checks" ≤ vertices
  visits : Heap.cost before.heap after.heap "edges" ≤ edges
  improvements : Heap.cost before.heap after.heap "improvements" ≤ edges
  settlements : Heap.cost before.heap after.heap "settlements" ≤ vertices
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.updateBudget * edges + model.popBudget * vertices

theorem CostBounds.refl (state : QueueState model) : CostBounds model state state 0 0 := by
  have zero : Heap.cost state.heap state.heap = (fun _ => 0) := by
    funext name
    simp [Heap.cost]
  constructor <;> simp [zero,work]

theorem CostBounds.trans {a b c : QueueState model} {v e v' e' : Nat}
    (one : CostBounds model a b v e) (two : CostBounds model b c v' e') :
    CostBounds model a c (v+v') (e+e') := by
  have cost (name : String) : Heap.cost a.heap c.heap name ≤
      Heap.cost a.heap b.heap name + Heap.cost b.heap c.heap name := by
    simp only [Heap.cost]
    omega
  refine ⟨Nat.le_trans (cost _) (Nat.add_le_add one.updates two.updates),
    Nat.le_trans (cost _) (Nat.add_le_add one.pops two.pops),
    Nat.le_trans (cost _) (Nat.add_le_add one.checks two.checks),
    Nat.le_trans (cost _) (Nat.add_le_add one.visits two.visits),
    Nat.le_trans (cost _) (Nat.add_le_add one.improvements two.improvements),
    Nat.le_trans (cost _) (Nat.add_le_add one.settlements two.settlements), ?_⟩
  have triangle := work_triangle model a.heap b.heap c.heap
  have first := one.amortized
  have second := two.amortized
  simp only [Nat.mul_add]
  omega

theorem CostBounds.weaken {a b : QueueState model} {v e v' e' : Nat}
    (one : CostBounds model a b v e) (vertices : v ≤ v') (edges : e ≤ e') :
    CostBounds model a b v' e' := by
  refine ⟨Nat.le_trans one.updates edges,Nat.le_trans one.pops vertices,Nat.le_trans one.checks vertices,
    Nat.le_trans one.visits edges,Nat.le_trans one.improvements edges,Nat.le_trans one.settlements vertices,?_⟩
  exact Nat.le_trans one.amortized (Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ edges) _)
    (Nat.mul_le_mul_left _ vertices))

variable (contracts : Contracts model reservedClocks)
include contracts

theorem work_tick_left (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model (before.tick name) after = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]

theorem work_tick_right (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model before (after.tick name) = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]

structure QueueUpdated (before after : QueueState model) (vertex key : Int) : Prop where
  execution : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue before.heap
    (client.queue,vertex,key) after.heap ()
  storage : Storage model after
  contents : ∀ v k, (v,k) ∈ after.entries model ↔
    (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v,k) ∈ before.entries model)
  key : after.heap.read client.key = before.heap.read client.key
  parent : after.heap.read client.parent = before.heap.read client.parent
  selected : after.heap.read client.selected = before.heap.read client.selected
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : PreservesClocks reservedClocks before.heap after.heap
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.updateBudget

structure QueueExtracted (before after : QueueState model) (vertex key : Int) : Prop where
  execution : PriorityQueue.pop_min.Call dependencies.PriorityQueue before.heap client.queue after.heap vertex
  storage : Storage model after
  member : (vertex,key) ∈ before.entries model
  least : ∀ v k, (v,k) ∈ before.entries model → key ≤ k
  contents : ∀ v k, (v,k) ∈ after.entries model ↔ v ≠ vertex ∧ (v,k) ∈ before.entries model
  key : after.heap.read client.key = before.heap.read client.key
  parent : after.heap.read client.parent = before.heap.read client.parent
  selected : after.heap.read client.selected = before.heap.read client.selected
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : PreservesClocks reservedClocks before.heap after.heap
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.popBudget

theorem queue_update (state : QueueState model) (vertex key : Int) (storage : Storage model state)
    (lower : 0 ≤ vertex) (upper : vertex < model.capacity)
    (improves : ∀ old, (vertex,old) ∈ state.entries model → key < old) :
    ∃ after, QueueUpdated model state after vertex key := by
  obtain ⟨heap,next,effect⟩ := contracts.update state.heap state.queueState vertex key storage.queue lower upper improves
  exact ⟨⟨heap,next⟩,effect.execution,storage.preserved model effect.represented effect.frame,effect.contents,
    effect.frame.sequences _ (by simp [Client.protection]) storage.keyAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.parentAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.selectedAllocated,
    graph_frame_of_protected storage.graph effect.frame,effect.clocks,effect.amortized⟩

theorem queue_extract (state : QueueState model) (storage : Storage model state)
    (nonempty : state.entries model ≠ []) : ∃ after vertex key, QueueExtracted model state after vertex key := by
  obtain ⟨heap,next,vertex,key,effect⟩ := contracts.extract state.heap state.queueState storage.queue nonempty
  exact ⟨⟨heap,next⟩,vertex,key,effect.execution,storage.preserved model effect.represented effect.frame,
    effect.selected,effect.least,effect.contents,
    effect.frame.sequences _ (by simp [Client.protection]) storage.keyAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.parentAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.selectedAllocated,
    graph_frame_of_protected storage.graph effect.frame,effect.clocks,effect.amortized⟩

theorem skip_edge_cost (state : QueueState model) :
    CostBounds model state (state.tick model "edges") 0 1 := by
  have zero : work model state.heap state.heap = 0 := Heap.weightedCost_self _ _
  constructor <;> try simp [QueueState.tick,Heap.cost,Heap.tick]
  change work model state.heap (state.heap.tick "edges") + _ ≤ _
  rw [work_tick_right model contracts _ _ "edges" (by simp [reservedClocks]),zero]
  simp

theorem updated_edge_cost {state after : QueueState model} {vertex target candidate : Int}
    (effect : QueueUpdated model
      ((((state.tick model "edges").write model client.key target candidate).write model client.parent target vertex).tick model "queue_updates")
      after target candidate) :
    CostBounds model state (after.tick model "improvements") 0 1 := by
  have clocks (name) (member : name ∈ reservedClocks) := effect.bookkeeping name member
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have same := clocks "queue_updates" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_pops" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_empty_checks" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "edges" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "improvements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "settlements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have bound := effect.amortized
    change work model ((((state.heap.tick "edges").write client.key target candidate).write client.parent target vertex).tick "queue_updates")
      after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "queue_updates" (by simp [reservedClocks])] at bound
    change work model (state.heap.tick "edges") after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "edges" (by simp [reservedClocks])] at bound
    change work model state.heap (after.heap.tick "improvements") + _ ≤ _
    rw [work_tick_right model contracts _ _ "improvements" (by simp [reservedClocks])]
    simpa [QueueState.tick,QueueState.write] using bound

theorem extracted_selected_cost {state after : QueueState model} {vertex key : Int}
    (effect : QueueExtracted model ((state.tick model "queue_empty_checks").tick model "queue_pops")
      after vertex key) :
    CostBounds model state ((after.write model client.selected vertex 1).tick model "settlements") 1 0 := by
  have clocks (name) (member : name ∈ reservedClocks) := effect.bookkeeping name member
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have same := clocks "queue_updates" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_pops" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_empty_checks" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "edges" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "improvements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "settlements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have bound := effect.amortized
    change work model ((state.heap.tick "queue_empty_checks").tick "queue_pops") after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "queue_pops" (by simp [reservedClocks]),
      work_tick_left model contracts _ _ "queue_empty_checks" (by simp [reservedClocks])] at bound
    change work model state.heap ((after.heap.write client.selected vertex 1).tick "settlements") + _ ≤ _
    rw [work_tick_right model contracts _ _ "settlements" (by simp [reservedClocks])]
    simpa [QueueState.tick,QueueState.write] using! bound


end PrimAnalysis
