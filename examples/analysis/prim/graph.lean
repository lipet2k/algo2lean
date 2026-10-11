import Algo.prim.graph.Generated
import Algo2LeanLib.Dijkstra
import Algo2LeanLib.KruskalMath

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Representation and preservation of finite adjacency lists with signed weights. -/
namespace PrimGraph
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated

inductive AdjacencyChain (heap : Heap) (size : Int) :
    Option Ref_Edge → List (Int × Int) → Prop where
  | empty : AdjacencyChain heap size none []
  | cons (edge : Ref_Edge) (target weight : Int) (next : Option Ref_Edge)
      (tail : List (Int × Int))
      (valid : is_Edge heap edge)
      (readTarget : field_Edge_target heap edge = some target)
      (readWeight : field_Edge_weight heap edge = some weight)
      (readNext : field_Edge_next heap edge = some next)
      (targetNonnegative : 0 ≤ target) (targetBound : target < size)
      (remaining : AdjacencyChain heap size next tail) :
      AdjacencyChain heap size (some edge) ((target, weight) :: tail)

/-- The public graph fields represent one finite adjacency list per vertex.
    Parallel edges, signed weights, self-loops, and shared suffixes are allowed. -/
structure GraphRep (heap : Heap) (graph : Ref_Graph) (size : Int) (heads : CollectionRef)
    (adjacency : Adjacency) : Prop where
  valid : is_Graph heap graph
  sizeNonnegative : 0 ≤ size
  readSize : field_Graph_size heap graph = some size
  readHeads : field_Graph_heads heap graph = some heads
  headsValid : seq_Edge_optional.valid heap heads
  chains : ∀ vertex, 0 ≤ vertex → vertex < size →
    ∃ head, seq_Edge_optional.get heap heads vertex = some head ∧
      AdjacencyChain heap size head (adjacency vertex)

theorem AdjacencyChain.head_valid {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges) :
    ∀ ref ∈ head, is_Edge heap ref := by
  cases chain with
  | empty => simp
  | cons edge target weight next tail valid => simpa using valid


def EdgeFieldsUnchanged (before after : Heap) : Prop :=
  ∀ ref, is_Edge before ref → is_Edge after ref ∧
    field_Edge_target after ref = field_Edge_target before ref ∧
    field_Edge_weight after ref = field_Edge_weight before ref ∧
    field_Edge_next after ref = field_Edge_next before ref


theorem AdjacencyChain.preserved {before after : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain before size head edges)
    (unchanged : EdgeFieldsUnchanged before after) : AdjacencyChain after size head edges := by
  induction chain with
  | empty => exact .empty
  | cons edge target weight next tail valid readTarget readWeight readNext nonnegative bound chain ih =>
    obtain ⟨newValid, targetSame, weightSame, nextSame⟩ := unchanged edge valid
    exact .cons edge target weight next tail newValid (targetSame.trans readTarget)
      (weightSame.trans readWeight) (nextSame.trans readNext) nonnegative bound ih


theorem AdjacencyChain.member_valid {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges)
    (target weight : Int) (member : (target, weight) ∈ edges) :
    0 ≤ target ∧ target < size := by
  induction chain with
  | empty => simp at member
  | cons edge first firstWeight next tail valid readTarget readWeight readNext lower upper chain ih =>
    simp only [List.mem_cons] at member
    rcases member with same | remaining
    · cases same
      exact ⟨lower, upper⟩
    · exact ih remaining

structure GraphFrame (before after : Heap) (graph : Ref_Graph) (heads : CollectionRef) : Prop where
  valid : is_Graph before graph → is_Graph after graph
  size : field_Graph_size after graph = field_Graph_size before graph
  headsField : field_Graph_heads after graph = field_Graph_heads before graph
  headsValid : seq_Edge_optional.valid before heads → seq_Edge_optional.valid after heads
  entries : ∀ vertex, seq_Edge_optional.get after heads vertex = seq_Edge_optional.get before heads vertex
  edges : EdgeFieldsUnchanged before after

theorem GraphFrame.refl (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef) :
    GraphFrame heap heap graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

theorem GraphFrame.trans {first middle last : Heap} {graph : Ref_Graph} {heads : CollectionRef}
    (one : GraphFrame first middle graph heads) (two : GraphFrame middle last graph heads) :
    GraphFrame first last graph heads := by
  refine ⟨fun valid => two.valid (one.valid valid), two.size.trans one.size,
    two.headsField.trans one.headsField, fun valid => two.headsValid (one.headsValid valid),
    fun vertex => (two.entries vertex).trans (one.entries vertex), ?_⟩
  intro ref valid
  obtain ⟨middleValid, firstTarget, firstWeight, firstNext⟩ := one.edges ref valid
  obtain ⟨lastValid, secondTarget, secondWeight, secondNext⟩ := two.edges ref middleValid
  exact ⟨lastValid, secondTarget.trans firstTarget, secondWeight.trans firstWeight, secondNext.trans firstNext⟩

theorem GraphRep.preserved {before after : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep before graph size heads adjacency)
    (frame : GraphFrame before after graph heads) : GraphRep after graph size heads adjacency := by
  refine ⟨frame.valid representation.valid, representation.sizeNonnegative,
    frame.size.trans representation.readSize, frame.headsField.trans representation.readHeads,
    frame.headsValid representation.headsValid, ?_⟩
  intro vertex nonnegative bound
  obtain ⟨head, readHead, chain⟩ := representation.chains vertex nonnegative bound
  exact ⟨head, (frame.entries vertex).trans readHead, chain.preserved frame.edges⟩

theorem graph_frame_write (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (ref : SeqRef) (index value : Int) : GraphFrame heap (heap.write ref index value) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

theorem graph_frame_allocate (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (values : Seq) : GraphFrame heap (heap.allocate values) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

theorem graph_frame_tick (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (clock : String) (amount : Nat) : GraphFrame heap (heap.tick clock amount) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩



@[simp] theorem edge_target_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_target (heap.tick clock amount) edge = field_Edge_target heap edge := rfl
@[simp] theorem edge_weight_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_weight (heap.tick clock amount) edge = field_Edge_weight heap edge := rfl
@[simp] theorem edge_next_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_next (heap.tick clock amount) edge = field_Edge_next heap edge := rfl


/-- Adjacency occurrences are ordered first by source vertex, then by their
    order in its adjacency list. Both orientations of an undirected edge remain
    distinct occurrences, including when endpoints and weights are equal. -/
def adjacencyEntries (size : Int) (adjacency : Adjacency) : List (Int × Int × Int) :=
  (vertexRange size).flatMap fun source =>
    (adjacency source).map fun entry => (source, entry)

/-- The finite mathematical input assigns each adjacency occurrence its position
    as a unique edge identity. These identities are ghost data used in proofs. -/
def inputEdges (size : Int) (adjacency : Adjacency) : List Algo2Lean.Kruskal.Edge :=
  (adjacencyEntries size adjacency).zipIdx.map fun item =>
    ⟨item.2, item.1.1, item.1.2.1, item.1.2.2⟩

theorem adjacencyEntries_member (size source target weight : Int) (adjacency : Adjacency) :
    (source, target, weight) ∈ adjacencyEntries size adjacency ↔
      0 ≤ source ∧ source < size ∧ (target, weight) ∈ adjacency source := by
  simp only [adjacencyEntries, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, member, entry, adjacent, sameSource, sameEntry⟩
    subst u
    subst entry
    exact ⟨(vertexRange_member size source).mp member |>.1,
      (vertexRange_member size source).mp member |>.2, adjacent⟩
  · rintro ⟨lower, upper, adjacent⟩
    exact ⟨source, (vertexRange_member size source).mpr ⟨lower, upper⟩,
      (target, weight), adjacent, rfl, rfl⟩

/-- Directed membership forgets only an occurrence's unique identity. -/
theorem inputEdges_member (size : Int) (adjacency : Adjacency) (source target weight : Int) :
    (∃ id, (⟨id, source, target, weight⟩ : Algo2Lean.Kruskal.Edge) ∈ inputEdges size adjacency) ↔
      0 ≤ source ∧ source < size ∧ (target, weight) ∈ adjacency source := by
  rw [← adjacencyEntries_member]
  constructor
  · rintro ⟨id, member⟩
    obtain ⟨⟨⟨u,v,w⟩, index⟩, included, same⟩ := List.mem_map.mp member
    cases same
    exact List.fst_mem_of_mem_zipIdx included
  · intro member
    obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp member
    refine ⟨index, List.mem_map.mpr ⟨((source,target,weight),index), ?_, rfl⟩⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr indexed

/-- Every represented occurrence gives the same directed adjacency observation. -/
theorem inputEdges_observation {size : Int} {adjacency : Adjacency}
    {edge : Algo2Lean.Kruskal.Edge} (member : edge ∈ inputEdges size adjacency) :
    0 ≤ edge.source ∧ edge.source < size ∧
      (edge.target, edge.weight) ∈ adjacency edge.source := by
  cases edge with
  | mk id source target weight => exact (inputEdges_member size adjacency source target weight).mp ⟨id, member⟩

/-- Occurrence identifiers are exactly a consecutive range, even for duplicate
    endpoint/weight triples and self-loops. -/
theorem inputEdges_identities (size : Int) (adjacency : Adjacency) :
    ((inputEdges size adjacency).map Algo2Lean.Kruskal.Edge.id).Nodup := by
  simpa only [inputEdges, List.map_map, Function.comp_def, List.zipIdx_map_snd] using
    List.nodup_range' (s := 0) (n := (adjacencyEntries size adjacency).length)

/-- The number of directed occurrences is the adjacency-scan budget. -/
theorem inputEdges_length (size : Int) (adjacency : Adjacency) :
    (inputEdges size adjacency).length = edgeBudget adjacency (vertexRange size) := by
  simp [inputEdges, adjacencyEntries, edgeBudget, List.length_flatMap]

/-- A represented signed-weight graph supplies the finite mathematical graph's
    endpoint bounds and unique edge identities. -/
theorem GraphRep.validInput {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) :
    Algo2Lean.Kruskal.ValidInput size.toNat (inputEdges size adjacency) := by
  refine ⟨inputEdges_identities size adjacency, ?_, ?_⟩
  · intro edge member
    obtain ⟨lower, upper, _⟩ := inputEdges_observation member
    exact ⟨lower, by omega⟩
  · intro edge member
    obtain ⟨lower, upper, adjacent⟩ := inputEdges_observation member
    obtain ⟨head, _, chain⟩ := representation.chains edge.source lower upper
    obtain ⟨nonnegative, bound⟩ := chain.member_valid edge.target edge.weight adjacent
    exact ⟨nonnegative, by omega⟩

/-- Each directed adjacency observation has an observation with reversed
    endpoints and the same weight. Parallel-edge multiplicities are irrelevant
    to this condition; individual occurrences keep their distinct identities. -/
def Symmetric (size : Int) (adjacency : Adjacency) : Prop :=
  ∀ source target weight, 0 ≤ source → source < size →
    (target,weight) ∈ adjacency source → (source,weight) ∈ adjacency target

/-- Symmetric adjacency lists give the reverse-edge witnesses needed by Prim's
    undirected cut argument. The reverse may have a different occurrence id. -/
theorem GraphRep.inputEdges_reverse {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency)
    (symmetric : Symmetric size adjacency) :
    ∀ edge ∈ inputEdges size adjacency,
      ∃ reverse ∈ inputEdges size adjacency,
        reverse.source = edge.target ∧ reverse.target = edge.source ∧
          reverse.weight = edge.weight := by
  intro edge member
  obtain ⟨lower, upper, adjacent⟩ := inputEdges_observation member
  obtain ⟨head, _, chain⟩ := representation.chains edge.source lower upper
  obtain ⟨targetLower, targetUpper⟩ := chain.member_valid edge.target edge.weight adjacent
  have reversed := symmetric edge.source edge.target edge.weight lower upper adjacent
  obtain ⟨id, included⟩ := (inputEdges_member size adjacency edge.target edge.source edge.weight).mpr
    ⟨targetLower, targetUpper, reversed⟩
  exact ⟨⟨id, edge.target, edge.source, edge.weight⟩, included, rfl, rfl, rfl⟩

end PrimGraph
