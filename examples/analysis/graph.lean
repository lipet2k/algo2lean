import GraphGeneratedPoints
import Algo2LeanLib.Dijkstra

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Shared mutable adjacency-list graph contracts for both Dijkstra backends. -/

namespace GraphAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra

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
      (weightNonnegative : 0 ≤ weight)
      (remaining : AdjacencyChain heap size next tail) :
      AdjacencyChain heap size (some edge) ((target, weight) :: tail)

/-- The public graph fields represent one finite adjacency list per vertex.
    Parallel edges, zero weights, self-loops, and shared suffixes are allowed. -/
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

/-- The generated input-data helper also describes the executed constructor's
    exact effect; the proof follows the three field assignments once. -/
theorem edge_constructor_summary (heap : Heap) (target weight : Int) (next : Option Ref_Edge)
    (nextValid : ∀ ref ∈ next, is_Edge heap ref) :
    Edge.Call heap (target, weight, next) (create_Edge heap target weight next).1
      (create_Edge heap target weight next).2 := by
  have allocated : is_Edge (heap.allocateObject "Edge") heap.nextObject := by simp [is_Edge]
  refine ⟨nextValid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Edge_pc9 _ _ _)
  apply Reaches.prepend (Step.Edge_pc8 _ _ _)
  apply Reaches.prepend (Step.Edge_pc7 _ _ _)
  apply Reaches.prepend (Step.Edge_pc6 _ _ _)
  apply Reaches.prepend (Step.Edge_pc5 _ _ _)
  apply Reaches.prepend (Step.Edge_pc4 _ _ _)
  apply Reaches.prepend (Step.Edge_pc3 _ _ _)
  apply Reaches.prepend (Step.Edge___init___pc5 _ _ _ allocated)
  apply Reaches.prepend (Step.Edge___init___pc4 _ _ _
    (by simp [is_Edge, set_Edge_target]))
  apply Reaches.prepend (Step.Edge___init___pc3 _ _ _
    (by simp [is_Edge, set_Edge_target, set_Edge_weight]))
  apply Reaches.prepend (Step.Edge___init___pc2 _ _ _)
  apply Reaches.prepend (Step.Edge___init___pc1 _ _ _)
  apply Reaches.prepend (Step.Edge_pc2 _ _ _)
  exact Reaches.single (Step.Edge_pc1 _ _ _
    (by simp [is_Edge, set_Edge_target, set_Edge_weight, set_Edge_next]))

theorem create_edge_preserves_fields (heap : Heap) (target weight : Int) (next : Option Ref_Edge)
    (ref : ObjectRef) (old : ref < heap.nextObject) :
    (create_Edge heap target weight next).1.objectClass ref = heap.objectClass ref ∧
    ∀ field, (create_Edge heap target weight next).1.readField ref field = heap.readField ref field := by
  have different : ref ≠ heap.nextObject := Nat.ne_of_lt old
  constructor
  · simp only [create_Edge, set_Edge_target, set_Edge_weight, set_Edge_next, Heap.objectClass_writeField]
    simp [Heap.objectClass, Heap.objects_allocateObject_old heap "Edge" ref old]
  · intro field
    simp only [create_Edge, set_Edge_target, set_Edge_weight, set_Edge_next,
      Heap.readField_writeField_other_ref _ _ _ _ _ _ different]
    simp [Heap.readField, Heap.objects_allocateObject_old heap "Edge" ref old]

theorem create_edge_preserves_graph (heap : Heap) (target weight : Int) (next : Option Ref_Edge)
    (graph : Ref_Graph) (valid : is_Graph heap graph) :
    is_Graph (create_Edge heap target weight next).1 graph ∧
    field_Graph_size (create_Edge heap target weight next).1 graph = field_Graph_size heap graph ∧
    field_Graph_heads (create_Edge heap target weight next).1 graph = field_Graph_heads heap graph := by
  have fields := create_edge_preserves_fields heap target weight next graph valid.1
  have newValid : is_Graph (create_Edge heap target weight next).1 graph := by
    refine ⟨?_, fields.1.trans valid.2⟩
    change graph < heap.nextObject + 1
    exact Nat.lt_succ_of_lt valid.1
  exact ⟨newValid, by simp [field_Graph_size, newValid, valid, fields.2],
    by simp [field_Graph_heads, newValid, valid, fields.2]⟩

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
  have preserved := create_edge_preserves_graph heap target weight next graph valid
  have newHeads : field_Graph_heads (create_Edge heap target weight next).1 graph = some heads :=
    preserved.2.2.trans readHeads
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Graph_add_edge_pc13 _ _ _ (by simp [readSize]))
  apply Reaches.prepend (Step.Graph_add_edge_pc12_false _ _ _ (by simp [readSize]; omega))
  apply Reaches.prepend (Step.Graph_add_edge_pc9 _ _ _)
  apply Reaches.prepend (Step.Graph_add_edge_pc8 _ _ _)
  apply Reaches.prepend (Step.Graph_add_edge_pc7 _ _ _ (by simp [readHeads, readNext]))
  apply Reaches.prepend (Step.Graph_add_edge_pc6 _ _ _)
  simp only [readHeads, readNext, Option.getD_some]
  apply Reaches.trans ((edge_constructor_summary heap target weight next nextValid).2 _)
  apply Reaches.prepend (Step.Graph_add_edge_pc5 _ _ _ (by simp [newHeads]))
  apply Reaches.prepend (Step.Graph_add_edge_pc4 _ _ _)
  apply Reaches.prepend (Step.Graph_add_edge_pc3 _ _ _ (by simpa [newHeads] using! headsValid))
  apply Reaches.prepend (Step.Graph_add_edge_pc2 _ _ _)
  simpa [addedEdgeHeap, newHeads] using Reaches.single (Step.Graph_add_edge_pc1 _ _ caller)

/-- Existing edge identities and all three observable fields are preserved. -/
def EdgeFieldsUnchanged (before after : Heap) : Prop :=
  ∀ ref, is_Edge before ref → is_Edge after ref ∧
    field_Edge_target after ref = field_Edge_target before ref ∧
    field_Edge_weight after ref = field_Edge_weight before ref ∧
    field_Edge_next after ref = field_Edge_next before ref

theorem create_edge_preserves_edges (heap : Heap) (target weight : Int) (next : Option Ref_Edge) :
    EdgeFieldsUnchanged heap (create_Edge heap target weight next).1 := by
  intro ref valid
  have fields := create_edge_preserves_fields heap target weight next ref valid.1
  have newValid : is_Edge (create_Edge heap target weight next).1 ref := by
    refine ⟨?_, fields.1.trans valid.2⟩
    exact Nat.lt_succ_of_lt valid.1
  exact ⟨newValid, by simp [field_Edge_target, newValid, valid, fields.2],
    by simp [field_Edge_weight, newValid, valid, fields.2],
    by simp [field_Edge_next, newValid, valid, fields.2]⟩

theorem added_edge_preserves_edges (heap : Heap) (heads : CollectionRef) (source target weight : Int)
    (next : Option Ref_Edge) :
    EdgeFieldsUnchanged heap (addedEdgeHeap heap heads source target weight next) := by
  exact create_edge_preserves_edges heap target weight next

theorem AdjacencyChain.preserved {before after : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain before size head edges)
    (unchanged : EdgeFieldsUnchanged before after) : AdjacencyChain after size head edges := by
  induction chain with
  | empty => exact .empty
  | cons edge target weight next tail valid readTarget readWeight readNext nonnegative bound weightBound chain ih =>
    obtain ⟨newValid, targetSame, weightSame, nextSame⟩ := unchanged edge valid
    exact .cons edge target weight next tail newValid (targetSame.trans readTarget)
      (weightSame.trans readWeight) (nextSame.trans readNext) nonnegative bound weightBound ih

theorem created_edge_fields (heap : Heap) (target weight : Int) (next : Option Ref_Edge) :
    is_Edge (create_Edge heap target weight next).1 heap.nextObject ∧
    field_Edge_target (create_Edge heap target weight next).1 heap.nextObject = some target ∧
    field_Edge_weight (create_Edge heap target weight next).1 heap.nextObject = some weight ∧
    field_Edge_next (create_Edge heap target weight next).1 heap.nextObject = some next := by
  have valid : is_Edge (create_Edge heap target weight next).1 heap.nextObject := by
    simp [create_Edge, is_Edge, set_Edge_target, set_Edge_weight, set_Edge_next]
  refine ⟨valid, ?_, ?_, ?_⟩
  · simp [field_Edge_target, is_Edge, create_Edge, set_Edge_target, set_Edge_weight,
      set_Edge_next, ObjectValue.asInt]
  · simp [field_Edge_weight, is_Edge, create_Edge, set_Edge_target, set_Edge_weight,
      set_Edge_next, ObjectValue.asInt]
  · cases next <;> simp [field_Edge_next, is_Edge, create_Edge, set_Edge_target,
      set_Edge_weight, set_Edge_next, ObjectValue.asNullableObject]

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
  obtain ⟨next, readNext, chain⟩ := representation.chains source sourceNonnegative sourceBound
  let after := addedEdgeHeap heap heads source target weight next
  have construction := add_edge_summary heap graph size heads source target weight next
    representation.valid representation.readSize representation.readHeads representation.headsValid
    readNext chain.head_valid sourceNonnegative sourceBound targetNonnegative targetBound weightNonnegative
  have graphPreserved := create_edge_preserves_graph heap target weight next graph representation.valid
  have headsStillValid : seq_Edge_optional.valid (create_Edge heap target weight next).1 heads :=
    representation.headsValid
  refine ⟨after, construction, ?_, ?_⟩
  · refine ⟨graphPreserved.1, representation.sizeNonnegative,
      graphPreserved.2.1.trans representation.readSize, graphPreserved.2.2.trans representation.readHeads,
      ?_, ?_⟩
    · exact (seq_Edge_optional.valid_set _ heads heads source (some heap.nextObject)).2 headsStillValid
    · intro vertex nonnegative bound
      by_cases same : vertex = source
      · subst vertex
        refine ⟨some heap.nextObject, ?_, ?_⟩
        · exact seq_Edge_optional.get_set_same _ heads source (some heap.nextObject) headsStillValid
        · obtain ⟨valid, readTarget, readWeight, readTail⟩ := created_edge_fields heap target weight next
          simpa [prependEdge] using
            AdjacencyChain.cons (heap := after) heap.nextObject target weight next (adjacency source)
              valid readTarget readWeight readTail targetNonnegative targetBound weightNonnegative
              (chain.preserved (added_edge_preserves_edges heap heads source target weight next))
      · obtain ⟨head, observed, oldChain⟩ := representation.chains vertex nonnegative bound
        refine ⟨head, ?_, ?_⟩
        · change seq_Edge_optional.get
            (seq_Edge_optional.set (create_Edge heap target weight next).1 heads source (some heap.nextObject))
            heads vertex = some head
          rw [seq_Edge_optional.get_set_other_index _ heads vertex source _ same]
          exact observed
        · simpa only [prependEdge, if_neg same] using
            oldChain.preserved (added_edge_preserves_edges heap heads source target weight next)
  · funext name
    change heap.clocks name - heap.clocks name = 0
    omega

theorem AdjacencyChain.member_valid {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges)
    (target weight : Int) (member : (target, weight) ∈ edges) :
    0 ≤ target ∧ target < size ∧ 0 ≤ weight := by
  induction chain with
  | empty => simp at member
  | cons edge first firstWeight next tail valid readTarget readWeight readNext lower upper nonnegative chain ih =>
    simp only [List.mem_cons] at member
    rcases member with same | remaining
    · cases same
      exact ⟨lower, upper, nonnegative⟩
    · exact ih remaining

theorem GraphRep.nonnegative_edges {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) :
    NonnegativeEdges (representedEdges size adjacency) := by
  intro source target weight connection
  obtain ⟨head, _, chain⟩ := representation.chains source connection.1 connection.2.1
  exact (chain.member_valid target weight connection.2.2).2.2

theorem GraphRep.edge_endpoints {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency)
    (source target weight : Int) (connection : representedEdges size adjacency source target weight) :
    0 ≤ source ∧ source < size ∧ 0 ≤ target ∧ target < size := by
  obtain ⟨head, _, chain⟩ := representation.chains source connection.1 connection.2.1
  have bounds := chain.member_valid target weight connection.2.2
  exact ⟨connection.1, connection.2.1, bounds.1, bounds.2.1⟩

/-- Rejected endpoints and negative weights return `false` without allocating
    an edge, modifying the adjacency lists, or changing a clock. -/
theorem add_invalid_edge_summary (heap : Heap) (graph : Ref_Graph) (size source target weight : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (invalid : source < 0 ∨ size ≤ source ∨ target < 0 ∨ size ≤ target ∨ weight < 0) :
    Graph.add_edge.Call heap (graph, source, target, weight) heap false := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Graph_add_edge_pc13 _ _ _ (by simp [readSize]))
  apply Reaches.prepend (Step.Graph_add_edge_pc12_true _ _ _ (by simp [readSize]; omega))
  apply Reaches.prepend (Step.Graph_add_edge_pc11 _ _ _)
  exact Reaches.single (Step.Graph_add_edge_pc10 _ _ _)

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
    (seq_Edge_optional.const heap none).1.objectClass ref = heap.objectClass ref := rfl

@[simp] theorem optional_edges_field (heap : Heap) (ref : ObjectRef) (field : String) :
    (seq_Edge_optional.const heap none).1.readField ref field = heap.readField ref field := rfl

@[simp] theorem optional_edges_next_object (heap : Heap) :
    (seq_Edge_optional.const heap none).1.nextObject = heap.nextObject := rfl

@[simp] theorem sized_graph_next_collection (heap : Heap) (graph : Ref_Graph) (size : Int) :
    (sizedGraphHeap heap graph size).nextCollection = heap.nextCollection := by
  by_cases negative : size < 0 <;> simp [sizedGraphHeap, negative, set_Graph_size]

@[simp] theorem optional_edges_valid_write_field (heap : Heap) (object : ObjectRef)
    (field : String) (value : ObjectValue) (heads : CollectionRef) :
    seq_Edge_optional.valid (heap.writeField object field value) heads ↔ seq_Edge_optional.valid heap heads := Iff.rfl

@[simp] theorem optional_edges_get_write_field (heap : Heap) (object : ObjectRef)
    (field : String) (value : ObjectValue) (heads : CollectionRef) (index : Int) :
    seq_Edge_optional.get (heap.writeField object field value) heads index =
      seq_Edge_optional.get heap heads index := rfl

theorem initialized_graph_valid (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) : is_Graph (initializedGraphHeap heap graph size) graph := by
  by_cases negative : size < 0 <;>
    simpa [initializedGraphHeap, sizedGraphHeap, negative, is_Graph, set_Graph_size,
      set_Graph_heads] using valid

theorem graph_initialization_summary (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) :
    Graph.__init__.Call heap (graph, size) (initializedGraphHeap heap graph size) () := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Graph___init___pc10 _ _ _ valid)
  apply Reaches.prepend (Step.Graph___init___pc9 _ _ _)
  by_cases negative : size < 0
  · apply Reaches.prepend (Step.Graph___init___pc8_true _ _ _ (by simp [negative]))
    apply Reaches.prepend (Step.Graph___init___pc7 _ _ _
      (by simpa [is_Graph, set_Graph_size] using valid))
    apply Reaches.prepend (Step.Graph___init___pc6 _ _ _)
    apply Reaches.prepend (Step.Graph___init___pc5 _ _ _)
    apply Reaches.prepend (Step.Graph___init___pc4 _ _ _)
    apply Reaches.prepend (Step.Graph___init___pc3 _ _ _
      (by simpa [is_Graph, set_Graph_size] using valid))
    apply Reaches.prepend (Step.Graph___init___pc2 _ _ _)
    simpa [initializedGraphHeap, sizedGraphHeap, negative] using!
      Reaches.single (Step.Graph___init___pc1 _ _ caller)
  · apply Reaches.prepend (Step.Graph___init___pc8_false _ _ _ (by simp [negative]))
    apply Reaches.prepend (Step.Graph___init___pc6 _ _ _)
    apply Reaches.prepend (Step.Graph___init___pc5 _ _ _)
    apply Reaches.prepend (Step.Graph___init___pc4 _ _ _)
    apply Reaches.prepend (Step.Graph___init___pc3 _ _ _
      (by simpa [is_Graph, set_Graph_size] using valid))
    apply Reaches.prepend (Step.Graph___init___pc2 _ _ _)
    simpa [initializedGraphHeap, sizedGraphHeap, negative] using!
      Reaches.single (Step.Graph___init___pc1 _ _ caller)

theorem graph_constructor_summary (heap : Heap) (size : Int) :
    Graph.Call heap size (newGraphHeap heap size) heap.nextObject := by
  have allocated : is_Graph (heap.allocateObject "Graph") heap.nextObject := by simp [is_Graph]
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.Graph_pc7 _ _ _)
  apply Reaches.prepend (Step.Graph_pc6 _ _ _)
  apply Reaches.prepend (Step.Graph_pc5 _ _ _)
  apply Reaches.prepend (Step.Graph_pc4 _ _ _)
  apply Reaches.prepend (Step.Graph_pc3 _ _ _)
  apply Reaches.trans ((graph_initialization_summary _ _ size allocated).2 _)
  apply Reaches.prepend (Step.Graph_pc2 _ _ _)
  exact Reaches.single (Step.Graph_pc1 _ _ _ (initialized_graph_valid _ _ size allocated))

theorem initialized_graph_size (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) :
    field_Graph_size (initializedGraphHeap heap graph size) graph = some (max 0 size) := by
  have finalValid := initialized_graph_valid heap graph size valid
  rw [field_Graph_size, if_pos finalValid]
  by_cases negative : size < 0
  · have normalized : max 0 size = 0 := Int.max_eq_left (by omega)
    simp [initializedGraphHeap, sizedGraphHeap, negative, normalized, set_Graph_heads,
      set_Graph_size, valid.2, ObjectValue.asInt]
  · have normalized : max 0 size = size := Int.max_eq_right (by omega)
    simp [initializedGraphHeap, sizedGraphHeap, negative, normalized, set_Graph_heads,
      set_Graph_size, valid.2, ObjectValue.asInt]

theorem initialized_graph_heads (heap : Heap) (graph : Ref_Graph) (size : Int)
    (valid : is_Graph heap graph) :
    field_Graph_heads (initializedGraphHeap heap graph size) graph = some heap.nextCollection := by
  have sizedValid : is_Graph (sizedGraphHeap heap graph size) graph := by
    by_cases negative : size < 0 <;>
      simpa [sizedGraphHeap, negative, is_Graph, set_Graph_size] using valid
  have headsValid : is_Graph (seq_Edge_optional.const (sizedGraphHeap heap graph size) none).1 graph := by
    simpa [is_Graph] using sizedValid
  have headsRef : (seq_Edge_optional.const (sizedGraphHeap heap graph size) none).2 = heap.nextCollection := by
    exact sized_graph_next_collection heap graph size
  unfold initializedGraphHeap
  rw [field_Graph_heads_set _ _ _ headsValid, headsRef]

theorem initialized_graph_empty (heap : Heap) (graph : Ref_Graph) (size : Int) :
    seq_Edge_optional.valid (initializedGraphHeap heap graph size) heap.nextCollection ∧
    ∀ vertex, seq_Edge_optional.get (initializedGraphHeap heap graph size) heap.nextCollection vertex = some none := by
  have headsRef : (seq_Edge_optional.const (sizedGraphHeap heap graph size) none).2 = heap.nextCollection := by
    exact sized_graph_next_collection heap graph size
  constructor
  · unfold initializedGraphHeap
    simp only [set_Graph_heads, optional_edges_valid_write_field]
    rw [← headsRef]
    exact seq_Edge_optional.valid_const _ none
  · intro vertex
    unfold initializedGraphHeap
    simp only [set_Graph_heads, optional_edges_get_write_field]
    rw [← headsRef]
    exact seq_Edge_optional.get_const _ none vertex

theorem graph_constructor_representation (heap : Heap) (size : Int) :
    GraphRep (newGraphHeap heap size) heap.nextObject (max 0 size) heap.nextCollection (fun _ => []) := by
  have allocated : is_Graph (heap.allocateObject "Graph") heap.nextObject := by simp [is_Graph]
  have empty := initialized_graph_empty (heap.allocateObject "Graph") heap.nextObject size
  refine ⟨initialized_graph_valid _ _ size allocated, Int.le_max_left _ _,
    initialized_graph_size _ _ size allocated, initialized_graph_heads _ _ size allocated,
    empty.1, ?_⟩
  intro vertex _ _
  exact ⟨none, empty.2 vertex, .empty⟩

/-- Construction allocates one graph and one heads collection. Existing
    integer sequences, objects, collections, and every clock are preserved. -/
theorem graph_constructor_preserves_storage (heap : Heap) (size : Int) :
    (newGraphHeap heap size).store = heap.store ∧
    (∀ ref, ref < heap.nextObject → (newGraphHeap heap size).objects ref = heap.objects ref) ∧
    (∀ ref, ref < heap.nextCollection → (newGraphHeap heap size).collections ref = heap.collections ref) ∧
    (newGraphHeap heap size).clocks = heap.clocks := by
  by_cases negative : size < 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [newGraphHeap, initializedGraphHeap, sizedGraphHeap, negative,
        set_Graph_size, set_Graph_heads, SequenceType.const, SequenceType.create, Heap.createSequence]
    · intro ref old
      have different := Nat.ne_of_lt old
      simp [newGraphHeap, initializedGraphHeap, sizedGraphHeap, negative,
        set_Graph_size, set_Graph_heads, SequenceType.const, SequenceType.create, Heap.createSequence,
        Heap.writeField, Heap.allocateObject, different]
    · intro ref old
      simp [newGraphHeap, initializedGraphHeap, sizedGraphHeap, negative,
        set_Graph_size, set_Graph_heads, SequenceType.const, SequenceType.create, Heap.createSequence,
        Heap.allocateSequence, Nat.ne_of_lt old]
    · simp [newGraphHeap, initializedGraphHeap, sizedGraphHeap, negative,
        set_Graph_size, set_Graph_heads, SequenceType.const, SequenceType.create, Heap.createSequence]

theorem graph_constructor_verified (heap : Heap) (size : Int) :
    Graph.Call heap size (newGraphHeap heap size) heap.nextObject ∧
    GraphRep (newGraphHeap heap size) heap.nextObject (max 0 size) heap.nextCollection (fun _ => []) ∧
    Heap.cost heap (newGraphHeap heap size) = (fun _ => 0) := by
  refine ⟨graph_constructor_summary heap size, graph_constructor_representation heap size, ?_⟩
  funext name
  simp [Heap.cost, (graph_constructor_preserves_storage heap size).2.2.2]

/-- A frame condition for graph reasoning: only graph fields, adjacency heads,
    and existing edge fields matter. Distances, queue arrays, and clocks may
    change freely when these observations are preserved. -/
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

/-- A nonempty adjacency observation exposes one edge and a strictly shorter
    tail. These are the facts needed for an edge-loop induction. -/
theorem AdjacencyChain.uncons {heap : Heap} {size : Int} {edge : Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size (some edge) edges) :
    ∃ target weight next tail, edges = (target, weight) :: tail ∧
      field_Edge_target heap edge = some target ∧ field_Edge_weight heap edge = some weight ∧
      field_Edge_next heap edge = some next ∧ 0 ≤ target ∧ target < size ∧ 0 ≤ weight ∧
      AdjacencyChain heap size next tail ∧ tail.length < edges.length := by
  cases chain with
  | cons edge target weight next tail valid readTarget readWeight readNext lower upper nonnegative remaining =>
    exact ⟨target, weight, next, tail, rfl, readTarget, readWeight, readNext,
      lower, upper, nonnegative, remaining, by simp⟩

theorem AdjacencyChain.empty_iff {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges) :
    head = none ↔ edges = [] := by
  cases chain <;> simp

/-- An adjacency snapshot determines one mathematical list, despite allowing
    shared tails. Proofs can therefore reuse the same finite-length measure. -/
theorem AdjacencyChain.unique {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {first second : List (Int × Int)} (one : AdjacencyChain heap size head first)
    (two : AdjacencyChain heap size head second) : first = second := by
  induction one generalizing second with
  | empty =>
    cases two
    rfl
  | cons edge target weight next tail valid readTarget readWeight readNext lower upper nonnegative remaining ih =>
    cases two with
    | cons edge otherTarget otherWeight otherNext otherTail otherValid otherReadTarget otherReadWeight otherReadNext
        otherLower otherUpper otherNonnegative otherRemaining =>
      have targets : target = otherTarget := Option.some.inj (readTarget.symm.trans otherReadTarget)
      have weights : weight = otherWeight := Option.some.inj (readWeight.symm.trans otherReadWeight)
      have nexts : next = otherNext := Option.some.inj (readNext.symm.trans otherReadNext)
      subst otherTarget otherWeight otherNext
      rw [ih otherRemaining]


/-- Writing an unrelated object's fields preserves all graph observations.
    Both priority-queue backends discharge the two class-tag inequalities. -/
theorem graph_frame_foreign_field (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (object : ObjectRef) (className : String) (classTag : heap.objectClass object = some className)
    (notGraph : className ≠ "Graph") (notEdge : className ≠ "Edge")
    (field : String) (value : ObjectValue) :
    GraphFrame heap (heap.writeField object field value) graph heads := by
  have sameGraph : is_Graph (heap.writeField object field value) graph ↔ is_Graph heap graph := by
    simp [is_Graph]
  have graphDifferent : is_Graph heap graph → graph ≠ object := by
    intro valid same
    subst graph
    exact notGraph (Option.some.inj (classTag.symm.trans valid.2))
  refine ⟨sameGraph.mpr, ?_, ?_, id, fun _ => rfl, ?_⟩
  · simp only [field_Graph_size, sameGraph]
    by_cases valid : is_Graph heap graph
    · simp [valid, graphDifferent valid]
    · simp [valid]
  · simp only [field_Graph_heads, sameGraph]
    by_cases valid : is_Graph heap graph
    · simp [valid, graphDifferent valid]
    · simp [valid]
  · intro ref valid
    have different : ref ≠ object := by
      intro same
      subst ref
      exact notEdge (Option.some.inj (classTag.symm.trans valid.2))
    have newValid : is_Edge (heap.writeField object field value) ref := by simpa [is_Edge] using valid
    exact ⟨newValid, by simp [field_Edge_target, newValid, valid, different],
      by simp [field_Edge_weight, newValid, valid, different],
      by simp [field_Edge_next, newValid, valid, different]⟩

/-- The graph interface observes only the object and collection stores. -/
theorem GraphFrame.same_storage {before after : Heap} (graph : Ref_Graph) (heads : CollectionRef)
    (nextObject : after.nextObject = before.nextObject) (objects : after.objects = before.objects)
    (nextCollection : after.nextCollection = before.nextCollection)
    (collections : after.collections = before.collections) : GraphFrame before after graph heads := by
  rcases before with ⟨nr, values, no, objects, clocks, nc, collections⟩
  rcases after with ⟨nr', values', no', objects', clocks', nc', collections'⟩
  dsimp at nextObject objects nextCollection collections
  subst no' objects' nc' collections'
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

end GraphAnalysis
