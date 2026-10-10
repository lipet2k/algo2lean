import «Algo2LeanExamples».«GraphGenerated»
import «DijkstraGenerated»
import Algo2LeanLib.Embedding

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace «GraphIntoDijkstra»

open Algo2LeanCore _root_.Algo2LeanGenerated

-- Translate only the component's control representation; the shared heap is unchanged.
def state_Edge___init__ (s : «GraphLibrary».Algo2LeanGenerated.State_Edge___init__) : Algo2LeanGenerated.State_Edge___init__ :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, t4 := s.t4 }

def state_Graph___init__ (s : «GraphLibrary».Algo2LeanGenerated.State_Graph___init__) : Algo2LeanGenerated.State_Graph___init__ :=
  { v0 := s.v0, v1 := s.v1, t2 := s.t2, t3 := s.t3, t4 := s.t4, t5 := s.t5, t6 := s.t6 }

def state_Graph_add_edge (s : «GraphLibrary».Algo2LeanGenerated.State_Graph_add_edge) : Algo2LeanGenerated.State_Graph_add_edge :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, t4 := s.t4, t5 := s.t5, t6 := s.t6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10, t11 := s.t11, t12 := s.t12 }

def state_Edge (s : «GraphLibrary».Algo2LeanGenerated.State_Edge) : Algo2LeanGenerated.State_Edge :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, t4 := s.t4, t5 := s.t5, t6 := s.t6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10 }

def state_Graph (s : «GraphLibrary».Algo2LeanGenerated.State_Graph) : Algo2LeanGenerated.State_Graph :=
  { v0 := s.v0, v1 := s.v1, t2 := s.t2, t3 := s.t3, t4 := s.t4, t5 := s.t5, t6 := s.t6 }

def encodeFrame : «GraphLibrary».Algo2LeanGenerated.Frame → Algo2LeanGenerated.Frame
  | .invalid => .invalid
  | .fn_Edge___init__ pc s => .fn_Edge___init__ pc (state_Edge___init__ s)
  | .fn_Graph___init__ pc s => .fn_Graph___init__ pc (state_Graph___init__ s)
  | .fn_Graph_add_edge pc s => .fn_Graph_add_edge pc (state_Graph_add_edge s)
  | .fn_Edge pc s => .fn_Edge pc (state_Edge s)
  | .fn_Graph pc s => .fn_Graph pc (state_Graph s)

def encodeResult : «GraphLibrary».Algo2LeanGenerated.Result → Algo2LeanGenerated.Result
  | .fn_Edge___init__ value => .fn_Edge___init__ value
  | .fn_Graph___init__ value => .fn_Graph___init__ value
  | .fn_Graph_add_edge value => .fn_Graph_add_edge value
  | .fn_Edge value => .fn_Edge value
  | .fn_Graph value => .fn_Graph value

def decodeResult : Algo2LeanGenerated.Result → Option «GraphLibrary».Algo2LeanGenerated.Result
  | .fn_MinHeap___init__ _ => none
  | .fn_MinHeap_swap _ => none
  | .fn_MinHeap_sift_up _ => none
  | .fn_MinHeap_sift_down _ => none
  | .fn_MinHeap_push_or_decrease _ => none
  | .fn_MinHeap_pop_min _ => none
  | .fn_MinHeap_is_empty _ => none
  | .fn_Edge___init__ value => some (.fn_Edge___init__ value)
  | .fn_Graph___init__ value => some (.fn_Graph___init__ value)
  | .fn_Graph_add_edge value => some (.fn_Graph_add_edge value)
  | .fn_dijkstra _ => none
  | .fn_MinHeap _ => none
  | .fn_Edge value => some (.fn_Edge value)
  | .fn_Graph value => some (.fn_Graph value)

def embedding : CallEmbedding «GraphLibrary».Algo2LeanGenerated.Frame «GraphLibrary».Algo2LeanGenerated.Result Algo2LeanGenerated.Frame Algo2LeanGenerated.Result where
  encodeFrame := encodeFrame
  encodeResult := encodeResult
  decodeResult := decodeResult
  invalidFrame := .invalid
  decode_encode := by intro result; cases result <;> rfl

-- Every source rule is checked against the actual corresponding application rule.
theorem simulates : embedding.Simulates «GraphLibrary».Algo2LeanGenerated.Step Algo2LeanGenerated.Step := by
  intro caller before after transition
  cases transition with
  | Edge___init___pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_Edge___init__] using!
      (Algo2LeanGenerated.Step.Edge___init___pc1 h (state_Edge___init__ s) (embedding.stack stack ++ caller))
  | Edge___init___pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge___init__] using!
      (Algo2LeanGenerated.Step.Edge___init___pc2 h (state_Edge___init__ s) (embedding.stack stack ++ caller))
  | Edge___init___pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge___init__] using!
      (Algo2LeanGenerated.Step.Edge___init___pc3 h (state_Edge___init__ s) (embedding.stack stack ++ caller) defined)
  | Edge___init___pc4 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge___init__] using!
      (Algo2LeanGenerated.Step.Edge___init___pc4 h (state_Edge___init__ s) (embedding.stack stack ++ caller) defined)
  | Edge___init___pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge___init__] using!
      (Algo2LeanGenerated.Step.Edge___init___pc5 h (state_Edge___init__ s) (embedding.stack stack ++ caller) defined)
  | Graph___init___pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc1 h (state_Graph___init__ s) (embedding.stack stack ++ caller))
  | Graph___init___pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc2 h (state_Graph___init__ s) (embedding.stack stack ++ caller))
  | Graph___init___pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc3 h (state_Graph___init__ s) (embedding.stack stack ++ caller) defined)
  | Graph___init___pc4 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc4 h (state_Graph___init__ s) (embedding.stack stack ++ caller))
  | Graph___init___pc5 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc5 h (state_Graph___init__ s) (embedding.stack stack ++ caller))
  | Graph___init___pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc6 h (state_Graph___init__ s) (embedding.stack stack ++ caller))
  | Graph___init___pc7 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc7 h (state_Graph___init__ s) (embedding.stack stack ++ caller) defined)
  | Graph___init___pc8_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc8_true h (state_Graph___init__ s) (embedding.stack stack ++ caller) condition)
  | Graph___init___pc8_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc8_false h (state_Graph___init__ s) (embedding.stack stack ++ caller) condition)
  | Graph___init___pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc9 h (state_Graph___init__ s) (embedding.stack stack ++ caller))
  | Graph___init___pc10 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph___init__] using!
      (Algo2LeanGenerated.Step.Graph___init___pc10 h (state_Graph___init__ s) (embedding.stack stack ++ caller) defined)
  | Graph_add_edge_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc1 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
  | Graph_add_edge_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc2 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
  | Graph_add_edge_pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc3 h (state_Graph_add_edge s) (embedding.stack stack ++ caller) defined)
  | Graph_add_edge_pc4 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc4 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
  | Graph_add_edge_pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc5 h (state_Graph_add_edge s) (embedding.stack stack ++ caller) defined)
  | Graph_add_edge_pc6 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.Graph_add_edge_pc6 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | Graph_add_edge_pc7 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc7 h (state_Graph_add_edge s) (embedding.stack stack ++ caller) defined)
  | Graph_add_edge_pc8 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc8 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
  | Graph_add_edge_pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc9 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
  | Graph_add_edge_pc10 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc10 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
  | Graph_add_edge_pc11 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc11 h (state_Graph_add_edge s) (embedding.stack stack ++ caller))
  | Graph_add_edge_pc12_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc12_true h (state_Graph_add_edge s) (embedding.stack stack ++ caller) condition)
  | Graph_add_edge_pc12_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc12_false h (state_Graph_add_edge s) (embedding.stack stack ++ caller) condition)
  | Graph_add_edge_pc13 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
      (Algo2LeanGenerated.Step.Graph_add_edge_pc13 h (state_Graph_add_edge s) (embedding.stack stack ++ caller) defined)
  | Edge_pc1 h s stack defined =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc1 h (state_Edge s) (embedding.stack stack ++ caller) defined)
  | Edge_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc2 h (state_Edge s) (embedding.stack stack ++ caller))
  | Edge_pc3 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.Edge_pc3 h (state_Edge s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | Edge_pc4 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc4 h (state_Edge s) (embedding.stack stack ++ caller))
  | Edge_pc5 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc5 h (state_Edge s) (embedding.stack stack ++ caller))
  | Edge_pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc6 h (state_Edge s) (embedding.stack stack ++ caller))
  | Edge_pc7 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc7 h (state_Edge s) (embedding.stack stack ++ caller))
  | Edge_pc8 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc8 h (state_Edge s) (embedding.stack stack ++ caller))
  | Edge_pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Edge] using!
      (Algo2LeanGenerated.Step.Edge_pc9 h (state_Edge s) (embedding.stack stack ++ caller))
  | Graph_pc1 h s stack defined =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_Graph] using!
      (Algo2LeanGenerated.Step.Graph_pc1 h (state_Graph s) (embedding.stack stack ++ caller) defined)
  | Graph_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph] using!
      (Algo2LeanGenerated.Step.Graph_pc2 h (state_Graph s) (embedding.stack stack ++ caller))
  | Graph_pc3 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.Graph_pc3 h (state_Graph s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | Graph_pc4 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph] using!
      (Algo2LeanGenerated.Step.Graph_pc4 h (state_Graph s) (embedding.stack stack ++ caller))
  | Graph_pc5 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph] using!
      (Algo2LeanGenerated.Step.Graph_pc5 h (state_Graph s) (embedding.stack stack ++ caller))
  | Graph_pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph] using!
      (Algo2LeanGenerated.Step.Graph_pc6 h (state_Graph s) (embedding.stack stack ++ caller))
  | Graph_pc7 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_Graph] using!
      (Algo2LeanGenerated.Step.Graph_pc7 h (state_Graph s) (embedding.stack stack ++ caller))

theorem summary_Edge___init__ {before after : Heap} {input : «GraphLibrary».Algo2LeanGenerated.Ref_Edge × Int × Int × (Option «GraphLibrary».Algo2LeanGenerated.Ref_Edge)} {output : Unit}
    (contract : «GraphLibrary».Edge.__init__.Call before input after output) :
    Edge.__init__.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_Edge___init__] using!
    embedding.summary simulates contract.2

theorem summary_Graph___init__ {before after : Heap} {input : «GraphLibrary».Algo2LeanGenerated.Ref_Graph × Int} {output : Unit}
    (contract : «GraphLibrary».Graph.__init__.Call before input after output) :
    Graph.__init__.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_Graph___init__] using!
    embedding.summary simulates contract.2

theorem summary_Graph_add_edge {before after : Heap} {input : «GraphLibrary».Algo2LeanGenerated.Ref_Graph × Int × Int × Int} {output : Bool}
    (contract : «GraphLibrary».Graph.add_edge.Call before input after output) :
    Graph.add_edge.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_Graph_add_edge] using!
    embedding.summary simulates contract.2

theorem summary_Edge {before after : Heap} {input : Int × Int × (Option «GraphLibrary».Algo2LeanGenerated.Ref_Edge)} {output : «GraphLibrary».Algo2LeanGenerated.Ref_Edge}
    (contract : «GraphLibrary».Edge.Call before input after output) :
    Edge.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_Edge] using!
    embedding.summary simulates contract.2

theorem summary_Graph {before after : Heap} {input : Int} {output : «GraphLibrary».Algo2LeanGenerated.Ref_Graph}
    (contract : «GraphLibrary».Graph.Call before input after output) :
    Graph.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_Graph] using!
    embedding.summary simulates contract.2

end «GraphIntoDijkstra»
