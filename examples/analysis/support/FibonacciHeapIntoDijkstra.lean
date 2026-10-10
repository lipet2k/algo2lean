import «Algo2LeanExamples».«FibonacciHeapGenerated»
import «DijkstraFibonacciGenerated»
import Algo2LeanLib.Embedding

namespace «FibonacciQueueEmbedding»

open Algo2LeanCore _root_.Algo2LeanGenerated

-- Translate only the component's control representation; the shared heap is unchanged.
def state_FibonacciHeap___init__ (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap___init__) : Algo2LeanGenerated.State_FibonacciHeap___init__ :=
  { v0 := s.v0, t1 := s.t1, t2 := s.t2, t3 := s.t3, t4 := s.t4, t5 := s.t5, t6 := s.t6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10, t11 := s.t11, t12 := s.t12, t13 := s.t13, t14 := s.t14, t15 := s.t15, t16 := s.t16, t17 := s.t17, t18 := s.t18, t19 := s.t19, t20 := s.t20, t21 := s.t21, t22 := s.t22, t23 := s.t23, t24 := s.t24, t25 := s.t25, t26 := s.t26, t27 := s.t27, t28 := s.t28 }

def state_FibonacciHeap_remove_from_ring (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_remove_from_ring) : Algo2LeanGenerated.State_FibonacciHeap_remove_from_ring :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, t4 := s.t4 }

def state_FibonacciHeap_add_root (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_add_root) : Algo2LeanGenerated.State_FibonacciHeap_add_root :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, t4 := s.t4, t5 := s.t5, t6 := s.t6 }

def state_FibonacciHeap_link (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_link) : Algo2LeanGenerated.State_FibonacciHeap_link :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, v4 := s.v4, t5 := s.t5, t6 := s.t6 }

def state_FibonacciHeap_consolidate (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_consolidate) : Algo2LeanGenerated.State_FibonacciHeap_consolidate :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, v4 := s.v4, v5 := s.v5, v6 := s.v6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10, t11 := s.t11, t12 := s.t12, t13 := s.t13, t14 := s.t14, t15 := s.t15, t16 := s.t16, t17 := s.t17, t18 := s.t18, t19 := s.t19, t20 := s.t20, t21 := s.t21, t22 := s.t22, t23 := s.t23, t24 := s.t24 }

def state_FibonacciHeap_cut (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_cut) : Algo2LeanGenerated.State_FibonacciHeap_cut :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, t3 := s.t3, t4 := s.t4, t5 := s.t5, t6 := s.t6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10, t11 := s.t11 }

def state_FibonacciHeap_cascading_cut (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_cascading_cut) : Algo2LeanGenerated.State_FibonacciHeap_cascading_cut :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, t3 := s.t3, t4 := s.t4, t5 := s.t5, t6 := s.t6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10 }

def state_FibonacciHeap_push_or_decrease (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_push_or_decrease) : Algo2LeanGenerated.State_FibonacciHeap_push_or_decrease :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, t4 := s.t4, t5 := s.t5, t6 := s.t6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10, t11 := s.t11, t12 := s.t12, t13 := s.t13, t14 := s.t14, t15 := s.t15, t16 := s.t16, t17 := s.t17, t18 := s.t18, t19 := s.t19, t20 := s.t20, t21 := s.t21, t22 := s.t22, t23 := s.t23, t24 := s.t24 }

def state_FibonacciHeap_pop_min (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_pop_min) : Algo2LeanGenerated.State_FibonacciHeap_pop_min :=
  { v0 := s.v0, v1 := s.v1, v2 := s.v2, v3 := s.v3, t4 := s.t4, t5 := s.t5, t6 := s.t6, t7 := s.t7, t8 := s.t8, t9 := s.t9, t10 := s.t10, t11 := s.t11, t12 := s.t12, t13 := s.t13, t14 := s.t14, t15 := s.t15, t16 := s.t16, t17 := s.t17, t18 := s.t18, t19 := s.t19, t20 := s.t20, t21 := s.t21, t22 := s.t22, t23 := s.t23 }

def state_FibonacciHeap_is_empty (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap_is_empty) : Algo2LeanGenerated.State_FibonacciHeap_is_empty :=
  { v0 := s.v0, t1 := s.t1 }

def state_FibonacciHeap (s : «FibonacciHeapLibrary».Algo2LeanGenerated.State_FibonacciHeap) : Algo2LeanGenerated.State_FibonacciHeap :=
  { v0 := s.v0, t1 := s.t1, t2 := s.t2, t3 := s.t3, t4 := s.t4 }

def encodeFrame : «FibonacciHeapLibrary».Algo2LeanGenerated.Frame → Algo2LeanGenerated.Frame
  | .invalid => .invalid
  | .fn_FibonacciHeap___init__ pc s => .fn_FibonacciHeap___init__ pc (state_FibonacciHeap___init__ s)
  | .fn_FibonacciHeap_remove_from_ring pc s => .fn_FibonacciHeap_remove_from_ring pc (state_FibonacciHeap_remove_from_ring s)
  | .fn_FibonacciHeap_add_root pc s => .fn_FibonacciHeap_add_root pc (state_FibonacciHeap_add_root s)
  | .fn_FibonacciHeap_link pc s => .fn_FibonacciHeap_link pc (state_FibonacciHeap_link s)
  | .fn_FibonacciHeap_consolidate pc s => .fn_FibonacciHeap_consolidate pc (state_FibonacciHeap_consolidate s)
  | .fn_FibonacciHeap_cut pc s => .fn_FibonacciHeap_cut pc (state_FibonacciHeap_cut s)
  | .fn_FibonacciHeap_cascading_cut pc s => .fn_FibonacciHeap_cascading_cut pc (state_FibonacciHeap_cascading_cut s)
  | .fn_FibonacciHeap_push_or_decrease pc s => .fn_FibonacciHeap_push_or_decrease pc (state_FibonacciHeap_push_or_decrease s)
  | .fn_FibonacciHeap_pop_min pc s => .fn_FibonacciHeap_pop_min pc (state_FibonacciHeap_pop_min s)
  | .fn_FibonacciHeap_is_empty pc s => .fn_FibonacciHeap_is_empty pc (state_FibonacciHeap_is_empty s)
  | .fn_FibonacciHeap pc s => .fn_FibonacciHeap pc (state_FibonacciHeap s)

def encodeResult : «FibonacciHeapLibrary».Algo2LeanGenerated.Result → Algo2LeanGenerated.Result
  | .fn_FibonacciHeap___init__ value => .fn_FibonacciHeap___init__ value
  | .fn_FibonacciHeap_remove_from_ring value => .fn_FibonacciHeap_remove_from_ring value
  | .fn_FibonacciHeap_add_root value => .fn_FibonacciHeap_add_root value
  | .fn_FibonacciHeap_link value => .fn_FibonacciHeap_link value
  | .fn_FibonacciHeap_consolidate value => .fn_FibonacciHeap_consolidate value
  | .fn_FibonacciHeap_cut value => .fn_FibonacciHeap_cut value
  | .fn_FibonacciHeap_cascading_cut value => .fn_FibonacciHeap_cascading_cut value
  | .fn_FibonacciHeap_push_or_decrease value => .fn_FibonacciHeap_push_or_decrease value
  | .fn_FibonacciHeap_pop_min value => .fn_FibonacciHeap_pop_min value
  | .fn_FibonacciHeap_is_empty value => .fn_FibonacciHeap_is_empty value
  | .fn_FibonacciHeap value => .fn_FibonacciHeap value

def decodeResult : Algo2LeanGenerated.Result → Option «FibonacciHeapLibrary».Algo2LeanGenerated.Result
  | .fn_FibonacciHeap___init__ value => some (.fn_FibonacciHeap___init__ value)
  | .fn_FibonacciHeap_remove_from_ring value => some (.fn_FibonacciHeap_remove_from_ring value)
  | .fn_FibonacciHeap_add_root value => some (.fn_FibonacciHeap_add_root value)
  | .fn_FibonacciHeap_link value => some (.fn_FibonacciHeap_link value)
  | .fn_FibonacciHeap_consolidate value => some (.fn_FibonacciHeap_consolidate value)
  | .fn_FibonacciHeap_cut value => some (.fn_FibonacciHeap_cut value)
  | .fn_FibonacciHeap_cascading_cut value => some (.fn_FibonacciHeap_cascading_cut value)
  | .fn_FibonacciHeap_push_or_decrease value => some (.fn_FibonacciHeap_push_or_decrease value)
  | .fn_FibonacciHeap_pop_min value => some (.fn_FibonacciHeap_pop_min value)
  | .fn_FibonacciHeap_is_empty value => some (.fn_FibonacciHeap_is_empty value)
  | .fn_Edge___init__ _ => none
  | .fn_Graph___init__ _ => none
  | .fn_Graph_add_edge _ => none
  | .fn_dijkstra _ => none
  | .fn_FibonacciHeap value => some (.fn_FibonacciHeap value)
  | .fn_Edge _ => none
  | .fn_Graph _ => none

def embedding : CallEmbedding «FibonacciHeapLibrary».Algo2LeanGenerated.Frame «FibonacciHeapLibrary».Algo2LeanGenerated.Result Algo2LeanGenerated.Frame Algo2LeanGenerated.Result where
  encodeFrame := encodeFrame
  encodeResult := encodeResult
  decodeResult := decodeResult
  invalidFrame := .invalid
  decode_encode := by intro result; cases result <;> rfl

-- Every source rule is checked against the actual corresponding application rule.
theorem simulates : embedding.Simulates «FibonacciHeapLibrary».Algo2LeanGenerated.Step Algo2LeanGenerated.Step := by
  intro caller before after transition
  cases transition with
  | FibonacciHeap___init___pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc1 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc2 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc3 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc4 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc4 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc5 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc6 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc7 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc7 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc8 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc8 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc9 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc9 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc10 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc10 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc11 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc11 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc12 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc12 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc13 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc13 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc14 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc14 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc15 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc15 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc16 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc16 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc17 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc17 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc18 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc18 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc19 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc19 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc20 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc20 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc21 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc21 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc22 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc22 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc23 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc23 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc24 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc24 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc25 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc25 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc26 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc26 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc27 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc27 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc28 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc28 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc29 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc29 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc30 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc30 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc31 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc31 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc32 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc32 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc33 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc33 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc34 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc34 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc35 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc35 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc36 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc36 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc37 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc37 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap___init___pc38 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc38 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc39 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc39 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap___init___pc40 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
      (Algo2LeanGenerated.Step.FibonacciHeap___init___pc40 h (state_FibonacciHeap___init__ s) (embedding.stack stack ++ caller))
  | FibonacciHeap_remove_from_ring_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc1 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller))
  | FibonacciHeap_remove_from_ring_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc2 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller))
  | FibonacciHeap_remove_from_ring_pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc3 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_remove_from_ring_pc4 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc4 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_remove_from_ring_pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc5 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_remove_from_ring_pc6 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc6 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_remove_from_ring_pc7 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc7 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_remove_from_ring_pc8 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
      (Algo2LeanGenerated.Step.FibonacciHeap_remove_from_ring_pc8 h (state_FibonacciHeap_remove_from_ring s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc1 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller))
  | FibonacciHeap_add_root_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc2 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller))
  | FibonacciHeap_add_root_pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc3 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc4 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc4 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc5 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc6 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc6 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc7_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc7_true h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_add_root_pc7_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc7_false h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_add_root_pc8 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc8 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc9 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller))
  | FibonacciHeap_add_root_pc10 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc10 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc11 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc11 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc12 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc12 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc13 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc13 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc14 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc14 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc15 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc15 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc16_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc16_true h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_add_root_pc16_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc16_false h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_add_root_pc17 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc17 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc18 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc18 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_add_root_pc19 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
      (Algo2LeanGenerated.Step.FibonacciHeap_add_root_pc19 h (state_FibonacciHeap_add_root s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc1 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller))
  | FibonacciHeap_link_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc2 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller))
  | FibonacciHeap_link_pc3 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc3 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller))
  | FibonacciHeap_link_pc4 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc4 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc5 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc6 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc6 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc7 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc7 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc8 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc8 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc9 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc9 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc10 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc10 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc11 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc11 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc12 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc12 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc13_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc13_true h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_link_pc13_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc13_false h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_link_pc14 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc14 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller))
  | FibonacciHeap_link_pc15 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc15 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc16 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc16 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_link_pc17 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
      (Algo2LeanGenerated.Step.FibonacciHeap_link_pc17 h (state_FibonacciHeap_link s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc1 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc2 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc3_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc3_true h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc3_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc3_false h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc4 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc4 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc5 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc5 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc6 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc6 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_consolidate_pc7 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc7 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc8 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc8 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc9 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc10_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc10_true h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc10_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc10_false h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc11 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc11 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc12 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc12 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc13 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc13 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc14 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc14 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc15 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc15 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc16_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc16_true h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc16_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc16_false h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc17 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc17 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc18 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc18 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc19_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc19_true h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc19_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc19_false h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc20 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc20 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc21 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc21 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc22_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc22_true h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc22_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc22_false h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc23 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc23 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc24 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc24 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc25 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc25 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_consolidate_pc26 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc26 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc27 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc27 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc28 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc28 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc29 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc29 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc30 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc30 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc31 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc31 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc32 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc32 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc33_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc33_true h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc33_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc33_false h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc34 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc34 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc35 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc35 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc36 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc36 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc37 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc37 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc38 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc38 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc39 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc39 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc40 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc40 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_consolidate_pc41 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc41 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc42 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc42 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc43 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc43 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc44 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc44 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc45 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc45 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc46_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc46_true h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc46_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc46_false h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_consolidate_pc47 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc47 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc48 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc48 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_consolidate_pc49 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc49 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller))
  | FibonacciHeap_consolidate_pc50 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
      (Algo2LeanGenerated.Step.FibonacciHeap_consolidate_pc50 h (state_FibonacciHeap_consolidate s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cut_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc1 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cut_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc2 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cut_pc3 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc3 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cut_pc4 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc4 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_cut_pc5 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc5 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cut_pc6 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc6 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cut_pc7 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc7 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cut_pc8 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc8 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_cut_pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc9 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cut_pc10 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc10 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cut_pc11 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc11 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cut_pc12 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc12 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cut_pc13 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc13 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cut_pc14 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc14 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cut_pc15_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc15_true h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cut_pc15_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc15_false h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cut_pc16 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc16 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cut_pc17_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc17_true h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cut_pc17_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc17_false h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cut_pc18 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cut_pc18 h (state_FibonacciHeap_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cascading_cut_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc1 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc2 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc3_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc3_true h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cascading_cut_pc3_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc3_false h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cascading_cut_pc4 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc4 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc5 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cascading_cut_pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc6 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc7 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc7 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_cascading_cut_pc8 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc8 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc9 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc10 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc10 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cascading_cut_pc11 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc11 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc12 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc12 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc13 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc13 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller))
  | FibonacciHeap_cascading_cut_pc14 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc14 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cascading_cut_pc15_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc15_true h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cascading_cut_pc15_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc15_false h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_cascading_cut_pc16 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc16 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_cascading_cut_pc17 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
      (Algo2LeanGenerated.Step.FibonacciHeap_cascading_cut_pc17 h (state_FibonacciHeap_cascading_cut s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc1 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc2 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc3 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc4_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc4_true h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc4_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc4_false h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc5 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc6 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc7 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc7 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_push_or_decrease_pc8 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc8 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc9 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc9 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc10 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc10 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc11 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc11 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_push_or_decrease_pc12 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc12 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc13 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc13 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc14 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc14 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc15 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc15 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc16_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc16_true h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc16_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc16_false h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc17 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc17 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc18 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc18 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc19_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc19_true h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc19_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc19_false h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc20 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc20 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc21 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc21 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc22 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc22 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc23 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc23 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc24 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc24 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc25_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc25_true h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc25_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc25_false h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc26 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc26 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc27 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc27 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc28 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc28 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc29 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc29 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc30 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc30 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_push_or_decrease_pc31 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc31 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc32 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc32 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc33 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc33 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc34 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc34 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc35 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc35 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc36 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc36 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc37 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc37 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_push_or_decrease_pc38 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc38 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc39 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc39 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc40 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc40 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc41 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc41 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc42_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc42_true h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc42_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc42_false h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_push_or_decrease_pc43 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc43 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_push_or_decrease_pc44 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
      (Algo2LeanGenerated.Step.FibonacciHeap_push_or_decrease_pc44 h (state_FibonacciHeap_push_or_decrease s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc1 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc2 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc3 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc3 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc4 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc4 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_pop_min_pc5 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc5 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc6 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc7 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc7 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc8_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc8_true h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc8_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc8_false h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc9 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc9 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc10 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc10 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc11 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc11 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc12 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc12 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc13 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc13 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc14 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc14 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc15 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc15 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_pop_min_pc16 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc16 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc17 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc17 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc18 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc18 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc19 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc19 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc20_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc20_true h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc20_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc20_false h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc21 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc21 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc22 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc22 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc23 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc23 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_pop_min_pc24 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc24 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc25 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc25 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc26 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc26 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc27 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc27 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_pop_min_pc28 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc28 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc29 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc29 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc30 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc30 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc31 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc31 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc32 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc32 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc33 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc33 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc34_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc34_true h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc34_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc34_false h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc35 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc35 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc36 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc36 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc37 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc37 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc38 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc38 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc39_true h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc39_true h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc39_false h s stack condition =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc39_false h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) condition)
  | FibonacciHeap_pop_min_pc40 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc40 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pop_min_pc41 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc41 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pop_min_pc42 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pop_min_pc42 h (state_FibonacciHeap_pop_min s) (embedding.stack stack ++ caller))
  | FibonacciHeap_is_empty_pc1 h s stack =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap_is_empty] using
      (Algo2LeanGenerated.Step.FibonacciHeap_is_empty_pc1 h (state_FibonacciHeap_is_empty s) (embedding.stack stack ++ caller))
  | FibonacciHeap_is_empty_pc2 h s stack defined =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap_is_empty] using
      (Algo2LeanGenerated.Step.FibonacciHeap_is_empty_pc2 h (state_FibonacciHeap_is_empty s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pc1 h s stack defined =>
    simpa only [CallEmbedding.config_active, CallEmbedding.resume, embedding, encodeFrame, encodeResult, state_FibonacciHeap] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pc1 h (state_FibonacciHeap s) (embedding.stack stack ++ caller) defined)
  | FibonacciHeap_pc2 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pc2 h (state_FibonacciHeap s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pc3 h s stack =>
    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]
    apply Eq.mp ?_ (Algo2LeanGenerated.Step.FibonacciHeap_pc3 h (state_FibonacciHeap s) (embedding.stack stack ++ caller))
    congr 4
    all_goals (funext value; cases value <;> rfl)
  | FibonacciHeap_pc4 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pc4 h (state_FibonacciHeap s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pc5 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pc5 h (state_FibonacciHeap s) (embedding.stack stack ++ caller))
  | FibonacciHeap_pc6 h s stack =>
    simpa only [CallEmbedding.config_active, embedding, encodeFrame, encodeResult, state_FibonacciHeap] using
      (Algo2LeanGenerated.Step.FibonacciHeap_pc6 h (state_FibonacciHeap s) (embedding.stack stack ++ caller))

theorem summary_FibonacciHeap___init__ {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.__init__.Call before input after output) :
    FibonacciHeap.__init__.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap___init__] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_remove_from_ring {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap × Int} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.remove_from_ring.Call before input after output) :
    FibonacciHeap.remove_from_ring.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_remove_from_ring] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_add_root {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap × Int} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.add_root.Call before input after output) :
    FibonacciHeap.add_root.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_add_root] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_link {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap × Int × Int} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.link.Call before input after output) :
    FibonacciHeap.link.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_link] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_consolidate {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.consolidate.Call before input after output) :
    FibonacciHeap.consolidate.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_consolidate] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_cut {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap × Int × Int} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.cut.Call before input after output) :
    FibonacciHeap.cut.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_cut] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_cascading_cut {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap × Int} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.cascading_cut.Call before input after output) :
    FibonacciHeap.cascading_cut.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_cascading_cut] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_push_or_decrease {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap × Int × Int} {output : Unit}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.push_or_decrease.Call before input after output) :
    FibonacciHeap.push_or_decrease.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_push_or_decrease] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_pop_min {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap} {output : Int}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.pop_min.Call before input after output) :
    FibonacciHeap.pop_min.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_pop_min] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap_is_empty {before after : Heap} {input : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap} {output : Bool}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.is_empty.Call before input after output) :
    FibonacciHeap.is_empty.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap_is_empty] using
    embedding.summary simulates contract.2

theorem summary_FibonacciHeap {before after : Heap} {input : Unit} {output : «FibonacciHeapLibrary».Algo2LeanGenerated.Ref_FibonacciHeap}
    (contract : «FibonacciHeapLibrary».FibonacciHeap.Call before input after output) :
    FibonacciHeap.Call before input after output := by
  refine ⟨contract.1, ?_⟩
  simpa only [embedding, encodeFrame, encodeResult, state_FibonacciHeap] using
    embedding.summary simulates contract.2

end «FibonacciQueueEmbedding»
