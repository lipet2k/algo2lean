import DijkstraFibonacciGenerated

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-! A deterministic next-configuration projection is only a certificate.
The theorem checks it against every actual compiled transition. -/

namespace DijkstraFibonacciDeterminism

open Algo2LeanCore Algo2LeanGenerated

private def next_FibonacciHeap___init__ (h : Heap) (s : State_FibonacciHeap___init__) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap___init__ (s.t1)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap___init__ 1 { s with t1 := () }) stack)
  | 3 => (.active (set_FibonacciHeap_size h (s.v0) ((0 : Int))) (Frame.fn_FibonacciHeap___init__ 2 s) stack)
  | 4 => (.active (set_FibonacciHeap_minimum h (s.v0) ((-(1 : Int)))) (Frame.fn_FibonacciHeap___init__ 3 s) stack)
  | 5 => (.active (set_FibonacciHeap_table h (s.t3) (s.t2)) (Frame.fn_FibonacciHeap___init__ 4 s) stack)
  | 6 => (.active h (Frame.fn_FibonacciHeap___init__ 5 { s with t3 := s.v0 }) stack)
  | 7 => (.active (h.allocate (fun _ => s.t4)) (Frame.fn_FibonacciHeap___init__ 6 { s with t2 := h.nextRef }) stack)
  | 8 => (.active h (Frame.fn_FibonacciHeap___init__ 7 { s with t4 := (-(1 : Int)) }) stack)
  | 9 => (.active (set_FibonacciHeap_present h (s.t6) (s.t5)) (Frame.fn_FibonacciHeap___init__ 8 s) stack)
  | 10 => (.active h (Frame.fn_FibonacciHeap___init__ 9 { s with t6 := s.v0 }) stack)
  | 11 => (.active (h.allocate (fun _ => s.t7)) (Frame.fn_FibonacciHeap___init__ 10 { s with t5 := h.nextRef }) stack)
  | 12 => (.active h (Frame.fn_FibonacciHeap___init__ 11 { s with t7 := (0 : Int) }) stack)
  | 13 => (.active (set_FibonacciHeap_marks h (s.t9) (s.t8)) (Frame.fn_FibonacciHeap___init__ 12 s) stack)
  | 14 => (.active h (Frame.fn_FibonacciHeap___init__ 13 { s with t9 := s.v0 }) stack)
  | 15 => (.active (h.allocate (fun _ => s.t10)) (Frame.fn_FibonacciHeap___init__ 14 { s with t8 := h.nextRef }) stack)
  | 16 => (.active h (Frame.fn_FibonacciHeap___init__ 15 { s with t10 := (0 : Int) }) stack)
  | 17 => (.active (set_FibonacciHeap_degrees h (s.t12) (s.t11)) (Frame.fn_FibonacciHeap___init__ 16 s) stack)
  | 18 => (.active h (Frame.fn_FibonacciHeap___init__ 17 { s with t12 := s.v0 }) stack)
  | 19 => (.active (h.allocate (fun _ => s.t13)) (Frame.fn_FibonacciHeap___init__ 18 { s with t11 := h.nextRef }) stack)
  | 20 => (.active h (Frame.fn_FibonacciHeap___init__ 19 { s with t13 := (0 : Int) }) stack)
  | 21 => (.active (set_FibonacciHeap_right h (s.t15) (s.t14)) (Frame.fn_FibonacciHeap___init__ 20 s) stack)
  | 22 => (.active h (Frame.fn_FibonacciHeap___init__ 21 { s with t15 := s.v0 }) stack)
  | 23 => (.active (h.allocate (fun _ => s.t16)) (Frame.fn_FibonacciHeap___init__ 22 { s with t14 := h.nextRef }) stack)
  | 24 => (.active h (Frame.fn_FibonacciHeap___init__ 23 { s with t16 := (0 : Int) }) stack)
  | 25 => (.active (set_FibonacciHeap_left h (s.t18) (s.t17)) (Frame.fn_FibonacciHeap___init__ 24 s) stack)
  | 26 => (.active h (Frame.fn_FibonacciHeap___init__ 25 { s with t18 := s.v0 }) stack)
  | 27 => (.active (h.allocate (fun _ => s.t19)) (Frame.fn_FibonacciHeap___init__ 26 { s with t17 := h.nextRef }) stack)
  | 28 => (.active h (Frame.fn_FibonacciHeap___init__ 27 { s with t19 := (0 : Int) }) stack)
  | 29 => (.active (set_FibonacciHeap_children h (s.t21) (s.t20)) (Frame.fn_FibonacciHeap___init__ 28 s) stack)
  | 30 => (.active h (Frame.fn_FibonacciHeap___init__ 29 { s with t21 := s.v0 }) stack)
  | 31 => (.active (h.allocate (fun _ => s.t22)) (Frame.fn_FibonacciHeap___init__ 30 { s with t20 := h.nextRef }) stack)
  | 32 => (.active h (Frame.fn_FibonacciHeap___init__ 31 { s with t22 := (-(1 : Int)) }) stack)
  | 33 => (.active (set_FibonacciHeap_parents h (s.t24) (s.t23)) (Frame.fn_FibonacciHeap___init__ 32 s) stack)
  | 34 => (.active h (Frame.fn_FibonacciHeap___init__ 33 { s with t24 := s.v0 }) stack)
  | 35 => (.active (h.allocate (fun _ => s.t25)) (Frame.fn_FibonacciHeap___init__ 34 { s with t23 := h.nextRef }) stack)
  | 36 => (.active h (Frame.fn_FibonacciHeap___init__ 35 { s with t25 := (-(1 : Int)) }) stack)
  | 37 => (.active (set_FibonacciHeap_keys h (s.t27) (s.t26)) (Frame.fn_FibonacciHeap___init__ 36 s) stack)
  | 38 => (.active h (Frame.fn_FibonacciHeap___init__ 37 { s with t27 := s.v0 }) stack)
  | 39 => (.active (h.allocate (fun _ => s.t28)) (Frame.fn_FibonacciHeap___init__ 38 { s with t26 := h.nextRef }) stack)
  | 40 => (.active h (Frame.fn_FibonacciHeap___init__ 39 { s with t28 := (0 : Int) }) stack)
  | pc => .active h (.fn_FibonacciHeap___init__ pc s) stack

private def next_FibonacciHeap_remove_from_ring (h : Heap) (s : State_FibonacciHeap_remove_from_ring) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_remove_from_ring (s.t4)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_remove_from_ring 1 { s with t4 := () }) stack)
  | 3 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1 s.v1) (Frame.fn_FibonacciHeap_remove_from_ring 2 s) stack)
  | 4 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v1 s.v1) (Frame.fn_FibonacciHeap_remove_from_ring 3 s) stack)
  | 5 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v3 s.v2) (Frame.fn_FibonacciHeap_remove_from_ring 4 s) stack)
  | 6 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v2 s.v3) (Frame.fn_FibonacciHeap_remove_from_ring 5 s) stack)
  | 7 => (.active h (Frame.fn_FibonacciHeap_remove_from_ring 6 { s with v3 := (h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1) }) stack)
  | 8 => (.active h (Frame.fn_FibonacciHeap_remove_from_ring 7 { s with v2 := (h.read ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v1) }) stack)
  | pc => .active h (.fn_FibonacciHeap_remove_from_ring pc s) stack

private def next_FibonacciHeap_add_root (h : Heap) (s : State_FibonacciHeap_add_root) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_add_root (s.t4)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_add_root 1 { s with t4 := () }) stack)
  | 3 => (.active (set_FibonacciHeap_minimum h (s.v0) (s.v1)) (Frame.fn_FibonacciHeap_add_root 2 s) stack)
  | 4 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1 s.v1) (Frame.fn_FibonacciHeap_add_root 3 s) stack)
  | 5 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v1 s.v1) (Frame.fn_FibonacciHeap_add_root 4 s) stack)
  | 6 => (.active (set_FibonacciHeap_minimum h (s.v0) (s.v1)) (Frame.fn_FibonacciHeap_add_root 2 s) stack)
  | 7 => if s.t6 then (.active h (Frame.fn_FibonacciHeap_add_root 6 s) stack) else (.active h (Frame.fn_FibonacciHeap_add_root 2 s) stack)
  | 8 => (.active h (Frame.fn_FibonacciHeap_add_root 7 { s with t6 := (decide (((h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v1) < (h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v2)))) }) stack)
  | 9 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_FibonacciHeap_add_root 8 s) stack)
  | 10 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v3 s.v1) (Frame.fn_FibonacciHeap_add_root 9 s) stack)
  | 11 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v2 s.v1) (Frame.fn_FibonacciHeap_add_root 10 s) stack)
  | 12 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1 s.v3) (Frame.fn_FibonacciHeap_add_root 11 s) stack)
  | 13 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v1 s.v2) (Frame.fn_FibonacciHeap_add_root 12 s) stack)
  | 14 => (.active h (Frame.fn_FibonacciHeap_add_root 13 { s with v3 := (h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v2) }) stack)
  | 15 => (.active h (Frame.fn_FibonacciHeap_add_root 14 { s with v2 := ((field_FibonacciHeap_minimum h (s.v0)).getD 0) }) stack)
  | 16 => if s.t5 then (.active h (Frame.fn_FibonacciHeap_add_root 5 s) stack) else (.active h (Frame.fn_FibonacciHeap_add_root 15 s) stack)
  | 17 => (.active h (Frame.fn_FibonacciHeap_add_root 16 { s with t5 := (decide ((((field_FibonacciHeap_minimum h (s.v0)).getD 0) < (0 : Int)))) }) stack)
  | 18 => (.active (h.write ((field_FibonacciHeap_marks h (s.v0)).getD 0) s.v1 (0 : Int)) (Frame.fn_FibonacciHeap_add_root 17 s) stack)
  | 19 => (.active (h.write ((field_FibonacciHeap_parents h (s.v0)).getD 0) s.v1 (-(1 : Int))) (Frame.fn_FibonacciHeap_add_root 18 s) stack)
  | pc => .active h (.fn_FibonacciHeap_add_root pc s) stack

private def next_FibonacciHeap_link (h : Heap) (s : State_FibonacciHeap_link) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_link (s.t5)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_link 1 { s with t5 := () }) stack)
  | 3 => (.active (h.tick "heap_links" 1) (Frame.fn_FibonacciHeap_link 2 s) stack)
  | 4 => (.active (h.write ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v2 ((h.read ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v2) + (1 : Int))) (Frame.fn_FibonacciHeap_link 3 s) stack)
  | 5 => (.active (h.write ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v2 s.v1) (Frame.fn_FibonacciHeap_link 4 s) stack)
  | 6 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1 s.v1) (Frame.fn_FibonacciHeap_link 5 s) stack)
  | 7 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v1 s.v1) (Frame.fn_FibonacciHeap_link 6 s) stack)
  | 8 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v3 s.v1) (Frame.fn_FibonacciHeap_link 5 s) stack)
  | 9 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v4 s.v1) (Frame.fn_FibonacciHeap_link 8 s) stack)
  | 10 => (.active (h.write ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1 s.v3) (Frame.fn_FibonacciHeap_link 9 s) stack)
  | 11 => (.active (h.write ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v1 s.v4) (Frame.fn_FibonacciHeap_link 10 s) stack)
  | 12 => (.active h (Frame.fn_FibonacciHeap_link 11 { s with v4 := (h.read ((field_FibonacciHeap_left h (s.v0)).getD 0) s.v3) }) stack)
  | 13 => if s.t6 then (.active h (Frame.fn_FibonacciHeap_link 7 s) stack) else (.active h (Frame.fn_FibonacciHeap_link 12 s) stack)
  | 14 => (.active h (Frame.fn_FibonacciHeap_link 13 { s with t6 := (decide ((s.v3 < (0 : Int)))) }) stack)
  | 15 => (.active h (Frame.fn_FibonacciHeap_link 14 { s with v3 := (h.read ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v2) }) stack)
  | 16 => (.active (h.write ((field_FibonacciHeap_marks h (s.v0)).getD 0) s.v1 (0 : Int)) (Frame.fn_FibonacciHeap_link 15 s) stack)
  | 17 => (.active (h.write ((field_FibonacciHeap_parents h (s.v0)).getD 0) s.v1 s.v2) (Frame.fn_FibonacciHeap_link 16 s) stack)
  | pc => .active h (.fn_FibonacciHeap_link pc s) stack

private def next_FibonacciHeap_consolidate (h : Heap) (s : State_FibonacciHeap_consolidate) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_consolidate (s.t7)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_consolidate 1 { s with t7 := () }) stack)
  | 3 => if s.t8 then (.active h (Frame.fn_FibonacciHeap_consolidate 14 s) stack) else (.active h (Frame.fn_FibonacciHeap_consolidate 2 s) stack)
  | 4 => (.active h (Frame.fn_FibonacciHeap_consolidate 3 { s with t8 := (decide ((s.v4 ≤ s.v2))) }) stack)
  | 5 => (.active h (Frame.fn_FibonacciHeap_consolidate 4 { s with v4 := (s.v4 + (1 : Int)) }) stack)
  | 6 => (.active h (Frame.fn_FibonacciHeap_add_root 19 ({ v0 := (s.t11), v1 := s.t12 } : State_FibonacciHeap_add_root)) ((fun value => match value with | .fn_FibonacciHeap_add_root result => (Frame.fn_FibonacciHeap_consolidate 5 { s with t10 := result }) | _ => .invalid) :: stack))
  | 7 => (.active h (Frame.fn_FibonacciHeap_consolidate 6 { s with t12 := s.v3 }) stack)
  | 8 => (.active h (Frame.fn_FibonacciHeap_consolidate 7 { s with t11 := s.t11 }) stack)
  | 9 => (.active h (Frame.fn_FibonacciHeap_consolidate 8 { s with t11 := s.v0 }) stack)
  | 10 => if s.t9 then (.active h (Frame.fn_FibonacciHeap_consolidate 9 s) stack) else (.active h (Frame.fn_FibonacciHeap_consolidate 5 s) stack)
  | 11 => (.active h (Frame.fn_FibonacciHeap_consolidate 10 { s with t9 := (decide ((s.v3 ≥ (0 : Int)))) }) stack)
  | 12 => (.active (h.write s.v1 s.v4 (-(1 : Int))) (Frame.fn_FibonacciHeap_consolidate 11 s) stack)
  | 13 => (.active h (Frame.fn_FibonacciHeap_consolidate 12 { s with v3 := (h.read s.v1 s.v4) }) stack)
  | 14 => (.active (h.tick "heap_degree_scans" 1) (Frame.fn_FibonacciHeap_consolidate 13 s) stack)
  | 15 => (.active h (Frame.fn_FibonacciHeap_consolidate 4 { s with v4 := (0 : Int) }) stack)
  | 16 => if s.t13 then (.active h (Frame.fn_FibonacciHeap_consolidate 48 s) stack) else (.active h (Frame.fn_FibonacciHeap_consolidate 15 s) stack)
  | 17 => (.active h (Frame.fn_FibonacciHeap_consolidate 16 { s with t13 := (decide ((((field_FibonacciHeap_minimum h (s.v0)).getD 0) ≥ (0 : Int)))) }) stack)
  | 18 => (.active h (Frame.fn_FibonacciHeap_consolidate 17 { s with v2 := s.v4 }) stack)
  | 19 => if s.t14 then (.active h (Frame.fn_FibonacciHeap_consolidate 18 s) stack) else (.active h (Frame.fn_FibonacciHeap_consolidate 17 s) stack)
  | 20 => (.active h (Frame.fn_FibonacciHeap_consolidate 19 { s with t14 := (decide ((s.v4 > s.v2))) }) stack)
  | 21 => (.active (h.write s.v1 s.v4 s.v3) (Frame.fn_FibonacciHeap_consolidate 20 s) stack)
  | 22 => if s.t15 then (.active h (Frame.fn_FibonacciHeap_consolidate 37 s) stack) else (.active h (Frame.fn_FibonacciHeap_consolidate 21 s) stack)
  | 23 => (.active h (Frame.fn_FibonacciHeap_consolidate 22 { s with t15 := (decide (((h.read s.v1 s.v4) ≥ (0 : Int)))) }) stack)
  | 24 => (.active h (Frame.fn_FibonacciHeap_consolidate 23 { s with v4 := (s.v4 + (1 : Int)) }) stack)
  | 25 => (.active h (Frame.fn_FibonacciHeap_link 17 ({ v0 := (s.t17), v1 := s.t18, v2 := s.t19 } : State_FibonacciHeap_link)) ((fun value => match value with | .fn_FibonacciHeap_link result => (Frame.fn_FibonacciHeap_consolidate 24 { s with t16 := result }) | _ => .invalid) :: stack))
  | 26 => (.active h (Frame.fn_FibonacciHeap_consolidate 25 { s with t19 := s.v3 }) stack)
  | 27 => (.active h (Frame.fn_FibonacciHeap_consolidate 26 { s with t18 := s.v5 }) stack)
  | 28 => (.active h (Frame.fn_FibonacciHeap_consolidate 27 { s with t17 := s.t17 }) stack)
  | 29 => (.active h (Frame.fn_FibonacciHeap_consolidate 28 { s with t17 := s.v0 }) stack)
  | 30 => (.active h (Frame.fn_FibonacciHeap_consolidate 29 { s with v5 := s.v6 }) stack)
  | 31 => (.active h (Frame.fn_FibonacciHeap_consolidate 30 { s with v3 := s.v5 }) stack)
  | 32 => (.active h (Frame.fn_FibonacciHeap_consolidate 31 { s with v6 := s.v3 }) stack)
  | 33 => if s.t20 then (.active h (Frame.fn_FibonacciHeap_consolidate 32 s) stack) else (.active h (Frame.fn_FibonacciHeap_consolidate 29 s) stack)
  | 34 => (.active h (Frame.fn_FibonacciHeap_consolidate 33 { s with t20 := (decide (((h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v5) < (h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v3)))) }) stack)
  | 35 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_FibonacciHeap_consolidate 34 s) stack)
  | 36 => (.active (h.write s.v1 s.v4 (-(1 : Int))) (Frame.fn_FibonacciHeap_consolidate 35 s) stack)
  | 37 => (.active h (Frame.fn_FibonacciHeap_consolidate 36 { s with v5 := (h.read s.v1 s.v4) }) stack)
  | 38 => (.active h (Frame.fn_FibonacciHeap_consolidate 23 { s with v4 := (h.read ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v3) }) stack)
  | 39 => (.active (h.tick "heap_root_scans" 1) (Frame.fn_FibonacciHeap_consolidate 38 s) stack)
  | 40 => (.active h (Frame.fn_FibonacciHeap_remove_from_ring 8 ({ v0 := (s.t22), v1 := s.t23 } : State_FibonacciHeap_remove_from_ring)) ((fun value => match value with | .fn_FibonacciHeap_remove_from_ring result => (Frame.fn_FibonacciHeap_consolidate 39 { s with t21 := result }) | _ => .invalid) :: stack))
  | 41 => (.active h (Frame.fn_FibonacciHeap_consolidate 40 { s with t23 := s.v3 }) stack)
  | 42 => (.active h (Frame.fn_FibonacciHeap_consolidate 41 { s with t22 := s.t22 }) stack)
  | 43 => (.active h (Frame.fn_FibonacciHeap_consolidate 42 { s with t22 := s.v0 }) stack)
  | 44 => (.active (set_FibonacciHeap_minimum h (s.v0) ((-(1 : Int)))) (Frame.fn_FibonacciHeap_consolidate 43 s) stack)
  | 45 => (.active (set_FibonacciHeap_minimum h (s.v0) ((h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v3))) (Frame.fn_FibonacciHeap_consolidate 43 s) stack)
  | 46 => if s.t24 then (.active h (Frame.fn_FibonacciHeap_consolidate 44 s) stack) else (.active h (Frame.fn_FibonacciHeap_consolidate 45 s) stack)
  | 47 => (.active h (Frame.fn_FibonacciHeap_consolidate 46 { s with t24 := (decide (((h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v3) = s.v3))) }) stack)
  | 48 => (.active h (Frame.fn_FibonacciHeap_consolidate 47 { s with v3 := ((field_FibonacciHeap_minimum h (s.v0)).getD 0) }) stack)
  | 49 => (.active h (Frame.fn_FibonacciHeap_consolidate 17 { s with v2 := (-(1 : Int)) }) stack)
  | 50 => (.active h (Frame.fn_FibonacciHeap_consolidate 49 { s with v1 := ((field_FibonacciHeap_table h (s.v0)).getD 0) }) stack)
  | pc => .active h (.fn_FibonacciHeap_consolidate pc s) stack

private def next_FibonacciHeap_cut (h : Heap) (s : State_FibonacciHeap_cut) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_cut (s.t3)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_cut 1 { s with t3 := () }) stack)
  | 3 => (.active (h.tick "heap_cuts" 1) (Frame.fn_FibonacciHeap_cut 2 s) stack)
  | 4 => (.active h (Frame.fn_FibonacciHeap_add_root 19 ({ v0 := (s.t5), v1 := s.t6 } : State_FibonacciHeap_add_root)) ((fun value => match value with | .fn_FibonacciHeap_add_root result => (Frame.fn_FibonacciHeap_cut 3 { s with t4 := result }) | _ => .invalid) :: stack))
  | 5 => (.active h (Frame.fn_FibonacciHeap_cut 4 { s with t6 := s.v1 }) stack)
  | 6 => (.active h (Frame.fn_FibonacciHeap_cut 5 { s with t5 := s.t5 }) stack)
  | 7 => (.active h (Frame.fn_FibonacciHeap_cut 6 { s with t5 := s.v0 }) stack)
  | 8 => (.active h (Frame.fn_FibonacciHeap_remove_from_ring 8 ({ v0 := (s.t8), v1 := s.t9 } : State_FibonacciHeap_remove_from_ring)) ((fun value => match value with | .fn_FibonacciHeap_remove_from_ring result => (Frame.fn_FibonacciHeap_cut 7 { s with t7 := result }) | _ => .invalid) :: stack))
  | 9 => (.active h (Frame.fn_FibonacciHeap_cut 8 { s with t9 := s.v1 }) stack)
  | 10 => (.active h (Frame.fn_FibonacciHeap_cut 9 { s with t8 := s.t8 }) stack)
  | 11 => (.active h (Frame.fn_FibonacciHeap_cut 10 { s with t8 := s.v0 }) stack)
  | 12 => (.active (h.write ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v2 ((h.read ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v2) - (1 : Int))) (Frame.fn_FibonacciHeap_cut 11 s) stack)
  | 13 => (.active (h.write ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v2 (-(1 : Int))) (Frame.fn_FibonacciHeap_cut 12 s) stack)
  | 14 => (.active (h.write ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v2 (h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1)) (Frame.fn_FibonacciHeap_cut 12 s) stack)
  | 15 => if s.t11 then (.active h (Frame.fn_FibonacciHeap_cut 13 s) stack) else (.active h (Frame.fn_FibonacciHeap_cut 14 s) stack)
  | 16 => (.active h (Frame.fn_FibonacciHeap_cut 15 { s with t11 := (decide (((h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1) = s.v1))) }) stack)
  | 17 => if s.t10 then (.active h (Frame.fn_FibonacciHeap_cut 16 s) stack) else (.active h (Frame.fn_FibonacciHeap_cut 12 s) stack)
  | 18 => (.active h (Frame.fn_FibonacciHeap_cut 17 { s with t10 := (decide (((h.read ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v2) = s.v1))) }) stack)
  | pc => .active h (.fn_FibonacciHeap_cut pc s) stack

private def next_FibonacciHeap_cascading_cut (h : Heap) (s : State_FibonacciHeap_cascading_cut) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_cascading_cut (s.t3)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 1 { s with t3 := () }) stack)
  | 3 => if s.t4 then (.active h (Frame.fn_FibonacciHeap_cascading_cut 16 s) stack) else (.active h (Frame.fn_FibonacciHeap_cascading_cut 2 s) stack)
  | 4 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 3 { s with t4 := (decide ((s.v2 ≥ (0 : Int)))) }) stack)
  | 5 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 4 { s with v2 := (h.read ((field_FibonacciHeap_parents h (s.v0)).getD 0) s.v1) }) stack)
  | 6 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 5 { s with v1 := s.v2 }) stack)
  | 7 => (.active h (Frame.fn_FibonacciHeap_cut 18 ({ v0 := (s.t6), v1 := s.t7, v2 := s.t8 } : State_FibonacciHeap_cut)) ((fun value => match value with | .fn_FibonacciHeap_cut result => (Frame.fn_FibonacciHeap_cascading_cut 6 { s with t5 := result }) | _ => .invalid) :: stack))
  | 8 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 7 { s with t8 := s.v2 }) stack)
  | 9 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 8 { s with t7 := s.v1 }) stack)
  | 10 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 9 { s with t6 := s.t6 }) stack)
  | 11 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 10 { s with t6 := s.v0 }) stack)
  | 12 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_cascading_cut (s.t10)) stack)
  | 13 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 12 { s with t10 := () }) stack)
  | 14 => (.active (h.write ((field_FibonacciHeap_marks h (s.v0)).getD 0) s.v1 (1 : Int)) (Frame.fn_FibonacciHeap_cascading_cut 13 s) stack)
  | 15 => if s.t9 then (.active h (Frame.fn_FibonacciHeap_cascading_cut 14 s) stack) else (.active h (Frame.fn_FibonacciHeap_cascading_cut 11 s) stack)
  | 16 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 15 { s with t9 := (decide (((h.read ((field_FibonacciHeap_marks h (s.v0)).getD 0) s.v1) = (0 : Int)))) }) stack)
  | 17 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 4 { s with v2 := (h.read ((field_FibonacciHeap_parents h (s.v0)).getD 0) s.v1) }) stack)
  | pc => .active h (.fn_FibonacciHeap_cascading_cut pc s) stack

private def next_FibonacciHeap_push_or_decrease (h : Heap) (s : State_FibonacciHeap_push_or_decrease) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_push_or_decrease (s.t4)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 1 { s with t4 := () }) stack)
  | 3 => (.active (set_FibonacciHeap_minimum h (s.v0) (s.v1)) (Frame.fn_FibonacciHeap_push_or_decrease 2 s) stack)
  | 4 => if s.t5 then (.active h (Frame.fn_FibonacciHeap_push_or_decrease 3 s) stack) else (.active h (Frame.fn_FibonacciHeap_push_or_decrease 2 s) stack)
  | 5 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 4 { s with t5 := (decide (((h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v1) < (h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) ((field_FibonacciHeap_minimum h (s.v0)).getD 0))))) }) stack)
  | 6 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_FibonacciHeap_push_or_decrease 5 s) stack)
  | 7 => (.active h (Frame.fn_FibonacciHeap_cascading_cut 17 ({ v0 := (s.t9), v1 := s.t10 } : State_FibonacciHeap_cascading_cut)) ((fun value => match value with | .fn_FibonacciHeap_cascading_cut result => (Frame.fn_FibonacciHeap_push_or_decrease 6 { s with t8 := result }) | _ => .invalid) :: stack))
  | 8 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 7 { s with t10 := s.v3 }) stack)
  | 9 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 8 { s with t9 := s.t9 }) stack)
  | 10 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 9 { s with t9 := s.v0 }) stack)
  | 11 => (.active h (Frame.fn_FibonacciHeap_cut 18 ({ v0 := (s.t12), v1 := s.t13, v2 := s.t14 } : State_FibonacciHeap_cut)) ((fun value => match value with | .fn_FibonacciHeap_cut result => (Frame.fn_FibonacciHeap_push_or_decrease 10 { s with t11 := result }) | _ => .invalid) :: stack))
  | 12 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 11 { s with t14 := s.v3 }) stack)
  | 13 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 12 { s with t13 := s.v1 }) stack)
  | 14 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 13 { s with t12 := s.t12 }) stack)
  | 15 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 14 { s with t12 := s.v0 }) stack)
  | 16 => if s.t7 then (.active h (Frame.fn_FibonacciHeap_push_or_decrease 15 s) stack) else (.active h (Frame.fn_FibonacciHeap_push_or_decrease 6 s) stack)
  | 17 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 16 { s with t7 := (decide ((s.v2 < (h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v3)))) }) stack)
  | 18 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_FibonacciHeap_push_or_decrease 17 s) stack)
  | 19 => if s.t6 then (.active h (Frame.fn_FibonacciHeap_push_or_decrease 18 s) stack) else (.active h (Frame.fn_FibonacciHeap_push_or_decrease 6 s) stack)
  | 20 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 19 { s with t6 := (decide ((s.v3 ≥ (0 : Int)))) }) stack)
  | 21 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 20 { s with v3 := (h.read ((field_FibonacciHeap_parents h (s.v0)).getD 0) s.v1) }) stack)
  | 22 => (.active (h.write ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v1 s.v2) (Frame.fn_FibonacciHeap_push_or_decrease 21 s) stack)
  | 23 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_push_or_decrease (s.t16)) stack)
  | 24 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 23 { s with t16 := () }) stack)
  | 25 => if s.t15 then (.active h (Frame.fn_FibonacciHeap_push_or_decrease 24 s) stack) else (.active h (Frame.fn_FibonacciHeap_push_or_decrease 22 s) stack)
  | 26 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 25 { s with t15 := (decide ((s.v2 ≥ (h.read ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v1)))) }) stack)
  | 27 => (.active (h.tick "heap_comparisons" 1) (Frame.fn_FibonacciHeap_push_or_decrease 26 s) stack)
  | 28 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_push_or_decrease (s.t18)) stack)
  | 29 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 28 { s with t18 := () }) stack)
  | 30 => (.active h (Frame.fn_FibonacciHeap_add_root 19 ({ v0 := (s.t20), v1 := s.t21 } : State_FibonacciHeap_add_root)) ((fun value => match value with | .fn_FibonacciHeap_add_root result => (Frame.fn_FibonacciHeap_push_or_decrease 29 { s with t19 := result }) | _ => .invalid) :: stack))
  | 31 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 30 { s with t21 := s.v1 }) stack)
  | 32 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 31 { s with t20 := s.t20 }) stack)
  | 33 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 32 { s with t20 := s.v0 }) stack)
  | 34 => (.active (set_FibonacciHeap_size h (s.t22) ((s.t23 + s.t24))) (Frame.fn_FibonacciHeap_push_or_decrease 33 s) stack)
  | 35 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 34 { s with t24 := (1 : Int) }) stack)
  | 36 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 35 { s with t23 := ((field_FibonacciHeap_size h (s.t22)).getD 0) }) stack)
  | 37 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 36 { s with t22 := s.v0 }) stack)
  | 38 => (.active (h.write ((field_FibonacciHeap_present h (s.v0)).getD 0) s.v1 (1 : Int)) (Frame.fn_FibonacciHeap_push_or_decrease 37 s) stack)
  | 39 => (.active (h.write ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v1 (0 : Int)) (Frame.fn_FibonacciHeap_push_or_decrease 38 s) stack)
  | 40 => (.active (h.write ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v1 (-(1 : Int))) (Frame.fn_FibonacciHeap_push_or_decrease 39 s) stack)
  | 41 => (.active (h.write ((field_FibonacciHeap_keys h (s.v0)).getD 0) s.v1 s.v2) (Frame.fn_FibonacciHeap_push_or_decrease 40 s) stack)
  | 42 => if s.t17 then (.active h (Frame.fn_FibonacciHeap_push_or_decrease 41 s) stack) else (.active h (Frame.fn_FibonacciHeap_push_or_decrease 27 s) stack)
  | 43 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 42 { s with t17 := (decide (((h.read ((field_FibonacciHeap_present h (s.v0)).getD 0) s.v1) = (0 : Int)))) }) stack)
  | 44 => (.active (h.tick "heap_operations" 1) (Frame.fn_FibonacciHeap_push_or_decrease 43 s) stack)
  | pc => .active h (.fn_FibonacciHeap_push_or_decrease pc s) stack

private def next_FibonacciHeap_pop_min (h : Heap) (s : State_FibonacciHeap_pop_min) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_pop_min (s.t4)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_pop_min 1 { s with t4 := s.v1 }) stack)
  | 3 => (.active (set_FibonacciHeap_minimum h (s.v0) ((-(1 : Int)))) (Frame.fn_FibonacciHeap_pop_min 2 s) stack)
  | 4 => (.active h (Frame.fn_FibonacciHeap_consolidate 50 ({ v0 := (s.t7) } : State_FibonacciHeap_consolidate)) ((fun value => match value with | .fn_FibonacciHeap_consolidate result => (Frame.fn_FibonacciHeap_pop_min 2 { s with t6 := result }) | _ => .invalid) :: stack))
  | 5 => (.active h (Frame.fn_FibonacciHeap_pop_min 4 { s with t7 := s.t7 }) stack)
  | 6 => (.active h (Frame.fn_FibonacciHeap_pop_min 5 { s with t7 := s.v0 }) stack)
  | 7 => (.active (set_FibonacciHeap_minimum h (s.v0) (s.v3)) (Frame.fn_FibonacciHeap_pop_min 6 s) stack)
  | 8 => if s.t5 then (.active h (Frame.fn_FibonacciHeap_pop_min 3 s) stack) else (.active h (Frame.fn_FibonacciHeap_pop_min 7 s) stack)
  | 9 => (.active h (Frame.fn_FibonacciHeap_pop_min 8 { s with t5 := (decide ((s.v3 = s.v1))) }) stack)
  | 10 => (.active (set_FibonacciHeap_size h (s.t8) ((s.t9 - s.t10))) (Frame.fn_FibonacciHeap_pop_min 9 s) stack)
  | 11 => (.active h (Frame.fn_FibonacciHeap_pop_min 10 { s with t10 := (1 : Int) }) stack)
  | 12 => (.active h (Frame.fn_FibonacciHeap_pop_min 11 { s with t9 := ((field_FibonacciHeap_size h (s.t8)).getD 0) }) stack)
  | 13 => (.active h (Frame.fn_FibonacciHeap_pop_min 12 { s with t8 := s.v0 }) stack)
  | 14 => (.active (h.write ((field_FibonacciHeap_present h (s.v0)).getD 0) s.v1 (0 : Int)) (Frame.fn_FibonacciHeap_pop_min 13 s) stack)
  | 15 => (.active h (Frame.fn_FibonacciHeap_remove_from_ring 8 ({ v0 := (s.t12), v1 := s.t13 } : State_FibonacciHeap_remove_from_ring)) ((fun value => match value with | .fn_FibonacciHeap_remove_from_ring result => (Frame.fn_FibonacciHeap_pop_min 14 { s with t11 := result }) | _ => .invalid) :: stack))
  | 16 => (.active h (Frame.fn_FibonacciHeap_pop_min 15 { s with t13 := s.v1 }) stack)
  | 17 => (.active h (Frame.fn_FibonacciHeap_pop_min 16 { s with t12 := s.t12 }) stack)
  | 18 => (.active h (Frame.fn_FibonacciHeap_pop_min 17 { s with t12 := s.v0 }) stack)
  | 19 => (.active h (Frame.fn_FibonacciHeap_pop_min 18 { s with v3 := (h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v1) }) stack)
  | 20 => if s.t14 then (.active h (Frame.fn_FibonacciHeap_pop_min 36 s) stack) else (.active h (Frame.fn_FibonacciHeap_pop_min 19 s) stack)
  | 21 => (.active h (Frame.fn_FibonacciHeap_pop_min 20 { s with t14 := (decide (((h.read ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v1) ≥ (0 : Int)))) }) stack)
  | 22 => (.active (h.tick "heap_promotions" 1) (Frame.fn_FibonacciHeap_pop_min 21 s) stack)
  | 23 => (.active h (Frame.fn_FibonacciHeap_add_root 19 ({ v0 := (s.t16), v1 := s.t17 } : State_FibonacciHeap_add_root)) ((fun value => match value with | .fn_FibonacciHeap_add_root result => (Frame.fn_FibonacciHeap_pop_min 22 { s with t15 := result }) | _ => .invalid) :: stack))
  | 24 => (.active h (Frame.fn_FibonacciHeap_pop_min 23 { s with t17 := s.v2 }) stack)
  | 25 => (.active h (Frame.fn_FibonacciHeap_pop_min 24 { s with t16 := s.t16 }) stack)
  | 26 => (.active h (Frame.fn_FibonacciHeap_pop_min 25 { s with t16 := s.v0 }) stack)
  | 27 => (.active h (Frame.fn_FibonacciHeap_remove_from_ring 8 ({ v0 := (s.t19), v1 := s.t20 } : State_FibonacciHeap_remove_from_ring)) ((fun value => match value with | .fn_FibonacciHeap_remove_from_ring result => (Frame.fn_FibonacciHeap_pop_min 26 { s with t18 := result }) | _ => .invalid) :: stack))
  | 28 => (.active h (Frame.fn_FibonacciHeap_pop_min 27 { s with t20 := s.v2 }) stack)
  | 29 => (.active h (Frame.fn_FibonacciHeap_pop_min 28 { s with t19 := s.t19 }) stack)
  | 30 => (.active h (Frame.fn_FibonacciHeap_pop_min 29 { s with t19 := s.v0 }) stack)
  | 31 => (.active (h.write ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v1 ((h.read ((field_FibonacciHeap_degrees h (s.v0)).getD 0) s.v1) - (1 : Int))) (Frame.fn_FibonacciHeap_pop_min 30 s) stack)
  | 32 => (.active (h.write ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v1 (-(1 : Int))) (Frame.fn_FibonacciHeap_pop_min 31 s) stack)
  | 33 => (.active (h.write ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v1 (h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v2)) (Frame.fn_FibonacciHeap_pop_min 31 s) stack)
  | 34 => if s.t21 then (.active h (Frame.fn_FibonacciHeap_pop_min 32 s) stack) else (.active h (Frame.fn_FibonacciHeap_pop_min 33 s) stack)
  | 35 => (.active h (Frame.fn_FibonacciHeap_pop_min 34 { s with t21 := (decide (((h.read ((field_FibonacciHeap_right h (s.v0)).getD 0) s.v2) = s.v2))) }) stack)
  | 36 => (.active h (Frame.fn_FibonacciHeap_pop_min 35 { s with v2 := (h.read ((field_FibonacciHeap_children h (s.v0)).getD 0) s.v1) }) stack)
  | 37 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_pop_min (s.t23)) stack)
  | 38 => (.active h (Frame.fn_FibonacciHeap_pop_min 37 { s with t23 := (-(1 : Int)) }) stack)
  | 39 => if s.t22 then (.active h (Frame.fn_FibonacciHeap_pop_min 38 s) stack) else (.active h (Frame.fn_FibonacciHeap_pop_min 21 s) stack)
  | 40 => (.active h (Frame.fn_FibonacciHeap_pop_min 39 { s with t22 := (decide ((s.v1 < (0 : Int)))) }) stack)
  | 41 => (.active h (Frame.fn_FibonacciHeap_pop_min 40 { s with v1 := ((field_FibonacciHeap_minimum h (s.v0)).getD 0) }) stack)
  | 42 => (.active (h.tick "heap_operations" 1) (Frame.fn_FibonacciHeap_pop_min 41 s) stack)
  | pc => .active h (.fn_FibonacciHeap_pop_min pc s) stack

private def next_FibonacciHeap_is_empty (h : Heap) (s : State_FibonacciHeap_is_empty) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap_is_empty (s.t1)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap_is_empty 1 { s with t1 := (decide ((((field_FibonacciHeap_size h (s.v0)).getD 0) ≤ (0 : Int)))) }) stack)
  | pc => .active h (.fn_FibonacciHeap_is_empty pc s) stack

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
  | 4 => (.active h (Frame.fn_dijkstra 3 { s with t10 := (decide ((((field_FibonacciHeap_size h (s.v4)).getD 0) > (0 : Int)))) }) stack)
  | 5 => if s.t11 then (.active h (Frame.fn_dijkstra 21 s) stack) else (.active h (Frame.fn_dijkstra 4 s) stack)
  | 6 => (.active h (Frame.fn_dijkstra 5 { s with t11 := (decide ((s.v6 ≠ none))) }) stack)
  | 7 => (.active h (Frame.fn_dijkstra 6 { s with v6 := ((field_Edge_next h ((s.v6).getD 0)).getD none) }) stack)
  | 8 => (.active (h.tick "improvements" 1) (Frame.fn_dijkstra 7 s) stack)
  | 9 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 44 ({ v0 := (s.t15), v1 := s.t16, v2 := s.t17 } : State_FibonacciHeap_push_or_decrease)) ((fun value => match value with | .fn_FibonacciHeap_push_or_decrease result => (Frame.fn_dijkstra 8 { s with t14 := result }) | _ => .invalid) :: stack))
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
  | 26 => (.active h (Frame.fn_FibonacciHeap_pop_min 42 ({ v0 := (s.t19) } : State_FibonacciHeap_pop_min)) ((fun value => match value with | .fn_FibonacciHeap_pop_min result => (Frame.fn_dijkstra 25 { s with t18 := result }) | _ => .invalid) :: stack))
  | 27 => (.active h (Frame.fn_dijkstra 26 { s with t19 := s.t19 }) stack)
  | 28 => (.active h (Frame.fn_dijkstra 27 { s with t19 := s.v4 }) stack)
  | 29 => (.active h (Frame.fn_FibonacciHeap_push_or_decrease 44 ({ v0 := (s.t21), v1 := s.t22, v2 := s.t23 } : State_FibonacciHeap_push_or_decrease)) ((fun value => match value with | .fn_FibonacciHeap_push_or_decrease result => (Frame.fn_dijkstra 4 { s with t20 := result }) | _ => .invalid) :: stack))
  | 30 => (.active h (Frame.fn_dijkstra 29 { s with t23 := (0 : Int) }) stack)
  | 31 => (.active h (Frame.fn_dijkstra 30 { s with t22 := s.v1 }) stack)
  | 32 => (.active h (Frame.fn_dijkstra 31 { s with t21 := s.t21 }) stack)
  | 33 => (.active h (Frame.fn_dijkstra 32 { s with t21 := s.v4 }) stack)
  | 34 => (.active (h.write s.v2 s.v1 (0 : Int)) (Frame.fn_dijkstra 33 s) stack)
  | 35 => (.active h (Frame.fn_dijkstra 34 { s with v4 := s.t24 }) stack)
  | 36 => (.active h (Frame.fn_FibonacciHeap 6 ({  } : State_FibonacciHeap)) ((fun value => match value with | .fn_FibonacciHeap result => (Frame.fn_dijkstra 35 { s with t24 := result }) | _ => .invalid) :: stack))
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

private def next_FibonacciHeap (h : Heap) (s : State_FibonacciHeap) (stack : Stack) : Nat → Configuration
  | 1 => (Algo2LeanCore.resumeConfig h (Result.fn_FibonacciHeap (s.t1)) stack)
  | 2 => (.active h (Frame.fn_FibonacciHeap 1 { s with t1 := s.v0 }) stack)
  | 3 => (.active h (Frame.fn_FibonacciHeap___init__ 40 ({ v0 := s.t3 } : State_FibonacciHeap___init__)) ((fun value => match value with | .fn_FibonacciHeap___init__ result => (Frame.fn_FibonacciHeap 2 { s with t2 := result }) | _ => .invalid) :: stack))
  | 4 => (.active h (Frame.fn_FibonacciHeap 3 { s with t3 := s.v0 }) stack)
  | 5 => (.active h (Frame.fn_FibonacciHeap 4 { s with v0 := s.t4 }) stack)
  | 6 => (.active (h.allocateObject "FibonacciHeap") (Frame.fn_FibonacciHeap 5 { s with t4 := h.nextObject }) stack)
  | pc => .active h (.fn_FibonacciHeap pc s) stack

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
    | .fn_FibonacciHeap___init__ pc s => next_FibonacciHeap___init__ h s stack pc
    | .fn_FibonacciHeap_remove_from_ring pc s => next_FibonacciHeap_remove_from_ring h s stack pc
    | .fn_FibonacciHeap_add_root pc s => next_FibonacciHeap_add_root h s stack pc
    | .fn_FibonacciHeap_link pc s => next_FibonacciHeap_link h s stack pc
    | .fn_FibonacciHeap_consolidate pc s => next_FibonacciHeap_consolidate h s stack pc
    | .fn_FibonacciHeap_cut pc s => next_FibonacciHeap_cut h s stack pc
    | .fn_FibonacciHeap_cascading_cut pc s => next_FibonacciHeap_cascading_cut h s stack pc
    | .fn_FibonacciHeap_push_or_decrease pc s => next_FibonacciHeap_push_or_decrease h s stack pc
    | .fn_FibonacciHeap_pop_min pc s => next_FibonacciHeap_pop_min h s stack pc
    | .fn_FibonacciHeap_is_empty pc s => next_FibonacciHeap_is_empty h s stack pc
    | .fn_Edge___init__ pc s => next_Edge___init__ h s stack pc
    | .fn_Graph___init__ pc s => next_Graph___init__ h s stack pc
    | .fn_Graph_add_edge pc s => next_Graph_add_edge h s stack pc
    | .fn_dijkstra pc s => next_dijkstra h s stack pc
    | .fn_FibonacciHeap pc s => next_FibonacciHeap h s stack pc
    | .fn_Edge pc s => next_Edge h s stack pc
    | .fn_Graph pc s => next_Graph h s stack pc

private theorem step_next {before after : Configuration} (transition : Step before after) :
    next before = after := by
  cases transition <;> first | rfl | simp_all [next, next_FibonacciHeap_add_root, next_FibonacciHeap_link, next_FibonacciHeap_consolidate, next_FibonacciHeap_cut, next_FibonacciHeap_cascading_cut, next_FibonacciHeap_push_or_decrease, next_FibonacciHeap_pop_min, next_Graph___init__, next_Graph_add_edge, next_dijkstra]

theorem step_deterministic : Deterministic Step := by
  intro before left right first second
  exact (step_next first).symm.trans (step_next second)

end DijkstraFibonacciDeterminism
