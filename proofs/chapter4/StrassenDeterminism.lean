import MatrixStrassenGenerated

open Algo2LeanCore Algo2LeanGenerated
namespace MatrixStrassenDeterminism

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A private successor selector used only to prove determinism. Its arbitrary
    value on stuck configurations is irrelevant: `step_selected` below checks
    every actual generated transition against it. This avoids a quadratic
    pairwise comparison of the generated instruction constructors. -/
private noncomputable def selectedNext (before : Configuration) : Configuration :=
  match before with
  | .done _ _ => before
  | .active h frame stack =>
    match frame with
    | .invalid => before
    | .fn_matrix_linear pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_linear (s.t6)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_linear 1 { s with t6 := s.v4 }) stack) else
      if pc = 3 then if s.t7 then (.active h (Frame.fn_matrix_linear 7 s) stack) else (.active h (Frame.fn_matrix_linear 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_linear 3 { s with t7 := (decide ((s.v5 < s.v2))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_linear 4 { s with v5 := (s.v5 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (h.tick "linear_cells" 1) (Frame.fn_matrix_linear 5 s) stack) else
      if pc = 7 then (.active (h.write s.v4 s.v5 ((h.read s.v0 s.v5) + (s.v3 * (h.read s.v1 s.v5)))) (Frame.fn_matrix_linear 6 s) stack) else
      if pc = 8 then (.active h (Frame.fn_matrix_linear 4 { s with v5 := (0 : Int) }) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_linear 8 { s with v4 := s.t8 }) stack) else
      if pc = 10 then (.active (h.allocate (fun _ => s.t9)) (Frame.fn_matrix_linear 9 { s with t8 := h.nextRef }) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_linear 10 { s with t9 := (0 : Int) }) stack) else
      before
    | .fn_matrix_quadrant pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_quadrant (s.t7)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_quadrant 1 { s with t7 := s.v5 }) stack) else
      if pc = 3 then if s.t8 then (.active h (Frame.fn_matrix_quadrant 7 s) stack) else (.active h (Frame.fn_matrix_quadrant 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_quadrant 3 { s with t8 := (decide ((s.v6 < (s.v2 * s.v2)))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_quadrant 4 { s with v6 := (s.v6 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (h.tick "copied_cells" 1) (Frame.fn_matrix_quadrant 5 s) stack) else
      if pc = 7 then (.active (h.write s.v5 s.v6 (h.read s.v0 ((((s.v3 + (Int.fdiv s.v6 s.v2)) * s.v1) + s.v4) + (Int.fmod s.v6 s.v2)))) (Frame.fn_matrix_quadrant 6 s) stack) else
      if pc = 8 then (.active h (Frame.fn_matrix_quadrant 4 { s with v6 := (0 : Int) }) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_quadrant 8 { s with v5 := s.t9 }) stack) else
      if pc = 10 then (.active (h.allocate (fun _ => s.t10)) (Frame.fn_matrix_quadrant 9 { s with t9 := h.nextRef }) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_quadrant 10 { s with t10 := (0 : Int) }) stack) else
      before
    | .fn_matrix_join pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_join (s.t9)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_join 1 { s with t9 := s.v5 }) stack) else
      if pc = 3 then if s.t10 then (.active h (Frame.fn_matrix_join 12 s) stack) else (.active h (Frame.fn_matrix_join 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_join 3 { s with t10 := (decide ((s.v6 < (s.v4 * s.v4)))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_join 4 { s with v6 := (s.v6 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (h.tick "copied_cells" 4) (Frame.fn_matrix_join 5 s) stack) else
      if pc = 7 then (.active (h.write s.v5 ((((s.v7 + s.v4) * ((2 : Int) * s.v4)) + s.v8) + s.v4) (h.read s.v3 s.v6)) (Frame.fn_matrix_join 6 s) stack) else
      if pc = 8 then (.active (h.write s.v5 (((s.v7 + s.v4) * ((2 : Int) * s.v4)) + s.v8) (h.read s.v2 s.v6)) (Frame.fn_matrix_join 7 s) stack) else
      if pc = 9 then (.active (h.write s.v5 (((s.v7 * ((2 : Int) * s.v4)) + s.v8) + s.v4) (h.read s.v1 s.v6)) (Frame.fn_matrix_join 8 s) stack) else
      if pc = 10 then (.active (h.write s.v5 ((s.v7 * ((2 : Int) * s.v4)) + s.v8) (h.read s.v0 s.v6)) (Frame.fn_matrix_join 9 s) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_join 10 { s with v8 := (Int.fmod s.v6 s.v4) }) stack) else
      if pc = 12 then (.active h (Frame.fn_matrix_join 11 { s with v7 := (Int.fdiv s.v6 s.v4) }) stack) else
      if pc = 13 then (.active h (Frame.fn_matrix_join 4 { s with v6 := (0 : Int) }) stack) else
      if pc = 14 then (.active h (Frame.fn_matrix_join 13 { s with v5 := s.t11 }) stack) else
      if pc = 15 then (.active (h.allocate (fun _ => s.t12)) (Frame.fn_matrix_join 14 { s with t11 := h.nextRef }) stack) else
      if pc = 16 then (.active h (Frame.fn_matrix_join 15 { s with t12 := (0 : Int) }) stack) else
      before
    | .fn_strassen pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_strassen (s.t25)) stack) else
      if pc = 2 then (.active h (Frame.fn_strassen 1 { s with t25 := s.v3 }) stack) else
      if pc = 3 then (.active (h.tick "products" 1) (Frame.fn_strassen 2 s) stack) else
      if pc = 4 then (.active (h.write s.v3 (0 : Int) ((h.read s.v0 (0 : Int)) * (h.read s.v1 (0 : Int)))) (Frame.fn_strassen 3 s) stack) else
      if pc = 5 then (.active h (Frame.fn_strassen 4 { s with v3 := s.t26 }) stack) else
      if pc = 6 then (.active (h.allocate (fun _ => s.t27)) (Frame.fn_strassen 5 { s with t26 := h.nextRef }) stack) else
      if pc = 7 then (.active h (Frame.fn_strassen 6 { s with t27 := (0 : Int) }) stack) else
      if pc = 8 then (Algo2LeanCore.resumeConfig h (Result.fn_strassen (s.t28)) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_join 16 ({ v0 := s.t29, v1 := s.t30, v2 := s.t31, v3 := s.t32, v4 := s.t33 } : State_matrix_join)) ((fun value => match value with | .fn_matrix_join result => (Frame.fn_strassen 8 { s with t28 := result }) | _ => .invalid) :: stack)) else
      if pc = 10 then (.active h (Frame.fn_strassen 9 { s with t33 := s.v4 }) stack) else
      if pc = 11 then (.active h (Frame.fn_strassen 10 { s with t32 := s.v23 }) stack) else
      if pc = 12 then (.active h (Frame.fn_strassen 11 { s with t31 := s.v22 }) stack) else
      if pc = 13 then (.active h (Frame.fn_strassen 12 { s with t30 := s.v21 }) stack) else
      if pc = 14 then (.active h (Frame.fn_strassen 13 { s with t29 := s.v20 }) stack) else
      if pc = 15 then (.active h (Frame.fn_strassen 14 { s with v23 := s.t34 }) stack) else
      if pc = 16 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t35, v1 := s.t36, v2 := s.t37, v3 := s.t38 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 15 { s with t34 := result }) | _ => .invalid) :: stack)) else
      if pc = 17 then (.active h (Frame.fn_strassen 16 { s with t38 := (-(1 : Int)) }) stack) else
      if pc = 18 then (.active h (Frame.fn_strassen 17 { s with t37 := (s.v4 * s.v4) }) stack) else
      if pc = 19 then (.active h (Frame.fn_strassen 18 { s with t36 := s.v19 }) stack) else
      if pc = 20 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t39, v1 := s.t40, v2 := s.t41, v3 := s.t42 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 19 { s with t35 := result }) | _ => .invalid) :: stack)) else
      if pc = 21 then (.active h (Frame.fn_strassen 20 { s with t42 := (-(1 : Int)) }) stack) else
      if pc = 22 then (.active h (Frame.fn_strassen 21 { s with t41 := (s.v4 * s.v4) }) stack) else
      if pc = 23 then (.active h (Frame.fn_strassen 22 { s with t40 := s.v15 }) stack) else
      if pc = 24 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t43, v1 := s.t44, v2 := s.t45, v3 := s.t46 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 23 { s with t39 := result }) | _ => .invalid) :: stack)) else
      if pc = 25 then (.active h (Frame.fn_strassen 24 { s with t46 := (1 : Int) }) stack) else
      if pc = 26 then (.active h (Frame.fn_strassen 25 { s with t45 := (s.v4 * s.v4) }) stack) else
      if pc = 27 then (.active h (Frame.fn_strassen 26 { s with t44 := s.v13 }) stack) else
      if pc = 28 then (.active h (Frame.fn_strassen 27 { s with t43 := s.v17 }) stack) else
      if pc = 29 then (.active h (Frame.fn_strassen 28 { s with v22 := s.t47 }) stack) else
      if pc = 30 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t48, v1 := s.t49, v2 := s.t50, v3 := s.t51 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 29 { s with t47 := result }) | _ => .invalid) :: stack)) else
      if pc = 31 then (.active h (Frame.fn_strassen 30 { s with t51 := (1 : Int) }) stack) else
      if pc = 32 then (.active h (Frame.fn_strassen 31 { s with t50 := (s.v4 * s.v4) }) stack) else
      if pc = 33 then (.active h (Frame.fn_strassen 32 { s with t49 := s.v16 }) stack) else
      if pc = 34 then (.active h (Frame.fn_strassen 33 { s with t48 := s.v15 }) stack) else
      if pc = 35 then (.active h (Frame.fn_strassen 34 { s with v21 := s.t52 }) stack) else
      if pc = 36 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t53, v1 := s.t54, v2 := s.t55, v3 := s.t56 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 35 { s with t52 := result }) | _ => .invalid) :: stack)) else
      if pc = 37 then (.active h (Frame.fn_strassen 36 { s with t56 := (1 : Int) }) stack) else
      if pc = 38 then (.active h (Frame.fn_strassen 37 { s with t55 := (s.v4 * s.v4) }) stack) else
      if pc = 39 then (.active h (Frame.fn_strassen 38 { s with t54 := s.v14 }) stack) else
      if pc = 40 then (.active h (Frame.fn_strassen 39 { s with t53 := s.v13 }) stack) else
      if pc = 41 then (.active h (Frame.fn_strassen 40 { s with v20 := s.t57 }) stack) else
      if pc = 42 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t58, v1 := s.t59, v2 := s.t60, v3 := s.t61 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 41 { s with t57 := result }) | _ => .invalid) :: stack)) else
      if pc = 43 then (.active h (Frame.fn_strassen 42 { s with t61 := (1 : Int) }) stack) else
      if pc = 44 then (.active h (Frame.fn_strassen 43 { s with t60 := (s.v4 * s.v4) }) stack) else
      if pc = 45 then (.active h (Frame.fn_strassen 44 { s with t59 := s.v18 }) stack) else
      if pc = 46 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t62, v1 := s.t63, v2 := s.t64, v3 := s.t65 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 45 { s with t58 := result }) | _ => .invalid) :: stack)) else
      if pc = 47 then (.active h (Frame.fn_strassen 46 { s with t65 := (-(1 : Int)) }) stack) else
      if pc = 48 then (.active h (Frame.fn_strassen 47 { s with t64 := (s.v4 * s.v4) }) stack) else
      if pc = 49 then (.active h (Frame.fn_strassen 48 { s with t63 := s.v14 }) stack) else
      if pc = 50 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t66, v1 := s.t67, v2 := s.t68, v3 := s.t69 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 49 { s with t62 := result }) | _ => .invalid) :: stack)) else
      if pc = 51 then (.active h (Frame.fn_strassen 50 { s with t69 := (1 : Int) }) stack) else
      if pc = 52 then (.active h (Frame.fn_strassen 51 { s with t68 := (s.v4 * s.v4) }) stack) else
      if pc = 53 then (.active h (Frame.fn_strassen 52 { s with t67 := s.v16 }) stack) else
      if pc = 54 then (.active h (Frame.fn_strassen 53 { s with t66 := s.v17 }) stack) else
      if pc = 55 then (.active h (Frame.fn_strassen 54 { s with v19 := s.t70 }) stack) else
      if pc = 56 then (.active h (Frame.fn_strassen 189 ({ v0 := s.t71, v1 := s.t72, v2 := s.t73 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 55 { s with t70 := result }) | _ => .invalid) :: stack)) else
      if pc = 57 then (.active h (Frame.fn_strassen 56 { s with t73 := s.v4 }) stack) else
      if pc = 58 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t74, v1 := s.t75, v2 := s.t76, v3 := s.t77 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 57 { s with t72 := result }) | _ => .invalid) :: stack)) else
      if pc = 59 then (.active h (Frame.fn_strassen 58 { s with t77 := (1 : Int) }) stack) else
      if pc = 60 then (.active h (Frame.fn_strassen 59 { s with t76 := (s.v4 * s.v4) }) stack) else
      if pc = 61 then (.active h (Frame.fn_strassen 60 { s with t75 := s.v10 }) stack) else
      if pc = 62 then (.active h (Frame.fn_strassen 61 { s with t74 := s.v9 }) stack) else
      if pc = 63 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t78, v1 := s.t79, v2 := s.t80, v3 := s.t81 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 62 { s with t71 := result }) | _ => .invalid) :: stack)) else
      if pc = 64 then (.active h (Frame.fn_strassen 63 { s with t81 := (-(1 : Int)) }) stack) else
      if pc = 65 then (.active h (Frame.fn_strassen 64 { s with t80 := (s.v4 * s.v4) }) stack) else
      if pc = 66 then (.active h (Frame.fn_strassen 65 { s with t79 := s.v7 }) stack) else
      if pc = 67 then (.active h (Frame.fn_strassen 66 { s with t78 := s.v5 }) stack) else
      if pc = 68 then (.active h (Frame.fn_strassen 67 { s with v18 := s.t82 }) stack) else
      if pc = 69 then (.active h (Frame.fn_strassen 189 ({ v0 := s.t83, v1 := s.t84, v2 := s.t85 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 68 { s with t82 := result }) | _ => .invalid) :: stack)) else
      if pc = 70 then (.active h (Frame.fn_strassen 69 { s with t85 := s.v4 }) stack) else
      if pc = 71 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t86, v1 := s.t87, v2 := s.t88, v3 := s.t89 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 70 { s with t84 := result }) | _ => .invalid) :: stack)) else
      if pc = 72 then (.active h (Frame.fn_strassen 71 { s with t89 := (1 : Int) }) stack) else
      if pc = 73 then (.active h (Frame.fn_strassen 72 { s with t88 := (s.v4 * s.v4) }) stack) else
      if pc = 74 then (.active h (Frame.fn_strassen 73 { s with t87 := s.v12 }) stack) else
      if pc = 75 then (.active h (Frame.fn_strassen 74 { s with t86 := s.v11 }) stack) else
      if pc = 76 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t90, v1 := s.t91, v2 := s.t92, v3 := s.t93 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 75 { s with t83 := result }) | _ => .invalid) :: stack)) else
      if pc = 77 then (.active h (Frame.fn_strassen 76 { s with t93 := (-(1 : Int)) }) stack) else
      if pc = 78 then (.active h (Frame.fn_strassen 77 { s with t92 := (s.v4 * s.v4) }) stack) else
      if pc = 79 then (.active h (Frame.fn_strassen 78 { s with t91 := s.v8 }) stack) else
      if pc = 80 then (.active h (Frame.fn_strassen 79 { s with t90 := s.v6 }) stack) else
      if pc = 81 then (.active h (Frame.fn_strassen 80 { s with v17 := s.t94 }) stack) else
      if pc = 82 then (.active h (Frame.fn_strassen 189 ({ v0 := s.t95, v1 := s.t96, v2 := s.t97 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 81 { s with t94 := result }) | _ => .invalid) :: stack)) else
      if pc = 83 then (.active h (Frame.fn_strassen 82 { s with t97 := s.v4 }) stack) else
      if pc = 84 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t98, v1 := s.t99, v2 := s.t100, v3 := s.t101 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 83 { s with t96 := result }) | _ => .invalid) :: stack)) else
      if pc = 85 then (.active h (Frame.fn_strassen 84 { s with t101 := (1 : Int) }) stack) else
      if pc = 86 then (.active h (Frame.fn_strassen 85 { s with t100 := (s.v4 * s.v4) }) stack) else
      if pc = 87 then (.active h (Frame.fn_strassen 86 { s with t99 := s.v12 }) stack) else
      if pc = 88 then (.active h (Frame.fn_strassen 87 { s with t98 := s.v9 }) stack) else
      if pc = 89 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t102, v1 := s.t103, v2 := s.t104, v3 := s.t105 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 88 { s with t95 := result }) | _ => .invalid) :: stack)) else
      if pc = 90 then (.active h (Frame.fn_strassen 89 { s with t105 := (1 : Int) }) stack) else
      if pc = 91 then (.active h (Frame.fn_strassen 90 { s with t104 := (s.v4 * s.v4) }) stack) else
      if pc = 92 then (.active h (Frame.fn_strassen 91 { s with t103 := s.v8 }) stack) else
      if pc = 93 then (.active h (Frame.fn_strassen 92 { s with t102 := s.v5 }) stack) else
      if pc = 94 then (.active h (Frame.fn_strassen 93 { s with v16 := s.t106 }) stack) else
      if pc = 95 then (.active h (Frame.fn_strassen 189 ({ v0 := s.t107, v1 := s.t108, v2 := s.t109 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 94 { s with t106 := result }) | _ => .invalid) :: stack)) else
      if pc = 96 then (.active h (Frame.fn_strassen 95 { s with t109 := s.v4 }) stack) else
      if pc = 97 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t110, v1 := s.t111, v2 := s.t112, v3 := s.t113 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 96 { s with t108 := result }) | _ => .invalid) :: stack)) else
      if pc = 98 then (.active h (Frame.fn_strassen 97 { s with t113 := (-(1 : Int)) }) stack) else
      if pc = 99 then (.active h (Frame.fn_strassen 98 { s with t112 := (s.v4 * s.v4) }) stack) else
      if pc = 100 then (.active h (Frame.fn_strassen 99 { s with t111 := s.v9 }) stack) else
      if pc = 101 then (.active h (Frame.fn_strassen 100 { s with t110 := s.v11 }) stack) else
      if pc = 102 then (.active h (Frame.fn_strassen 101 { s with t107 := s.v8 }) stack) else
      if pc = 103 then (.active h (Frame.fn_strassen 102 { s with v15 := s.t114 }) stack) else
      if pc = 104 then (.active h (Frame.fn_strassen 189 ({ v0 := s.t115, v1 := s.t116, v2 := s.t117 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 103 { s with t114 := result }) | _ => .invalid) :: stack)) else
      if pc = 105 then (.active h (Frame.fn_strassen 104 { s with t117 := s.v4 }) stack) else
      if pc = 106 then (.active h (Frame.fn_strassen 105 { s with t116 := s.v9 }) stack) else
      if pc = 107 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t118, v1 := s.t119, v2 := s.t120, v3 := s.t121 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 106 { s with t115 := result }) | _ => .invalid) :: stack)) else
      if pc = 108 then (.active h (Frame.fn_strassen 107 { s with t121 := (1 : Int) }) stack) else
      if pc = 109 then (.active h (Frame.fn_strassen 108 { s with t120 := (s.v4 * s.v4) }) stack) else
      if pc = 110 then (.active h (Frame.fn_strassen 109 { s with t119 := s.v8 }) stack) else
      if pc = 111 then (.active h (Frame.fn_strassen 110 { s with t118 := s.v7 }) stack) else
      if pc = 112 then (.active h (Frame.fn_strassen 111 { s with v14 := s.t122 }) stack) else
      if pc = 113 then (.active h (Frame.fn_strassen 189 ({ v0 := s.t123, v1 := s.t124, v2 := s.t125 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 112 { s with t122 := result }) | _ => .invalid) :: stack)) else
      if pc = 114 then (.active h (Frame.fn_strassen 113 { s with t125 := s.v4 }) stack) else
      if pc = 115 then (.active h (Frame.fn_strassen 114 { s with t124 := s.v12 }) stack) else
      if pc = 116 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t126, v1 := s.t127, v2 := s.t128, v3 := s.t129 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 115 { s with t123 := result }) | _ => .invalid) :: stack)) else
      if pc = 117 then (.active h (Frame.fn_strassen 116 { s with t129 := (1 : Int) }) stack) else
      if pc = 118 then (.active h (Frame.fn_strassen 117 { s with t128 := (s.v4 * s.v4) }) stack) else
      if pc = 119 then (.active h (Frame.fn_strassen 118 { s with t127 := s.v6 }) stack) else
      if pc = 120 then (.active h (Frame.fn_strassen 119 { s with t126 := s.v5 }) stack) else
      if pc = 121 then (.active h (Frame.fn_strassen 120 { s with v13 := s.t130 }) stack) else
      if pc = 122 then (.active h (Frame.fn_strassen 189 ({ v0 := s.t131, v1 := s.t132, v2 := s.t133 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 121 { s with t130 := result }) | _ => .invalid) :: stack)) else
      if pc = 123 then (.active h (Frame.fn_strassen 122 { s with t133 := s.v4 }) stack) else
      if pc = 124 then (.active h (Frame.fn_matrix_linear 11 ({ v0 := s.t134, v1 := s.t135, v2 := s.t136, v3 := s.t137 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 123 { s with t132 := result }) | _ => .invalid) :: stack)) else
      if pc = 125 then (.active h (Frame.fn_strassen 124 { s with t137 := (-(1 : Int)) }) stack) else
      if pc = 126 then (.active h (Frame.fn_strassen 125 { s with t136 := (s.v4 * s.v4) }) stack) else
      if pc = 127 then (.active h (Frame.fn_strassen 126 { s with t135 := s.v12 }) stack) else
      if pc = 128 then (.active h (Frame.fn_strassen 127 { s with t134 := s.v10 }) stack) else
      if pc = 129 then (.active h (Frame.fn_strassen 128 { s with t131 := s.v5 }) stack) else
      if pc = 130 then (.active h (Frame.fn_strassen 129 { s with v12 := s.t138 }) stack) else
      if pc = 131 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t139, v1 := s.t140, v2 := s.t141, v3 := s.t142, v4 := s.t143 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 130 { s with t138 := result }) | _ => .invalid) :: stack)) else
      if pc = 132 then (.active h (Frame.fn_strassen 131 { s with t143 := s.v4 }) stack) else
      if pc = 133 then (.active h (Frame.fn_strassen 132 { s with t142 := s.v4 }) stack) else
      if pc = 134 then (.active h (Frame.fn_strassen 133 { s with t141 := s.v4 }) stack) else
      if pc = 135 then (.active h (Frame.fn_strassen 134 { s with t140 := s.v2 }) stack) else
      if pc = 136 then (.active h (Frame.fn_strassen 135 { s with t139 := s.v1 }) stack) else
      if pc = 137 then (.active h (Frame.fn_strassen 136 { s with v11 := s.t144 }) stack) else
      if pc = 138 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t145, v1 := s.t146, v2 := s.t147, v3 := s.t148, v4 := s.t149 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 137 { s with t144 := result }) | _ => .invalid) :: stack)) else
      if pc = 139 then (.active h (Frame.fn_strassen 138 { s with t149 := (0 : Int) }) stack) else
      if pc = 140 then (.active h (Frame.fn_strassen 139 { s with t148 := s.v4 }) stack) else
      if pc = 141 then (.active h (Frame.fn_strassen 140 { s with t147 := s.v4 }) stack) else
      if pc = 142 then (.active h (Frame.fn_strassen 141 { s with t146 := s.v2 }) stack) else
      if pc = 143 then (.active h (Frame.fn_strassen 142 { s with t145 := s.v1 }) stack) else
      if pc = 144 then (.active h (Frame.fn_strassen 143 { s with v10 := s.t150 }) stack) else
      if pc = 145 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t151, v1 := s.t152, v2 := s.t153, v3 := s.t154, v4 := s.t155 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 144 { s with t150 := result }) | _ => .invalid) :: stack)) else
      if pc = 146 then (.active h (Frame.fn_strassen 145 { s with t155 := s.v4 }) stack) else
      if pc = 147 then (.active h (Frame.fn_strassen 146 { s with t154 := (0 : Int) }) stack) else
      if pc = 148 then (.active h (Frame.fn_strassen 147 { s with t153 := s.v4 }) stack) else
      if pc = 149 then (.active h (Frame.fn_strassen 148 { s with t152 := s.v2 }) stack) else
      if pc = 150 then (.active h (Frame.fn_strassen 149 { s with t151 := s.v1 }) stack) else
      if pc = 151 then (.active h (Frame.fn_strassen 150 { s with v9 := s.t156 }) stack) else
      if pc = 152 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t157, v1 := s.t158, v2 := s.t159, v3 := s.t160, v4 := s.t161 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 151 { s with t156 := result }) | _ => .invalid) :: stack)) else
      if pc = 153 then (.active h (Frame.fn_strassen 152 { s with t161 := (0 : Int) }) stack) else
      if pc = 154 then (.active h (Frame.fn_strassen 153 { s with t160 := (0 : Int) }) stack) else
      if pc = 155 then (.active h (Frame.fn_strassen 154 { s with t159 := s.v4 }) stack) else
      if pc = 156 then (.active h (Frame.fn_strassen 155 { s with t158 := s.v2 }) stack) else
      if pc = 157 then (.active h (Frame.fn_strassen 156 { s with t157 := s.v1 }) stack) else
      if pc = 158 then (.active h (Frame.fn_strassen 157 { s with v8 := s.t162 }) stack) else
      if pc = 159 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t163, v1 := s.t164, v2 := s.t165, v3 := s.t166, v4 := s.t167 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 158 { s with t162 := result }) | _ => .invalid) :: stack)) else
      if pc = 160 then (.active h (Frame.fn_strassen 159 { s with t167 := s.v4 }) stack) else
      if pc = 161 then (.active h (Frame.fn_strassen 160 { s with t166 := s.v4 }) stack) else
      if pc = 162 then (.active h (Frame.fn_strassen 161 { s with t165 := s.v4 }) stack) else
      if pc = 163 then (.active h (Frame.fn_strassen 162 { s with t164 := s.v2 }) stack) else
      if pc = 164 then (.active h (Frame.fn_strassen 163 { s with t163 := s.v0 }) stack) else
      if pc = 165 then (.active h (Frame.fn_strassen 164 { s with v7 := s.t168 }) stack) else
      if pc = 166 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t169, v1 := s.t170, v2 := s.t171, v3 := s.t172, v4 := s.t173 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 165 { s with t168 := result }) | _ => .invalid) :: stack)) else
      if pc = 167 then (.active h (Frame.fn_strassen 166 { s with t173 := (0 : Int) }) stack) else
      if pc = 168 then (.active h (Frame.fn_strassen 167 { s with t172 := s.v4 }) stack) else
      if pc = 169 then (.active h (Frame.fn_strassen 168 { s with t171 := s.v4 }) stack) else
      if pc = 170 then (.active h (Frame.fn_strassen 169 { s with t170 := s.v2 }) stack) else
      if pc = 171 then (.active h (Frame.fn_strassen 170 { s with t169 := s.v0 }) stack) else
      if pc = 172 then (.active h (Frame.fn_strassen 171 { s with v6 := s.t174 }) stack) else
      if pc = 173 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t175, v1 := s.t176, v2 := s.t177, v3 := s.t178, v4 := s.t179 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 172 { s with t174 := result }) | _ => .invalid) :: stack)) else
      if pc = 174 then (.active h (Frame.fn_strassen 173 { s with t179 := s.v4 }) stack) else
      if pc = 175 then (.active h (Frame.fn_strassen 174 { s with t178 := (0 : Int) }) stack) else
      if pc = 176 then (.active h (Frame.fn_strassen 175 { s with t177 := s.v4 }) stack) else
      if pc = 177 then (.active h (Frame.fn_strassen 176 { s with t176 := s.v2 }) stack) else
      if pc = 178 then (.active h (Frame.fn_strassen 177 { s with t175 := s.v0 }) stack) else
      if pc = 179 then (.active h (Frame.fn_strassen 178 { s with v5 := s.t180 }) stack) else
      if pc = 180 then (.active h (Frame.fn_matrix_quadrant 11 ({ v0 := s.t181, v1 := s.t182, v2 := s.t183, v3 := s.t184, v4 := s.t185 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 179 { s with t180 := result }) | _ => .invalid) :: stack)) else
      if pc = 181 then (.active h (Frame.fn_strassen 180 { s with t185 := (0 : Int) }) stack) else
      if pc = 182 then (.active h (Frame.fn_strassen 181 { s with t184 := (0 : Int) }) stack) else
      if pc = 183 then (.active h (Frame.fn_strassen 182 { s with t183 := s.v4 }) stack) else
      if pc = 184 then (.active h (Frame.fn_strassen 183 { s with t182 := s.v2 }) stack) else
      if pc = 185 then (.active h (Frame.fn_strassen 184 { s with t181 := s.v0 }) stack) else
      if pc = 186 then (.active h (Frame.fn_strassen 185 { s with v4 := (Int.fdiv s.v2 (2 : Int)) }) stack) else
      if pc = 187 then if s.t24 then (.active h (Frame.fn_strassen 7 s) stack) else (.active h (Frame.fn_strassen 186 s) stack) else
      if pc = 188 then (.active h (Frame.fn_strassen 187 { s with t24 := (decide ((s.v2 ≤ (1 : Int)))) }) stack) else
      if pc = 189 then (.active (h.tick "calls" 1) (Frame.fn_strassen 188 s) stack) else
      before

private theorem step_selected {before after : Configuration}
    (transition : Step before after) : selectedNext before = after := by
  cases transition <;> first | rfl | simp_all [selectedNext]

/-- Every generated instruction has at most one successor configuration. -/
theorem deterministicStep : Deterministic Step := by
  intro before left right first second
  exact (step_selected first).symm.trans (step_selected second)

/-- Completed runs from the same source inputs agree on the returned reference
    and the complete final heap, including all runtime counters. -/
theorem executions_unique (initial final₁ final₂ : Heap)
    (input : SeqRef × SeqRef × Int) (result₁ result₂ : SeqRef)
    (first : strassen.Run initial input final₁ result₁)
    (second : strassen.Run initial input final₂ result₂) :
    final₁ = final₂ ∧ result₁ = result₂ := by
  have same := Reaches.eq_of_terminal (step := Step) deterministicStep
    first.2 second.2
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

/-- Two completed runs at the ordinary-value interface have identical matrices
    and identical increments for every named runtime counter. -/
theorem outputs_with_cost_unique (input : Seq × Seq × Int)
    (result₁ result₂ : Seq) (costs₁ costs₂ : Clocks)
    (first : strassen.ReturnsWithCost input result₁ costs₁)
    (second : strassen.ReturnsWithCost input result₂ costs₂) :
    result₁ = result₂ ∧ costs₁ = costs₂ := by
  obtain ⟨heap₁, ref₁, execution₁, value₁, cost₁⟩ := first
  obtain ⟨heap₂, ref₂, execution₂, value₂, cost₂⟩ := second
  obtain ⟨rfl, rfl⟩ := executions_unique _ _ _ _ _ _ execution₁ execution₂
  exact ⟨value₁.symm.trans value₂, cost₁.symm.trans cost₂⟩

/-- One constructed terminating run gives a complete output-and-cost
    characterization; no other completed execution can return another result. -/
theorem output_with_cost_iff_of_run (input : Seq × Seq × Int)
    (canonical : Seq) (canonicalCosts : Clocks)
    (run : strassen.ReturnsWithCost input canonical canonicalCosts)
    (result : Seq) (charged : Clocks) :
    strassen.ReturnsWithCost input result charged ↔
      result = canonical ∧ charged = canonicalCosts := by
  constructor
  · intro completed
    exact outputs_with_cost_unique input result canonical charged canonicalCosts completed run
  · rintro ⟨rfl, rfl⟩
    exact run

/-- The same constructed run characterizes the ordinary matrix output alone. -/
theorem output_iff_of_run (input : Seq × Seq × Int)
    (canonical : Seq) (canonicalCosts : Clocks)
    (run : strassen.ReturnsWithCost input canonical canonicalCosts)
    (result : Seq) :
    strassen.Returns input result ↔ result = canonical := by
  constructor
  · intro completed
    obtain ⟨charged, withCost⟩ := completed.withCost
    exact (outputs_with_cost_unique input result canonical charged canonicalCosts withCost run).1
  · rintro rfl
    exact run.returns

end MatrixStrassenDeterminism
