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
    | .fn_matrix_linear_row pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_linear_row (s.t6)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_linear_row 1 { s with t6 := s.v4 }) stack) else
      if pc = 3 then if s.t7 then (.active h (Frame.fn_matrix_linear_row 7 s) stack) else (.active h (Frame.fn_matrix_linear_row 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_linear_row 3 { s with t7 := (decide ((s.v5 < s.v2))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_linear_row 4 { s with v5 := (s.v5 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (h.tick "linear_cells" 1) (Frame.fn_matrix_linear_row 5 s) stack) else
      if pc = 7 then (.active (h.write s.v4 s.v5 ((h.read s.v0 s.v5) + (s.v3 * (h.read s.v1 s.v5)))) (Frame.fn_matrix_linear_row 6 s) stack) else
      if pc = 8 then (.active h (Frame.fn_matrix_linear_row 4 { s with v5 := (0 : Int) }) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_linear_row 8 { s with v4 := s.t8 }) stack) else
      if pc = 10 then (.active (h.allocate (fun _ => s.t9)) (Frame.fn_matrix_linear_row 9 { s with t8 := h.nextRef }) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_linear_row 10 { s with t9 := (0 : Int) }) stack) else
      before
    | .fn_matrix_linear pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_linear (s.t6)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_linear 1 { s with t6 := s.v4 }) stack) else
      if pc = 3 then if s.t7 then (.active h (Frame.fn_matrix_linear 13 s) stack) else (.active h (Frame.fn_matrix_linear 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_linear 3 { s with t7 := (decide ((s.v5 < s.v2))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_linear 4 { s with v5 := (s.v5 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (seq_Seq_Int.set h s.t10 s.t9 s.t8) (Frame.fn_matrix_linear 5 s) stack) else
      if pc = 7 then (.active h (Frame.fn_matrix_linear 6 { s with t9 := s.v5 }) stack) else
      if pc = 8 then (.active h (Frame.fn_matrix_linear 7 { s with t10 := s.v4 }) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_linear_row 11 ({ v0 := s.t11, v1 := s.t12, v2 := s.t13, v3 := s.t14 } : State_matrix_linear_row)) ((fun value => match value with | .fn_matrix_linear_row result => (Frame.fn_matrix_linear 8 { s with t8 := result }) | _ => .invalid) :: stack)) else
      if pc = 10 then (.active h (Frame.fn_matrix_linear 9 { s with t14 := s.v3 }) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_linear 10 { s with t13 := s.v2 }) stack) else
      if pc = 12 then (.active h (Frame.fn_matrix_linear 11 { s with t12 := ((seq_Seq_Int.get h s.v1 s.v5).getD 0) }) stack) else
      if pc = 13 then (.active h (Frame.fn_matrix_linear 12 { s with t11 := ((seq_Seq_Int.get h s.v0 s.v5).getD 0) }) stack) else
      if pc = 14 then (.active h (Frame.fn_matrix_linear 4 { s with v5 := (0 : Int) }) stack) else
      if pc = 15 then (.active h (Frame.fn_matrix_linear 14 { s with v4 := s.t15 }) stack) else
      if pc = 16 then (.active (seq_Seq_Int.const h s.t16).1 (Frame.fn_matrix_linear 15 { s with t15 := h.nextCollection }) stack) else
      if pc = 17 then (.active (h.allocate (fun _ => s.t17)) (Frame.fn_matrix_linear 16 { s with t16 := h.nextRef }) stack) else
      if pc = 18 then (.active h (Frame.fn_matrix_linear 17 { s with t17 := (0 : Int) }) stack) else
      before
    | .fn_matrix_quadrant_row pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_quadrant_row (s.t5)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_quadrant_row 1 { s with t5 := s.v3 }) stack) else
      if pc = 3 then if s.t6 then (.active h (Frame.fn_matrix_quadrant_row 7 s) stack) else (.active h (Frame.fn_matrix_quadrant_row 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_quadrant_row 3 { s with t6 := (decide ((s.v4 < s.v1))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_quadrant_row 4 { s with v4 := (s.v4 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (h.tick "copied_cells" 1) (Frame.fn_matrix_quadrant_row 5 s) stack) else
      if pc = 7 then (.active (h.write s.v3 s.v4 (h.read s.v0 (s.v2 + s.v4))) (Frame.fn_matrix_quadrant_row 6 s) stack) else
      if pc = 8 then (.active h (Frame.fn_matrix_quadrant_row 4 { s with v4 := (0 : Int) }) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_quadrant_row 8 { s with v3 := s.t7 }) stack) else
      if pc = 10 then (.active (h.allocate (fun _ => s.t8)) (Frame.fn_matrix_quadrant_row 9 { s with t7 := h.nextRef }) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_quadrant_row 10 { s with t8 := (0 : Int) }) stack) else
      before
    | .fn_matrix_quadrant pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_quadrant (s.t7)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_quadrant 1 { s with t7 := s.v5 }) stack) else
      if pc = 3 then if s.t8 then (.active h (Frame.fn_matrix_quadrant 12 s) stack) else (.active h (Frame.fn_matrix_quadrant 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_quadrant 3 { s with t8 := (decide ((s.v6 < s.v2))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_quadrant 4 { s with v6 := (s.v6 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (seq_Seq_Int.set h s.t11 s.t10 s.t9) (Frame.fn_matrix_quadrant 5 s) stack) else
      if pc = 7 then (.active h (Frame.fn_matrix_quadrant 6 { s with t10 := s.v6 }) stack) else
      if pc = 8 then (.active h (Frame.fn_matrix_quadrant 7 { s with t11 := s.v5 }) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_quadrant_row 11 ({ v0 := s.t12, v1 := s.t13, v2 := s.t14 } : State_matrix_quadrant_row)) ((fun value => match value with | .fn_matrix_quadrant_row result => (Frame.fn_matrix_quadrant 8 { s with t9 := result }) | _ => .invalid) :: stack)) else
      if pc = 10 then (.active h (Frame.fn_matrix_quadrant 9 { s with t14 := s.v4 }) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_quadrant 10 { s with t13 := s.v2 }) stack) else
      if pc = 12 then (.active h (Frame.fn_matrix_quadrant 11 { s with t12 := ((seq_Seq_Int.get h s.v0 (s.v3 + s.v6)).getD 0) }) stack) else
      if pc = 13 then (.active h (Frame.fn_matrix_quadrant 4 { s with v6 := (0 : Int) }) stack) else
      if pc = 14 then (.active h (Frame.fn_matrix_quadrant 13 { s with v5 := s.t15 }) stack) else
      if pc = 15 then (.active (seq_Seq_Int.const h s.t16).1 (Frame.fn_matrix_quadrant 14 { s with t15 := h.nextCollection }) stack) else
      if pc = 16 then (.active (h.allocate (fun _ => s.t17)) (Frame.fn_matrix_quadrant 15 { s with t16 := h.nextRef }) stack) else
      if pc = 17 then (.active h (Frame.fn_matrix_quadrant 16 { s with t17 := (0 : Int) }) stack) else
      before
    | .fn_matrix_join_row pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_join_row (s.t5)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_join_row 1 { s with t5 := s.v3 }) stack) else
      if pc = 3 then if s.t6 then (.active h (Frame.fn_matrix_join_row 8 s) stack) else (.active h (Frame.fn_matrix_join_row 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_join_row 3 { s with t6 := (decide ((s.v4 < s.v2))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_join_row 4 { s with v4 := (s.v4 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (h.tick "copied_cells" 2) (Frame.fn_matrix_join_row 5 s) stack) else
      if pc = 7 then (.active (h.write s.v3 (s.v4 + s.v2) (h.read s.v1 s.v4)) (Frame.fn_matrix_join_row 6 s) stack) else
      if pc = 8 then (.active (h.write s.v3 s.v4 (h.read s.v0 s.v4)) (Frame.fn_matrix_join_row 7 s) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_join_row 4 { s with v4 := (0 : Int) }) stack) else
      if pc = 10 then (.active h (Frame.fn_matrix_join_row 9 { s with v3 := s.t7 }) stack) else
      if pc = 11 then (.active (h.allocate (fun _ => s.t8)) (Frame.fn_matrix_join_row 10 { s with t7 := h.nextRef }) stack) else
      if pc = 12 then (.active h (Frame.fn_matrix_join_row 11 { s with t8 := (0 : Int) }) stack) else
      before
    | .fn_matrix_join pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_matrix_join (s.t7)) stack) else
      if pc = 2 then (.active h (Frame.fn_matrix_join 1 { s with t7 := s.v5 }) stack) else
      if pc = 3 then if s.t8 then (.active h (Frame.fn_matrix_join 19 s) stack) else (.active h (Frame.fn_matrix_join 2 s) stack) else
      if pc = 4 then (.active h (Frame.fn_matrix_join 3 { s with t8 := (decide ((s.v6 < s.v4))) }) stack) else
      if pc = 5 then (.active h (Frame.fn_matrix_join 4 { s with v6 := (s.v6 + (1 : Int)) }) stack) else
      if pc = 6 then (.active (seq_Seq_Int.set h s.t11 s.t10 s.t9) (Frame.fn_matrix_join 5 s) stack) else
      if pc = 7 then (.active h (Frame.fn_matrix_join 6 { s with t10 := (s.v6 + s.v4) }) stack) else
      if pc = 8 then (.active h (Frame.fn_matrix_join 7 { s with t11 := s.v5 }) stack) else
      if pc = 9 then (.active h (Frame.fn_matrix_join_row 12 ({ v0 := s.t12, v1 := s.t13, v2 := s.t14 } : State_matrix_join_row)) ((fun value => match value with | .fn_matrix_join_row result => (Frame.fn_matrix_join 8 { s with t9 := result }) | _ => .invalid) :: stack)) else
      if pc = 10 then (.active h (Frame.fn_matrix_join 9 { s with t14 := s.v4 }) stack) else
      if pc = 11 then (.active h (Frame.fn_matrix_join 10 { s with t13 := ((seq_Seq_Int.get h s.v3 s.v6).getD 0) }) stack) else
      if pc = 12 then (.active h (Frame.fn_matrix_join 11 { s with t12 := ((seq_Seq_Int.get h s.v2 s.v6).getD 0) }) stack) else
      if pc = 13 then (.active (seq_Seq_Int.set h s.t17 s.t16 s.t15) (Frame.fn_matrix_join 12 s) stack) else
      if pc = 14 then (.active h (Frame.fn_matrix_join 13 { s with t16 := s.v6 }) stack) else
      if pc = 15 then (.active h (Frame.fn_matrix_join 14 { s with t17 := s.v5 }) stack) else
      if pc = 16 then (.active h (Frame.fn_matrix_join_row 12 ({ v0 := s.t18, v1 := s.t19, v2 := s.t20 } : State_matrix_join_row)) ((fun value => match value with | .fn_matrix_join_row result => (Frame.fn_matrix_join 15 { s with t15 := result }) | _ => .invalid) :: stack)) else
      if pc = 17 then (.active h (Frame.fn_matrix_join 16 { s with t20 := s.v4 }) stack) else
      if pc = 18 then (.active h (Frame.fn_matrix_join 17 { s with t19 := ((seq_Seq_Int.get h s.v1 s.v6).getD 0) }) stack) else
      if pc = 19 then (.active h (Frame.fn_matrix_join 18 { s with t18 := ((seq_Seq_Int.get h s.v0 s.v6).getD 0) }) stack) else
      if pc = 20 then (.active h (Frame.fn_matrix_join 4 { s with v6 := (0 : Int) }) stack) else
      if pc = 21 then (.active h (Frame.fn_matrix_join 20 { s with v5 := s.t21 }) stack) else
      if pc = 22 then (.active (seq_Seq_Int.const h s.t22).1 (Frame.fn_matrix_join 21 { s with t21 := h.nextCollection }) stack) else
      if pc = 23 then (.active (h.allocate (fun _ => s.t23)) (Frame.fn_matrix_join 22 { s with t22 := h.nextRef }) stack) else
      if pc = 24 then (.active h (Frame.fn_matrix_join 23 { s with t23 := (0 : Int) }) stack) else
      before
    | .fn_strassen pc s =>
      if pc = 1 then (Algo2LeanCore.resumeConfig h (Result.fn_strassen (s.t25)) stack) else
      if pc = 2 then (.active h (Frame.fn_strassen 1 { s with t25 := s.v3 }) stack) else
      if pc = 3 then (.active (h.tick "products" 1) (Frame.fn_strassen 2 s) stack) else
      if pc = 4 then (.active (h.write ((seq_Seq_Int.get h s.v3 (0 : Int)).getD 0) (0 : Int) ((h.read ((seq_Seq_Int.get h s.v0 (0 : Int)).getD 0) (0 : Int)) * (h.read ((seq_Seq_Int.get h s.v1 (0 : Int)).getD 0) (0 : Int)))) (Frame.fn_strassen 3 s) stack) else
      if pc = 5 then (.active (seq_Seq_Int.set h s.t28 s.t27 s.t26) (Frame.fn_strassen 4 s) stack) else
      if pc = 6 then (.active h (Frame.fn_strassen 5 { s with t27 := (0 : Int) }) stack) else
      if pc = 7 then (.active h (Frame.fn_strassen 6 { s with t28 := s.v3 }) stack) else
      if pc = 8 then (.active (h.allocate (fun _ => s.t29)) (Frame.fn_strassen 7 { s with t26 := h.nextRef }) stack) else
      if pc = 9 then (.active h (Frame.fn_strassen 8 { s with t29 := (0 : Int) }) stack) else
      if pc = 10 then (.active h (Frame.fn_strassen 9 { s with v3 := s.t30 }) stack) else
      if pc = 11 then (.active (seq_Seq_Int.const h s.t31).1 (Frame.fn_strassen 10 { s with t30 := h.nextCollection }) stack) else
      if pc = 12 then (.active (h.allocate (fun _ => s.t32)) (Frame.fn_strassen 11 { s with t31 := h.nextRef }) stack) else
      if pc = 13 then (.active h (Frame.fn_strassen 12 { s with t32 := (0 : Int) }) stack) else
      if pc = 14 then (Algo2LeanCore.resumeConfig h (Result.fn_strassen (s.t33)) stack) else
      if pc = 15 then (.active h (Frame.fn_matrix_join 24 ({ v0 := s.t34, v1 := s.t35, v2 := s.t36, v3 := s.t37, v4 := s.t38 } : State_matrix_join)) ((fun value => match value with | .fn_matrix_join result => (Frame.fn_strassen 14 { s with t33 := result }) | _ => .invalid) :: stack)) else
      if pc = 16 then (.active h (Frame.fn_strassen 15 { s with t38 := s.v4 }) stack) else
      if pc = 17 then (.active h (Frame.fn_strassen 16 { s with t37 := s.v23 }) stack) else
      if pc = 18 then (.active h (Frame.fn_strassen 17 { s with t36 := s.v22 }) stack) else
      if pc = 19 then (.active h (Frame.fn_strassen 18 { s with t35 := s.v21 }) stack) else
      if pc = 20 then (.active h (Frame.fn_strassen 19 { s with t34 := s.v20 }) stack) else
      if pc = 21 then (.active h (Frame.fn_strassen 20 { s with v23 := s.t39 }) stack) else
      if pc = 22 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t40, v1 := s.t41, v2 := s.t42, v3 := s.t43 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 21 { s with t39 := result }) | _ => .invalid) :: stack)) else
      if pc = 23 then (.active h (Frame.fn_strassen 22 { s with t43 := (-(1 : Int)) }) stack) else
      if pc = 24 then (.active h (Frame.fn_strassen 23 { s with t42 := s.v4 }) stack) else
      if pc = 25 then (.active h (Frame.fn_strassen 24 { s with t41 := s.v19 }) stack) else
      if pc = 26 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t44, v1 := s.t45, v2 := s.t46, v3 := s.t47 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 25 { s with t40 := result }) | _ => .invalid) :: stack)) else
      if pc = 27 then (.active h (Frame.fn_strassen 26 { s with t47 := (-(1 : Int)) }) stack) else
      if pc = 28 then (.active h (Frame.fn_strassen 27 { s with t46 := s.v4 }) stack) else
      if pc = 29 then (.active h (Frame.fn_strassen 28 { s with t45 := s.v15 }) stack) else
      if pc = 30 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t48, v1 := s.t49, v2 := s.t50, v3 := s.t51 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 29 { s with t44 := result }) | _ => .invalid) :: stack)) else
      if pc = 31 then (.active h (Frame.fn_strassen 30 { s with t51 := (1 : Int) }) stack) else
      if pc = 32 then (.active h (Frame.fn_strassen 31 { s with t50 := s.v4 }) stack) else
      if pc = 33 then (.active h (Frame.fn_strassen 32 { s with t49 := s.v13 }) stack) else
      if pc = 34 then (.active h (Frame.fn_strassen 33 { s with t48 := s.v17 }) stack) else
      if pc = 35 then (.active h (Frame.fn_strassen 34 { s with v22 := s.t52 }) stack) else
      if pc = 36 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t53, v1 := s.t54, v2 := s.t55, v3 := s.t56 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 35 { s with t52 := result }) | _ => .invalid) :: stack)) else
      if pc = 37 then (.active h (Frame.fn_strassen 36 { s with t56 := (1 : Int) }) stack) else
      if pc = 38 then (.active h (Frame.fn_strassen 37 { s with t55 := s.v4 }) stack) else
      if pc = 39 then (.active h (Frame.fn_strassen 38 { s with t54 := s.v16 }) stack) else
      if pc = 40 then (.active h (Frame.fn_strassen 39 { s with t53 := s.v15 }) stack) else
      if pc = 41 then (.active h (Frame.fn_strassen 40 { s with v21 := s.t57 }) stack) else
      if pc = 42 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t58, v1 := s.t59, v2 := s.t60, v3 := s.t61 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 41 { s with t57 := result }) | _ => .invalid) :: stack)) else
      if pc = 43 then (.active h (Frame.fn_strassen 42 { s with t61 := (1 : Int) }) stack) else
      if pc = 44 then (.active h (Frame.fn_strassen 43 { s with t60 := s.v4 }) stack) else
      if pc = 45 then (.active h (Frame.fn_strassen 44 { s with t59 := s.v14 }) stack) else
      if pc = 46 then (.active h (Frame.fn_strassen 45 { s with t58 := s.v13 }) stack) else
      if pc = 47 then (.active h (Frame.fn_strassen 46 { s with v20 := s.t62 }) stack) else
      if pc = 48 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t63, v1 := s.t64, v2 := s.t65, v3 := s.t66 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 47 { s with t62 := result }) | _ => .invalid) :: stack)) else
      if pc = 49 then (.active h (Frame.fn_strassen 48 { s with t66 := (1 : Int) }) stack) else
      if pc = 50 then (.active h (Frame.fn_strassen 49 { s with t65 := s.v4 }) stack) else
      if pc = 51 then (.active h (Frame.fn_strassen 50 { s with t64 := s.v18 }) stack) else
      if pc = 52 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t67, v1 := s.t68, v2 := s.t69, v3 := s.t70 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 51 { s with t63 := result }) | _ => .invalid) :: stack)) else
      if pc = 53 then (.active h (Frame.fn_strassen 52 { s with t70 := (-(1 : Int)) }) stack) else
      if pc = 54 then (.active h (Frame.fn_strassen 53 { s with t69 := s.v4 }) stack) else
      if pc = 55 then (.active h (Frame.fn_strassen 54 { s with t68 := s.v14 }) stack) else
      if pc = 56 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t71, v1 := s.t72, v2 := s.t73, v3 := s.t74 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 55 { s with t67 := result }) | _ => .invalid) :: stack)) else
      if pc = 57 then (.active h (Frame.fn_strassen 56 { s with t74 := (1 : Int) }) stack) else
      if pc = 58 then (.active h (Frame.fn_strassen 57 { s with t73 := s.v4 }) stack) else
      if pc = 59 then (.active h (Frame.fn_strassen 58 { s with t72 := s.v16 }) stack) else
      if pc = 60 then (.active h (Frame.fn_strassen 59 { s with t71 := s.v17 }) stack) else
      if pc = 61 then (.active h (Frame.fn_strassen 60 { s with v19 := s.t75 }) stack) else
      if pc = 62 then (.active h (Frame.fn_strassen 195 ({ v0 := s.t76, v1 := s.t77, v2 := s.t78 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 61 { s with t75 := result }) | _ => .invalid) :: stack)) else
      if pc = 63 then (.active h (Frame.fn_strassen 62 { s with t78 := s.v4 }) stack) else
      if pc = 64 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t79, v1 := s.t80, v2 := s.t81, v3 := s.t82 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 63 { s with t77 := result }) | _ => .invalid) :: stack)) else
      if pc = 65 then (.active h (Frame.fn_strassen 64 { s with t82 := (1 : Int) }) stack) else
      if pc = 66 then (.active h (Frame.fn_strassen 65 { s with t81 := s.v4 }) stack) else
      if pc = 67 then (.active h (Frame.fn_strassen 66 { s with t80 := s.v10 }) stack) else
      if pc = 68 then (.active h (Frame.fn_strassen 67 { s with t79 := s.v9 }) stack) else
      if pc = 69 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t83, v1 := s.t84, v2 := s.t85, v3 := s.t86 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 68 { s with t76 := result }) | _ => .invalid) :: stack)) else
      if pc = 70 then (.active h (Frame.fn_strassen 69 { s with t86 := (-(1 : Int)) }) stack) else
      if pc = 71 then (.active h (Frame.fn_strassen 70 { s with t85 := s.v4 }) stack) else
      if pc = 72 then (.active h (Frame.fn_strassen 71 { s with t84 := s.v7 }) stack) else
      if pc = 73 then (.active h (Frame.fn_strassen 72 { s with t83 := s.v5 }) stack) else
      if pc = 74 then (.active h (Frame.fn_strassen 73 { s with v18 := s.t87 }) stack) else
      if pc = 75 then (.active h (Frame.fn_strassen 195 ({ v0 := s.t88, v1 := s.t89, v2 := s.t90 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 74 { s with t87 := result }) | _ => .invalid) :: stack)) else
      if pc = 76 then (.active h (Frame.fn_strassen 75 { s with t90 := s.v4 }) stack) else
      if pc = 77 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t91, v1 := s.t92, v2 := s.t93, v3 := s.t94 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 76 { s with t89 := result }) | _ => .invalid) :: stack)) else
      if pc = 78 then (.active h (Frame.fn_strassen 77 { s with t94 := (1 : Int) }) stack) else
      if pc = 79 then (.active h (Frame.fn_strassen 78 { s with t93 := s.v4 }) stack) else
      if pc = 80 then (.active h (Frame.fn_strassen 79 { s with t92 := s.v12 }) stack) else
      if pc = 81 then (.active h (Frame.fn_strassen 80 { s with t91 := s.v11 }) stack) else
      if pc = 82 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t95, v1 := s.t96, v2 := s.t97, v3 := s.t98 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 81 { s with t88 := result }) | _ => .invalid) :: stack)) else
      if pc = 83 then (.active h (Frame.fn_strassen 82 { s with t98 := (-(1 : Int)) }) stack) else
      if pc = 84 then (.active h (Frame.fn_strassen 83 { s with t97 := s.v4 }) stack) else
      if pc = 85 then (.active h (Frame.fn_strassen 84 { s with t96 := s.v8 }) stack) else
      if pc = 86 then (.active h (Frame.fn_strassen 85 { s with t95 := s.v6 }) stack) else
      if pc = 87 then (.active h (Frame.fn_strassen 86 { s with v17 := s.t99 }) stack) else
      if pc = 88 then (.active h (Frame.fn_strassen 195 ({ v0 := s.t100, v1 := s.t101, v2 := s.t102 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 87 { s with t99 := result }) | _ => .invalid) :: stack)) else
      if pc = 89 then (.active h (Frame.fn_strassen 88 { s with t102 := s.v4 }) stack) else
      if pc = 90 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t103, v1 := s.t104, v2 := s.t105, v3 := s.t106 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 89 { s with t101 := result }) | _ => .invalid) :: stack)) else
      if pc = 91 then (.active h (Frame.fn_strassen 90 { s with t106 := (1 : Int) }) stack) else
      if pc = 92 then (.active h (Frame.fn_strassen 91 { s with t105 := s.v4 }) stack) else
      if pc = 93 then (.active h (Frame.fn_strassen 92 { s with t104 := s.v12 }) stack) else
      if pc = 94 then (.active h (Frame.fn_strassen 93 { s with t103 := s.v9 }) stack) else
      if pc = 95 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t107, v1 := s.t108, v2 := s.t109, v3 := s.t110 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 94 { s with t100 := result }) | _ => .invalid) :: stack)) else
      if pc = 96 then (.active h (Frame.fn_strassen 95 { s with t110 := (1 : Int) }) stack) else
      if pc = 97 then (.active h (Frame.fn_strassen 96 { s with t109 := s.v4 }) stack) else
      if pc = 98 then (.active h (Frame.fn_strassen 97 { s with t108 := s.v8 }) stack) else
      if pc = 99 then (.active h (Frame.fn_strassen 98 { s with t107 := s.v5 }) stack) else
      if pc = 100 then (.active h (Frame.fn_strassen 99 { s with v16 := s.t111 }) stack) else
      if pc = 101 then (.active h (Frame.fn_strassen 195 ({ v0 := s.t112, v1 := s.t113, v2 := s.t114 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 100 { s with t111 := result }) | _ => .invalid) :: stack)) else
      if pc = 102 then (.active h (Frame.fn_strassen 101 { s with t114 := s.v4 }) stack) else
      if pc = 103 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t115, v1 := s.t116, v2 := s.t117, v3 := s.t118 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 102 { s with t113 := result }) | _ => .invalid) :: stack)) else
      if pc = 104 then (.active h (Frame.fn_strassen 103 { s with t118 := (-(1 : Int)) }) stack) else
      if pc = 105 then (.active h (Frame.fn_strassen 104 { s with t117 := s.v4 }) stack) else
      if pc = 106 then (.active h (Frame.fn_strassen 105 { s with t116 := s.v9 }) stack) else
      if pc = 107 then (.active h (Frame.fn_strassen 106 { s with t115 := s.v11 }) stack) else
      if pc = 108 then (.active h (Frame.fn_strassen 107 { s with t112 := s.v8 }) stack) else
      if pc = 109 then (.active h (Frame.fn_strassen 108 { s with v15 := s.t119 }) stack) else
      if pc = 110 then (.active h (Frame.fn_strassen 195 ({ v0 := s.t120, v1 := s.t121, v2 := s.t122 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 109 { s with t119 := result }) | _ => .invalid) :: stack)) else
      if pc = 111 then (.active h (Frame.fn_strassen 110 { s with t122 := s.v4 }) stack) else
      if pc = 112 then (.active h (Frame.fn_strassen 111 { s with t121 := s.v9 }) stack) else
      if pc = 113 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t123, v1 := s.t124, v2 := s.t125, v3 := s.t126 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 112 { s with t120 := result }) | _ => .invalid) :: stack)) else
      if pc = 114 then (.active h (Frame.fn_strassen 113 { s with t126 := (1 : Int) }) stack) else
      if pc = 115 then (.active h (Frame.fn_strassen 114 { s with t125 := s.v4 }) stack) else
      if pc = 116 then (.active h (Frame.fn_strassen 115 { s with t124 := s.v8 }) stack) else
      if pc = 117 then (.active h (Frame.fn_strassen 116 { s with t123 := s.v7 }) stack) else
      if pc = 118 then (.active h (Frame.fn_strassen 117 { s with v14 := s.t127 }) stack) else
      if pc = 119 then (.active h (Frame.fn_strassen 195 ({ v0 := s.t128, v1 := s.t129, v2 := s.t130 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 118 { s with t127 := result }) | _ => .invalid) :: stack)) else
      if pc = 120 then (.active h (Frame.fn_strassen 119 { s with t130 := s.v4 }) stack) else
      if pc = 121 then (.active h (Frame.fn_strassen 120 { s with t129 := s.v12 }) stack) else
      if pc = 122 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t131, v1 := s.t132, v2 := s.t133, v3 := s.t134 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 121 { s with t128 := result }) | _ => .invalid) :: stack)) else
      if pc = 123 then (.active h (Frame.fn_strassen 122 { s with t134 := (1 : Int) }) stack) else
      if pc = 124 then (.active h (Frame.fn_strassen 123 { s with t133 := s.v4 }) stack) else
      if pc = 125 then (.active h (Frame.fn_strassen 124 { s with t132 := s.v6 }) stack) else
      if pc = 126 then (.active h (Frame.fn_strassen 125 { s with t131 := s.v5 }) stack) else
      if pc = 127 then (.active h (Frame.fn_strassen 126 { s with v13 := s.t135 }) stack) else
      if pc = 128 then (.active h (Frame.fn_strassen 195 ({ v0 := s.t136, v1 := s.t137, v2 := s.t138 } : State_strassen)) ((fun value => match value with | .fn_strassen result => (Frame.fn_strassen 127 { s with t135 := result }) | _ => .invalid) :: stack)) else
      if pc = 129 then (.active h (Frame.fn_strassen 128 { s with t138 := s.v4 }) stack) else
      if pc = 130 then (.active h (Frame.fn_matrix_linear 18 ({ v0 := s.t139, v1 := s.t140, v2 := s.t141, v3 := s.t142 } : State_matrix_linear)) ((fun value => match value with | .fn_matrix_linear result => (Frame.fn_strassen 129 { s with t137 := result }) | _ => .invalid) :: stack)) else
      if pc = 131 then (.active h (Frame.fn_strassen 130 { s with t142 := (-(1 : Int)) }) stack) else
      if pc = 132 then (.active h (Frame.fn_strassen 131 { s with t141 := s.v4 }) stack) else
      if pc = 133 then (.active h (Frame.fn_strassen 132 { s with t140 := s.v12 }) stack) else
      if pc = 134 then (.active h (Frame.fn_strassen 133 { s with t139 := s.v10 }) stack) else
      if pc = 135 then (.active h (Frame.fn_strassen 134 { s with t136 := s.v5 }) stack) else
      if pc = 136 then (.active h (Frame.fn_strassen 135 { s with v12 := s.t143 }) stack) else
      if pc = 137 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t144, v1 := s.t145, v2 := s.t146, v3 := s.t147, v4 := s.t148 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 136 { s with t143 := result }) | _ => .invalid) :: stack)) else
      if pc = 138 then (.active h (Frame.fn_strassen 137 { s with t148 := s.v4 }) stack) else
      if pc = 139 then (.active h (Frame.fn_strassen 138 { s with t147 := s.v4 }) stack) else
      if pc = 140 then (.active h (Frame.fn_strassen 139 { s with t146 := s.v4 }) stack) else
      if pc = 141 then (.active h (Frame.fn_strassen 140 { s with t145 := s.v2 }) stack) else
      if pc = 142 then (.active h (Frame.fn_strassen 141 { s with t144 := s.v1 }) stack) else
      if pc = 143 then (.active h (Frame.fn_strassen 142 { s with v11 := s.t149 }) stack) else
      if pc = 144 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t150, v1 := s.t151, v2 := s.t152, v3 := s.t153, v4 := s.t154 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 143 { s with t149 := result }) | _ => .invalid) :: stack)) else
      if pc = 145 then (.active h (Frame.fn_strassen 144 { s with t154 := (0 : Int) }) stack) else
      if pc = 146 then (.active h (Frame.fn_strassen 145 { s with t153 := s.v4 }) stack) else
      if pc = 147 then (.active h (Frame.fn_strassen 146 { s with t152 := s.v4 }) stack) else
      if pc = 148 then (.active h (Frame.fn_strassen 147 { s with t151 := s.v2 }) stack) else
      if pc = 149 then (.active h (Frame.fn_strassen 148 { s with t150 := s.v1 }) stack) else
      if pc = 150 then (.active h (Frame.fn_strassen 149 { s with v10 := s.t155 }) stack) else
      if pc = 151 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t156, v1 := s.t157, v2 := s.t158, v3 := s.t159, v4 := s.t160 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 150 { s with t155 := result }) | _ => .invalid) :: stack)) else
      if pc = 152 then (.active h (Frame.fn_strassen 151 { s with t160 := s.v4 }) stack) else
      if pc = 153 then (.active h (Frame.fn_strassen 152 { s with t159 := (0 : Int) }) stack) else
      if pc = 154 then (.active h (Frame.fn_strassen 153 { s with t158 := s.v4 }) stack) else
      if pc = 155 then (.active h (Frame.fn_strassen 154 { s with t157 := s.v2 }) stack) else
      if pc = 156 then (.active h (Frame.fn_strassen 155 { s with t156 := s.v1 }) stack) else
      if pc = 157 then (.active h (Frame.fn_strassen 156 { s with v9 := s.t161 }) stack) else
      if pc = 158 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t162, v1 := s.t163, v2 := s.t164, v3 := s.t165, v4 := s.t166 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 157 { s with t161 := result }) | _ => .invalid) :: stack)) else
      if pc = 159 then (.active h (Frame.fn_strassen 158 { s with t166 := (0 : Int) }) stack) else
      if pc = 160 then (.active h (Frame.fn_strassen 159 { s with t165 := (0 : Int) }) stack) else
      if pc = 161 then (.active h (Frame.fn_strassen 160 { s with t164 := s.v4 }) stack) else
      if pc = 162 then (.active h (Frame.fn_strassen 161 { s with t163 := s.v2 }) stack) else
      if pc = 163 then (.active h (Frame.fn_strassen 162 { s with t162 := s.v1 }) stack) else
      if pc = 164 then (.active h (Frame.fn_strassen 163 { s with v8 := s.t167 }) stack) else
      if pc = 165 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t168, v1 := s.t169, v2 := s.t170, v3 := s.t171, v4 := s.t172 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 164 { s with t167 := result }) | _ => .invalid) :: stack)) else
      if pc = 166 then (.active h (Frame.fn_strassen 165 { s with t172 := s.v4 }) stack) else
      if pc = 167 then (.active h (Frame.fn_strassen 166 { s with t171 := s.v4 }) stack) else
      if pc = 168 then (.active h (Frame.fn_strassen 167 { s with t170 := s.v4 }) stack) else
      if pc = 169 then (.active h (Frame.fn_strassen 168 { s with t169 := s.v2 }) stack) else
      if pc = 170 then (.active h (Frame.fn_strassen 169 { s with t168 := s.v0 }) stack) else
      if pc = 171 then (.active h (Frame.fn_strassen 170 { s with v7 := s.t173 }) stack) else
      if pc = 172 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t174, v1 := s.t175, v2 := s.t176, v3 := s.t177, v4 := s.t178 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 171 { s with t173 := result }) | _ => .invalid) :: stack)) else
      if pc = 173 then (.active h (Frame.fn_strassen 172 { s with t178 := (0 : Int) }) stack) else
      if pc = 174 then (.active h (Frame.fn_strassen 173 { s with t177 := s.v4 }) stack) else
      if pc = 175 then (.active h (Frame.fn_strassen 174 { s with t176 := s.v4 }) stack) else
      if pc = 176 then (.active h (Frame.fn_strassen 175 { s with t175 := s.v2 }) stack) else
      if pc = 177 then (.active h (Frame.fn_strassen 176 { s with t174 := s.v0 }) stack) else
      if pc = 178 then (.active h (Frame.fn_strassen 177 { s with v6 := s.t179 }) stack) else
      if pc = 179 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t180, v1 := s.t181, v2 := s.t182, v3 := s.t183, v4 := s.t184 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 178 { s with t179 := result }) | _ => .invalid) :: stack)) else
      if pc = 180 then (.active h (Frame.fn_strassen 179 { s with t184 := s.v4 }) stack) else
      if pc = 181 then (.active h (Frame.fn_strassen 180 { s with t183 := (0 : Int) }) stack) else
      if pc = 182 then (.active h (Frame.fn_strassen 181 { s with t182 := s.v4 }) stack) else
      if pc = 183 then (.active h (Frame.fn_strassen 182 { s with t181 := s.v2 }) stack) else
      if pc = 184 then (.active h (Frame.fn_strassen 183 { s with t180 := s.v0 }) stack) else
      if pc = 185 then (.active h (Frame.fn_strassen 184 { s with v5 := s.t185 }) stack) else
      if pc = 186 then (.active h (Frame.fn_matrix_quadrant 17 ({ v0 := s.t186, v1 := s.t187, v2 := s.t188, v3 := s.t189, v4 := s.t190 } : State_matrix_quadrant)) ((fun value => match value with | .fn_matrix_quadrant result => (Frame.fn_strassen 185 { s with t185 := result }) | _ => .invalid) :: stack)) else
      if pc = 187 then (.active h (Frame.fn_strassen 186 { s with t190 := (0 : Int) }) stack) else
      if pc = 188 then (.active h (Frame.fn_strassen 187 { s with t189 := (0 : Int) }) stack) else
      if pc = 189 then (.active h (Frame.fn_strassen 188 { s with t188 := s.v4 }) stack) else
      if pc = 190 then (.active h (Frame.fn_strassen 189 { s with t187 := s.v2 }) stack) else
      if pc = 191 then (.active h (Frame.fn_strassen 190 { s with t186 := s.v0 }) stack) else
      if pc = 192 then (.active h (Frame.fn_strassen 191 { s with v4 := (Int.fdiv s.v2 (2 : Int)) }) stack) else
      if pc = 193 then if s.t24 then (.active h (Frame.fn_strassen 13 s) stack) else (.active h (Frame.fn_strassen 192 s) stack) else
      if pc = 194 then (.active h (Frame.fn_strassen 193 { s with t24 := (decide ((s.v2 ≤ (1 : Int)))) }) stack) else
      if pc = 195 then (.active (h.tick "calls" 1) (Frame.fn_strassen 194 s) stack) else
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
    (input : CollectionRef × CollectionRef × Int) (result₁ result₂ : CollectionRef)
    (first : strassen.Run initial input final₁ result₁)
    (second : strassen.Run initial input final₂ result₂) :
    final₁ = final₂ ∧ result₁ = result₂ := by
  have same := Reaches.eq_of_terminal (step := Step) deterministicStep
    first.2 second.2
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

end MatrixStrassenDeterminism
