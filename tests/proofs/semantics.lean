-- Appended to generated Lean by tests/test_lean.py.
-- The helper tactic searches only the generated inductive constructors.
-- The expected results are specified independently of the generated transitions.

example : choose.Returns (2, 7) 7 := by
  unfold choose.Returns
  algo_steps

example : choose.Returns (0, 7) (-7) := by
  unfold choose.Returns
  algo_steps

example : zero.Returns () 17 := by
  unfold zero.Returns
  algo_steps

example : three.Returns (2, 3, 4) 9 := by
  unfold three.Returns
  algo_steps

example : fact.Returns 5 120 := by
  unfold fact.Returns
  algo_steps

example : sum_to.Returns 5 15 := by
  unfold sum_to.Returns
  algo_steps

example : sum_to.Returns (-3) 0 := by
  unfold sum_to.Returns
  algo_steps

example : odd.Returns 5 true := by
  unfold odd.Returns
  algo_steps

example : even.Returns 6 true := by
  unfold even.Returns
  algo_steps

example : even.Returns 3 false := by
  unfold even.Returns
  algo_steps

example : read_negative.Returns (fun i => i * 2) (-24) := by
  unfold read_negative.Returns
  algo_steps

example : distant.Returns 137 137 := by
  unfold distant.Returns
  algo_steps

example : aliasing.Returns (fun _ => 8) 99 := by
  unfold aliasing.Returns
  algo_steps

example : untouched.Returns (fun i => i * 2) 10 := by
  unfold untouched.Returns
  algo_steps

example : replacement.Returns ((fun _ => 0), -17, 61) 61 := by
  unfold replacement.Returns
  algo_steps

example : «constant».Returns 83 (fun _ => 83) := by
  unfold «constant».Returns
  algo_steps

example : huge.Returns () 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  unfold huge.Returns
  algo_steps

example : floor_div.Returns (7, 3) 2 := by
  unfold floor_div.Returns
  algo_steps

example : floor_div.Returns (-7, 3) (-3) := by
  unfold floor_div.Returns
  algo_steps

example : floor_div.Returns (7, -3) (-3) := by
  unfold floor_div.Returns
  algo_steps

example : floor_mod.Returns (-7, 3) 2 := by
  unfold floor_mod.Returns
  algo_steps

example : floor_mod.Returns (7, -3) (-2) := by
  unfold floor_mod.Returns
  algo_steps

example : «end».Returns 5 6 := by
  unfold «end».Returns
  algo_steps

example : boolean_alias.Returns true true := by
  unfold boolean_alias.Returns
  algo_steps

example : boolean_and_alias.Returns false false := by
  unfold boolean_and_alias.Returns
  algo_steps

example : branch_return.Returns 1 7 := by
  unfold branch_return.Returns
  algo_steps

example : branch_return.Returns (-1) (-7) := by
  unfold branch_return.Returns
  algo_steps

example : break_by_return.Returns 4 42 := by
  unfold break_by_return.Returns
  algo_steps

example : false_and.Returns () false := by
  unfold false_and.Returns
  algo_steps

example : true_or.Returns () true := by
  unfold true_or.Returns
  algo_steps

example : short_chain.Returns () false := by
  unfold short_chain.Returns
  algo_steps
