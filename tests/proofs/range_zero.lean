-- Even an empty range with step zero gets stuck before its first test.
-- The argument bounds and the initial heap are arbitrary.
private def zeroStepRegion : Configuration → Prop
  | .active _ (.fn_zero_step pc s) _ =>
    pc = 11 ∨ pc = 10 ∨ pc = 9 ∨ pc = 8 ∨ (pc = 7 ∧ s.t7 = 0)
  | _ => False

private theorem zeroStepRegion_preserved (before after : Configuration)
    (transition : Step before after) (inside : zeroStepRegion before) : zeroStepRegion after := by
  cases transition <;> simp_all [zeroStepRegion]

theorem zero_step_execution_impossible (heap finalHeap : Heap) (start stop output : Int) :
    ¬ zero_step.Run heap (start, stop) finalHeap output := by
  rintro ⟨_, run⟩
  exact Algo2LeanCore.Reaches.invariant run zeroStepRegion
    (by simp [zero_step.initial, zeroStepRegion, Algo2LeanCore.start]) zeroStepRegion_preserved

theorem range_zero_step_has_no_output (start stop output : Int) :
    ¬ zero_step.Returns (start, stop) output := by
  rintro ⟨finalHeap, run⟩
  exact zero_step_execution_impossible _ finalHeap start stop output run
