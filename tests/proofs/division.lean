-- Zero is retained until the division guard gets stuck. Lean's total
-- integer-division operation therefore cannot manufacture a source output.
private def zeroDivisorRegion : Configuration → Prop
  | .active _ (.fn_quotient pc s) _ =>
    pc = 2 ∧ s.v1 = 0
  | _ => False

private theorem zeroDivisorRegion_preserved (before after : Configuration)
    (transition : Step before after) (inside : zeroDivisorRegion before) : zeroDivisorRegion after := by
  cases transition <;> simp_all [zeroDivisorRegion]

theorem division_by_zero_has_no_output (input output : Int) :
    ¬ «quotient».Returns (input, 0) output := by
  rintro ⟨_, _, run⟩
  exact Algo2LeanCore.Reaches.invariant run zeroDivisorRegion
    (by simp [«quotient».initial, zeroDivisorRegion, Algo2LeanCore.start, «quotient».load]) zeroDivisorRegion_preserved
