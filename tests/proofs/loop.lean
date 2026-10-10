-- A local preservation fact excludes the unreachable return, and is lifted
-- to every completed transcript. No loop iterations are enumerated.
private def foreverRegion : Configuration → Prop
  | .active _ (.fn_forever pc s) _ =>
    pc = 4 ∨ pc = 5 ∨ (pc = 3 ∧ s.t2 = true)
  | _ => False

private theorem foreverRegion_preserved (before after : Configuration)
    (transition : Step before after) (inside : foreverRegion before) : foreverRegion after := by
  cases transition <;> simp_all [foreverRegion]

theorem infinite_loop_has_no_output (input output : Int) :
    ¬ forever.Returns input output := by
  rintro ⟨_, _, run⟩
  exact Algo2LeanCore.Reaches.invariant run foreverRegion
    (by simp [forever.initial, foreverRegion, Algo2LeanCore.start]) foreverRegion_preserved
