-- Each call enters the same nonreturning region with another suspended caller.
-- The invariant applies to every stack, so recursion depth is unrestricted.
private def recursiveRegion : Configuration → Prop
  | .active _ (.fn_recurse pc _) _ => pc = 2 ∨ pc = 3
  | _ => False

private theorem recursiveRegion_preserved (before after : Configuration)
    (transition : Step before after) (inside : recursiveRegion before) : recursiveRegion after := by
  cases transition <;> simp_all [recursiveRegion]

theorem recursion_has_no_output (input output : Int) :
    ¬ recurse.Returns input output := by
  rintro ⟨_, _, run⟩
  exact Algo2LeanCore.Reaches.invariant run recursiveRegion
    (by simp [recurse.initial, recursiveRegion, Algo2LeanCore.start]) recursiveRegion_preserved
