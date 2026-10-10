-- The step argument recurses before the range can test its empty interval.
-- All finite prefixes remain in the argument-evaluation region.
private def boundRegion : Configuration → Prop
  | .active _ (.fn_diverging_bound pc _) _ => pc = 8 ∨ pc = 9 ∨ pc = 10 ∨ pc = 11
  | _ => False

private theorem boundRegion_preserved (before after : Configuration)
    (transition : Step before after) (inside : boundRegion before) : boundRegion after := by
  cases transition <;> simp_all [boundRegion]

theorem diverging_range_bound_has_no_output (input output : Int) :
    ¬ diverging_bound.Returns input output := by
  rintro ⟨_, _, run⟩
  exact Algo2LeanCore.Reaches.invariant run boundRegion
    (by simp [diverging_bound.initial, boundRegion, Algo2LeanCore.start]) boundRegion_preserved
