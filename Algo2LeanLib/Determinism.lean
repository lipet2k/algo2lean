import Algo2Lean

/-! Optional determinism on an invariant part of the existing transition relation. -/

namespace Algo2LeanCore

/-- A closed region in which every actual next step is unique. -/
structure DeterministicOn {State : Type u} (step : State → State → Prop)
    (safe : State → Prop) : Prop where
  preserved : ∀ {before after}, step before after → safe before → safe after
  unique : ∀ {before left right}, safe before → step before left → step before right → left = right

theorem Reaches.eq_of_terminal_on {State : Type u} {step : State → State → Prop}
    {safe : State → Prop} (region : DeterministicOn step safe)
    {initial left right : State} (atStart : safe initial)
    (first : Reaches step initial left) (second : Reaches step initial right)
    (atLeft : Terminal step left) (atRight : Terminal step right) : left = right := by
  obtain ⟨states, first⟩ := first
  obtain ⟨others, second⟩ := second
  induction first generalizing others right with
  | single state =>
      cases second with
      | single => rfl
      | cons advance tail => exact False.elim (atLeft _ advance)
  | cons advance tail ih =>
      cases second with
      | single => exact False.elim (atRight _ advance)
      | cons other rest =>
          have same := region.unique atStart advance other
          cases same
          exact ih (region.preserved advance atStart) atLeft atRight _ rest

namespace FrameSafety

universe v w

def stack {Frame : Type v} {Result : Type w} (safe : Frame → Prop)
    (stack : Stack Frame Result) : Prop :=
  ∀ resume ∈ stack, ∀ result, safe (resume result)

def config {Heap : Type u} {Frame : Type v} {Result : Type w} (safe : Frame → Prop) :
    Config Heap Frame Result → Prop
  | .done _ _ => True
  | .active _ frame callers => safe frame ∧ stack safe callers

theorem resume {Heap : Type u} {Frame : Type v} {Result : Type w} {safe : Frame → Prop}
    (heap : Heap) (result : Result) {callers : Stack Frame Result}
    (valid : stack safe callers) : config safe (resumeConfig heap result callers) := by
  cases callers with
  | nil => trivial
  | cons head tail =>
      exact ⟨valid head (by simp) result, fun next member => valid next (by simp [member])⟩

theorem cons {Frame : Type v} {Result : Type w} {safe : Frame → Prop}
    {resume : Result → Frame} {callers : Stack Frame Result}
    (head : ∀ result, safe (resume result)) (tail : stack safe callers) :
    stack safe (resume :: callers) := by
  intro next member
  rcases List.mem_cons.mp member with same | member
  · subst next; exact head
  · exact tail next member

end FrameSafety
end Algo2LeanCore
