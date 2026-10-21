import Std

/-!
Finite choices made by one algorithm instruction. This description uses only
Lean's standard library; the optional probability package supplies its law.
Integer intervals include the lower bound and exclude the upper bound. An empty interval has no allowed successor.
-/

namespace Algo2LeanCore

universe u v

/-- A deterministic instruction, a fresh uniform integer draw, successful
    termination, or a failed instruction. The latter two have no transitions. -/
inductive Choice (State : Type u) where
  | next (state : State)
  | uniform (lower upper : Int) (resume : Int → State)
  | halt
  | fail

namespace Choice

variable {State : Type u} {Target : Type v}

/-- Possible successors, without asserting a probability or termination. -/
def Allows : Choice State → State → Prop
  | .next state, after => after = state
  | .uniform lower upper resume, after =>
      ∃ value, lower ≤ value ∧ value < upper ∧ after = resume value
  | .halt, _ => False
  | .fail, _ => False

/-- Embed an instruction in a caller while retaining the same random choice. -/
def map (embed : State → Target) : Choice State → Choice Target
  | .next state => .next (embed state)
  | .uniform lower upper resume => .uniform lower upper (embed ∘ resume)
  | .halt => .halt
  | .fail => .fail

@[simp] theorem allows_next {state after : State} :
    Allows (.next state) after ↔ after = state := Iff.rfl

@[simp] theorem allows_uniform {lower upper : Int} {resume : Int → State}
    {after : State} : Allows (.uniform lower upper resume) after ↔
      ∃ value, lower ≤ value ∧ value < upper ∧ after = resume value := Iff.rfl

@[simp] theorem not_allows_halt (after : State) : ¬ Allows .halt after := id

@[simp] theorem not_allows_fail (after : State) : ¬ Allows .fail after := id

theorem uniform_bounds {lower upper : Int} {resume : Int → State} {after : State}
    (allowed : Allows (.uniform lower upper resume) after) : lower < upper := by
  obtain ⟨value, lowerBound, upperBound, _⟩ := allowed
  omega

theorem allows_map (embed : State → Target) (choice : Choice State) (after : Target) :
    Allows (choice.map embed) after ↔
      ∃ before, choice.Allows before ∧ after = embed before := by
  cases choice with
  | next state => simp [map, Allows]
  | uniform lower upper resume =>
      constructor
      · rintro ⟨value, lowerBound, upperBound, rfl⟩
        exact ⟨resume value, ⟨value, lowerBound, upperBound, rfl⟩, rfl⟩
      · rintro ⟨before, ⟨value, lowerBound, upperBound, rfl⟩, rfl⟩
        exact ⟨value, lowerBound, upperBound, rfl⟩
  | halt => simp [map, Allows]
  | fail => simp [map, Allows]

@[simp] theorem map_id (choice : Choice State) : choice.map id = choice := by
  cases choice <;> rfl

@[simp] theorem map_map {Other : Type w} (first : State → Target)
    (second : Target → Other) (choice : Choice State) :
    (choice.map first).map second = choice.map (second ∘ first) := by
  cases choice <;> rfl

end Choice
end Algo2LeanCore
