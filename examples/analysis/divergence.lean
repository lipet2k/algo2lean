import DivergenceGenerated

/-!
Analysis outline:
- `endless_loop_has_no_output`: Loop has no terminating output.
- `endless_recursion_has_no_output`: Recursion has no terminating output.
- `endless_loop_has_nontrivial_prefix`: Finite loop transcript.
- `endless_recursion_has_nontrivial_prefix`: Finite recursive transcript.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace DivergenceAnalysis

-- The proof identifies a region preserved by every transition. The return
-- location lies outside it, so no finite completed transcript can exist.
theorem endless_loop_has_no_execution (initialHeap finalHeap : Heap) (input output : Int) :
    ¬ endless_loop.Run initialHeap input finalHeap output := by
  let looping : Configuration → Prop := fun configuration => match configuration with
    | .active _ (.fn_endless_loop pc state) _ =>
      pc = 4 ∨ pc = 5 ∨ (pc = 3 ∧ state.t2 = true)
    | _ => False
  rintro ⟨_, execution⟩
  exact execution.invariant looping
    (by simp [looping, endless_loop.initial, start])
    (by intro before after transition inside; cases transition <;> simp_all [looping])

theorem endless_loop_has_no_output (input output : Int) :
    ¬ endless_loop.Returns input output := by
  rintro ⟨finalHeap, execution⟩
  exact endless_loop_has_no_execution _ finalHeap input output execution

-- The invariant allows an arbitrary call stack, so it applies at every depth
-- of self-recursion; it is not a bound on how many calls were attempted.
theorem endless_recursion_has_no_execution (initialHeap finalHeap : Heap) (input output : Int) :
    ¬ endless_recursion.Run initialHeap input finalHeap output := by
  let recursing : Configuration → Prop := fun configuration => match configuration with
    | .active _ (.fn_endless_recursion pc _) _ => pc = 2 ∨ pc = 3
    | _ => False
  rintro ⟨_, execution⟩
  exact execution.invariant recursing
    (by simp [recursing, endless_recursion.initial, start])
    (by intro before after transition inside; cases transition <;> simp_all [recursing])

theorem endless_recursion_has_no_output (input output : Int) :
    ¬ endless_recursion.Returns input output := by
  rintro ⟨finalHeap, execution⟩
  exact endless_recursion_has_no_execution _ finalHeap input output execution

-- Valid finite prefixes still exist, even though neither function returns.
theorem endless_loop_has_nontrivial_prefix (input : Int) :
    ∃ trace, endless_loop.ValidTranscript input trace ∧ trace.length = 4 := by
  have first := Step.endless_loop_pc4 {} { v0 := input } []
  have second := Step.endless_loop_pc3_true {} { v0 := input, t2 := true } [] rfl
  have third := Step.endless_loop_pc5 {} { v0 := input, t2 := true } []
  have executionPrefix := Valid.cons first (Valid.cons second (Valid.cons third (Valid.single _)))
  exact ⟨_, ⟨True.intro, _, executionPrefix⟩, rfl⟩

theorem endless_recursion_has_nontrivial_prefix (input : Int) :
    ∃ trace, endless_recursion.ValidTranscript input trace ∧ trace.length = 3 := by
  have first := Step.endless_recursion_pc3 {} { v0 := input } []
  have second := Step.endless_recursion_pc2 {} { v0 := input, t2 := input } []
  have executionPrefix := Valid.cons first (Valid.cons second (Valid.single _))
  exact ⟨_, ⟨True.intro, _, executionPrefix⟩, rfl⟩

end DivergenceAnalysis
