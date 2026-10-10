import TranscriptsGeneratedPoints

/-!
Analysis outline:
- `assignment_sets_one`: Local assignment postcondition.
- `assignment_then_pass`: Composition of local postconditions.
- `assignment_fact_on_transcript`: Assignment fact on every valid transcript.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace TranscriptsAnalysis

-- A local postcondition: the supplied state need not have been reached from
-- function entry, and there is no transcript to construct.
theorem assignment_sets_one {before after : Configuration}
    (transition : Step before after) (location : assignment.At.set before) :
    assignment.At.after after ∧ assignment.Local.a after = some 1 := by
  cases transition <;> simp_all [assignment.At.set, assignment.At.after, assignment.Local.a]

theorem pass_preserves_one {before after : Configuration}
    (transition : Step before after) (location : assignment.At.after before)
    (value : assignment.Local.a before = some 1) :
    assignment.At.ready after ∧ assignment.Local.a after = some 1 := by
  cases transition <;> simp_all [assignment.At.after, assignment.At.ready, assignment.Local.a]

-- Two local facts compose without a whole-run assumption.
theorem assignment_then_pass {before middle after : Configuration}
    (assignmentStep : Step before middle) (pass : Step middle after)
    (location : assignment.At.set before) :
    Reaches Step before after ∧ assignment.At.ready after ∧ assignment.Local.a after = some 1 := by
  have assigned := assignment_sets_one assignmentStep location
  exact ⟨(Reaches.single assignmentStep).trans (Reaches.single pass),
    pass_preserves_one pass assigned.1 assigned.2⟩

-- The same statement-level fact applies to every adjacent pair in any valid
-- transcript, including an unfinished prefix of a larger execution.
theorem assignment_fact_on_transcript {initial final : Configuration} {trace : Transcript}
    (valid : Valid Step initial trace final) :
    Valid (fun before after => assignment.At.set before → assignment.Local.a after = some 1)
      initial trace final := by
  exact valid.lift (fun _ _ transition location => (assignment_sets_one transition location).2)

end TranscriptsAnalysis
