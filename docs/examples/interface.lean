import InterfaceGeneratedPoints

-- Independent proof companion; no test-specific tactics are used.
open Algo2LeanCore Algo2LeanGenerated

namespace InterfaceTutorial

-- These are the generated declarations, with their actual current types.
#check assignment.Returns
#check touch.Returns
#check touch.load
#check touch.ValidInput
#check touch.ValidTranscript
#check touch.ValidHeapTranscript
#check touch.Run
#check touch.Call
#check touch.Call.run
#check touch.CallFrom
#check assignment.At.set
#check assignment.Local.a
#check touch.Local.b
#check touch.Element.b

-- Output predicates use source-level values: Seq here means Int → Int.
example : Int → Int → Prop := assignment.Returns
example : (Algo2LeanGenerated.Seq × Algo2LeanGenerated.Seq) → Int → Prop := touch.Returns
example : Int → Transcript → Prop := assignment.ValidTranscript
example : (Algo2LeanGenerated.Seq × Algo2LeanGenerated.Seq) → Transcript → Prop := touch.ValidTranscript
example : Heap → (SeqRef × SeqRef) → Transcript → Prop := touch.ValidHeapTranscript
example : Configuration → Int → Option Int := touch.Element.b

theorem assignment_output (n : Int) : assignment.Returns n 1 := by
  refine ⟨{}, True.intro, ?_⟩
  refine (Reaches.single (Step.assignment_pc3 _ _ _)).trans ?_
  refine (Reaches.single (Step.assignment_pc2 _ _ _)).trans ?_
  exact Reaches.single (Step.assignment_pc1 _ _ _)

-- Value-input transcript predicates perform the same loading as Returns.
-- This loader-validity lemma is proved here for this example.
theorem loaded_inputs_valid (input : Algo2LeanGenerated.Seq × Algo2LeanGenerated.Seq) :
    touch.ValidInput (touch.load input).1 (touch.load input).2 := by
  simp [touch.ValidInput, touch.load, Heap.allocate]

-- An unfinished transcript containing only its initial state is valid.
theorem initial_transcript (input : Algo2LeanGenerated.Seq × Algo2LeanGenerated.Seq) :
    touch.ValidTranscript input
      [touch.initial (touch.load input).1 (touch.load input).2] := by
  exact ⟨loaded_inputs_valid input, _, Valid.single _⟩

-- A local postcondition needs one transition, not a complete execution.
theorem assignment_local {before after : Configuration}
    (transition : Step before after) (location : assignment.At.set before) :
    assignment.At.ready after ∧ assignment.Local.a after = some 1 := by
  cases transition <;>
    simp_all [assignment.At.set, assignment.At.ready, assignment.Local.a]

def AssignmentFact (before after : Configuration) : Prop :=
  assignment.At.set before → assignment.Local.a after = some 1

-- Reuse the local theorem for every adjacent pair in an arbitrary transcript.
theorem assignment_fact_in_transcript {initial final : Configuration} {trace : Transcript}
    (valid : Valid Step initial trace final) : Valid AssignmentFact initial trace final := by
  exact valid.lift (fun _ _ transition location => (assignment_local transition location).2)

-- A source-facing property of every visited return location. The proof checks
-- the possible finite prefixes; its statement mentions no implementation fields.
theorem assignment_ready_in_transcript (n : Int) (trace : Transcript)
    (valid : assignment.ValidTranscript n trace) :
    ∀ cfg ∈ trace, assignment.At.ready cfg → assignment.Local.a cfg = some 1 := by
  obtain ⟨_, final, valid⟩ := valid
  cases valid with
  | single => simp [assignment.initial, assignment.load, start, assignment.At.ready]
  | cons first tail =>
    cases first
    cases tail with
    | single => simp [assignment.initial, assignment.load, start,
        assignment.At.ready, assignment.Local.a]
    | cons second tail =>
      cases second
      cases tail with
      | single => simp [assignment.initial, assignment.load, start,
          assignment.At.ready, assignment.Local.a]
      | cons third tail =>
        cases third
        cases tail with
        | single => simp [assignment.initial, assignment.load, start,
            assignment.At.ready, assignment.Local.a, resumeConfig]
        | cons impossible _ => cases impossible

-- Outputs and transcripts use the same execution evidence. This bridge simply
-- exposes that evidence; it neither reruns the program nor assumes termination.
theorem assignment_output_has_transcript {n output : Int}
    (produces : assignment.Returns n output) :
    ∃ heap trace, assignment.ValidTranscript n trace ∧
      Config.done heap (Result.fn_assignment output) ∈ trace := by
  obtain ⟨heap, inputsValid, trace, valid⟩ := produces
  exact ⟨heap, trace, ⟨inputsValid, _, valid⟩, valid.final_mem⟩

-- For this simple return, the returned value was read at @ready. This private
-- return-segment argument supplies the connection used by the public theorem.
private theorem assignment_output_ready_witness {n output : Int}
    (produces : assignment.Returns n output) :
    ∃ trace cfg, assignment.ValidTranscript n trace ∧ cfg ∈ trace ∧
      assignment.At.ready cfg ∧ assignment.Local.a cfg = some output := by
  obtain ⟨heap, inputsValid, trace, valid⟩ := produces
  have transcript : assignment.ValidTranscript n trace := ⟨inputsValid, _, valid⟩
  cases valid with
  | cons first tail =>
    cases first
    cases tail with
    | cons second tail =>
      cases second
      cases tail with
      | cons third tail =>
        cases third
        cases tail with
        | single =>
          exact ⟨_, _, transcript,
            List.mem_cons_of_mem _ List.mem_cons_self, True.intro, rfl⟩
        | cons impossible _ => cases impossible

-- This output property explicitly reuses the theorem about reached @ready
-- states. The user-facing claims mention only source inputs, labels and locals.
theorem assignment_output_is_one {n output : Int}
    (produces : assignment.Returns n output) : output = 1 := by
  obtain ⟨trace, cfg, valid, member, location, returned⟩ := assignment_output_ready_witness produces
  have ready := assignment_ready_in_transcript n trace valid cfg member location
  exact Option.some.inj (returned.symm.trans ready)

-- The field exists internally before assignment, but is not initialized in
-- the source language, so the public getter returns none there.
example (heap : Heap) (n : Int) : assignment.Local.a (assignment.initial heap n) = none := rfl

-- The source-facing sequence helper reads through the current heap for us.
-- The raw touch.Local.b getter remains available when object identity matters.
-- This assertion does not claim that the location is reached.
def BAtZeroIs (expected : Int) (cfg : Configuration) : Prop :=
  touch.At.observe cfg ∧ touch.Element.b cfg 0 = some expected

-- The following small execution lemma uses generated instruction names.
-- Such names are lower-level details and can change when source code changes.
theorem touch_execution (heap : Heap) (a b : SeqRef)
    (a_valid : a < heap.nextRef) (b_valid : b < heap.nextRef) :
    touch.Run heap (a, b) (heap.write a 0 1) ((heap.write a 0 1).read b 0) := by
  refine ⟨⟨a_valid, b_valid⟩, ?_⟩
  apply Reaches.prepend (Step.touch_pc3 _ _ _ a_valid)
  apply Reaches.prepend (Step.touch_pc2 _ _ _ b_valid)
  exact Reaches.single (Step.touch_pc1 _ _ _)

-- Allocate once and pass reference 0 twice to express input aliasing.
def sharedHeap : Heap := ({} : Heap).allocate (fun _ => 3)

theorem shared_inputs_valid : touch.ValidInput sharedHeap (0, 0) := by
  simp [touch.ValidInput, sharedHeap, Heap.allocate]

theorem touch_aliased : touch.Run sharedHeap (0, 0) (sharedHeap.write 0 0 1) 1 := by
  simpa [Heap.read, Heap.write] using
    touch_execution sharedHeap 0 0 (by decide) (by decide)

-- Equal contents supplied to Returns are loaded into distinct objects.
theorem touch_distinct_contents : touch.Returns ((fun _ => 3), (fun _ => 3)) 3 := by
  let heap := (touch.load ((fun _ => 3), (fun _ => 3))).1
  refine ⟨heap.write 0 0 1, ?_⟩
  have execution := touch_execution heap 0 1
    (by change (0 : Nat) < 2; decide) (by change (1 : Nat) < 2; decide)
  simpa [heap, touch.load, Heap.read, Heap.write, Heap.allocate] using execution

end InterfaceTutorial
