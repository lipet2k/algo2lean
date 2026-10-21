import Algo2LeanLib.CallContext
import Algo2LeanProbability.CallTransport

/-!
Reuse a completed-call reward under a suspended caller stack. The stack-depth
boundary is shared infrastructure: client analyses supply the callee's return
reward and the caller's continuation, without constructing execution paths or
proving a new stopping-boundary invariant at each call site.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

namespace Algo2LeanProbability

open Algo2LeanCore
open scoped ENNReal

variable {Heap Frame Result Output Final : Type*}

private def callExited : SampleState (Config Heap Frame Result) → Prop
  | none => True
  | some (.done _ _) => True
  | _ => False

private def callerDepth (depth : Nat) : SampleState (Config Heap Frame Result) → Prop
  | none => True
  | some (.done _ _) => True
  | some (.active _ _ stack) => stack.length ≤ depth

/-- Reuse a callee's return expectation inside any caller stack. All suspended
    frames are retained. The continuation premise describes both the accepted
    result tag and any rejected tags, whose completed-return reward is zero. -/
theorem callExpected_with_stack
    (next : Config Heap Frame Result → Choice (Config Heap Frame Result))
    (observe : Config Heap Frame Result → Option Output)
    (finalObserve : Config Heap Frame Result → Option Final)
    (context : ∀ heap frame inner caller,
      next (.active heap frame (inner ++ caller)) =
        (next (.active heap frame inner)).map (CallContext.config caller))
    (halts : ∀ heap result, next (.done heap result) = .halt)
    (activeNone : ∀ heap frame stack, observe (.active heap frame stack) = none)
    (finalActiveNone : ∀ heap frame stack, finalObserve (.active heap frame stack) = none)
    (heap : Heap) (frame : Frame) (resume : Result → Frame) (caller : Stack Frame Result)
    (reward : Final → ℝ≥0∞) (payoff : Output → ℝ≥0∞)
    (continuation : ∀ heap result,
      callExpected next finalObserve (.active heap (resume result) caller) reward =
        returnReward observe payoff (some (.done heap result))) :
    callExpected next finalObserve (.active heap frame (resume :: caller)) reward =
      callExpected next observe (.active heap frame []) payoff := by
  let embed : SampleState (Config Heap Frame Result) → SampleState (Config Heap Frame Result) :=
    Option.map (CallContext.config (resume :: caller))
  apply callExpected_in_context_stopped next observe (.active heap frame []) callExited
    (by
      rintro sample ⟨state, output, rfl, seen⟩
      cases state with
      | done => trivial
      | active h f stack => simp [activeNone] at seen)
    (by
      intro sample exited _
      cases sample with
      | none => rfl
      | some state => cases state with
        | active => exact False.elim exited
        | done h result => simp [transition, halts])
    (transition next) embed (callerDepth caller.length) (completed finalObserve)
    (by
      rintro sample ⟨state, output, rfl, seen⟩
      cases state with
      | done => trivial
      | active h f stack => simp [finalActiveNone] at seen)
    (by
      intro sample active
      cases sample with
      | none => exact False.elim (active trivial)
      | some state => cases state with
        | done => exact False.elim (active trivial)
        | active h f inner =>
          change choiceLaw _ (next (.active h f (inner ++ resume :: caller))) = _
          rw [context]
          exact choiceLaw_map (CallContext.config (resume :: caller))
            (.active h f inner) (next (.active h f inner)))
    (by
      intro sample
      cases sample with
      | none => rfl
      | some state => cases state with
        | done => simp [embed, callerDepth, callExited, CallContext.config, resumeConfig]
        | active h f inner =>
          simp only [embed, Option.map_some, CallContext.active, callerDepth,
            List.length_append, List.length_cons, callExited]
          constructor
          · intro impossible
            omega
          · intro impossible
            exact False.elim impossible)
    (returnReward finalObserve reward) payoff
  intro sample exited
  cases sample with
  | none =>
      exact Stopped.expected_eq_zero_of_self_loop (transition next) (completed finalObserve)
        (returnReward finalObserve reward) none (by simp [completed]) rfl
  | some state => cases state with
    | active => exact False.elim exited
    | done h result => exact continuation h result

variable {TargetFrame TargetResult : Type*}

private def outsideImport (inside : TargetFrame → Bool) :
    SampleState (Config Heap TargetFrame TargetResult) → Prop
  | none => True
  | some (.done _ _) => True
  | some (.active _ frame _) => inside frame = false

/-- Reuse an independently compiled module's return reward. The wrapper
    delegates source choices unchanged; its frame tag marks the call boundary.
    Analyses provide only the returned-value continuation, including rejected
    tags, instead of rebuilding a probabilistic path embedding. -/
theorem callExpected_import
    (next : Config Heap Frame Result → Choice (Config Heap Frame Result))
    (targetNext : Config Heap TargetFrame TargetResult → Choice (Config Heap TargetFrame TargetResult))
    (observe : Config Heap Frame Result → Option Output)
    (finalObserve : Config Heap TargetFrame TargetResult → Option Final)
    (wrap : ModuleCall.Wrapper Frame Result TargetFrame)
    (inside : TargetFrame → Bool) (resume : Result → TargetFrame)
    (caller : Stack TargetFrame TargetResult)
    (delegates : ∀ heap frame inner,
      targetNext (.active heap (wrap frame inner resume) caller) =
        (next (.active heap frame inner)).map (ModuleCall.config wrap resume caller))
    (halts : ∀ heap result, next (.done heap result) = .halt)
    (activeNone : ∀ heap frame stack, observe (.active heap frame stack) = none)
    (finalActiveNone : ∀ heap frame stack, finalObserve (.active heap frame stack) = none)
    (wrapped : ∀ frame inner, inside (wrap frame inner resume) = true)
    (resumed : ∀ result, inside (resume result) = false)
    (heap : Heap) (frame : Frame) (reward : Final → ℝ≥0∞) (payoff : Output → ℝ≥0∞)
    (continuation : ∀ heap result,
      callExpected targetNext finalObserve (.active heap (resume result) caller) reward =
        returnReward observe payoff (some (.done heap result))) :
    callExpected targetNext finalObserve (.active heap (wrap frame [] resume) caller) reward =
      callExpected next observe (.active heap frame []) payoff := by
  let embed : SampleState (Config Heap Frame Result) → SampleState (Config Heap TargetFrame TargetResult) :=
    Option.map (ModuleCall.config wrap resume caller)
  apply callExpected_in_context_stopped next observe (.active heap frame []) callExited
    (by
      rintro sample ⟨state, output, rfl, seen⟩
      cases state with
      | done => trivial
      | active h f stack => simp [activeNone] at seen)
    (by
      intro sample exited _
      cases sample with
      | none => rfl
      | some state => cases state with
        | active => exact False.elim exited
        | done h result => simp [transition, halts])
    (transition targetNext) embed (outsideImport inside) (completed finalObserve)
    (by
      rintro sample ⟨state, output, rfl, seen⟩
      cases state with
      | done => trivial
      | active h f stack => simp [finalActiveNone] at seen)
    (by
      intro sample active
      cases sample with
      | none => exact False.elim (active trivial)
      | some state => cases state with
        | done => exact False.elim (active trivial)
        | active h f inner =>
          change choiceLaw _ (targetNext (.active h (wrap f inner resume) caller)) = _
          rw [delegates]
          exact choiceLaw_map (ModuleCall.config wrap resume caller)
            (.active h f inner) (next (.active h f inner)))
    (by
      intro sample
      cases sample with
      | none => rfl
      | some state => cases state with
        | done h result => simp [embed, outsideImport, callExited, resumed]
        | active h f inner => simp [embed, outsideImport, callExited, wrapped])
    (returnReward finalObserve reward) payoff
  intro sample exited
  cases sample with
  | none =>
      exact Stopped.expected_eq_zero_of_self_loop (transition targetNext) (completed finalObserve)
        (returnReward finalObserve reward) none (by simp [completed]) rfl
  | some state => cases state with
    | active => exact False.elim exited
    | done h result => exact continuation h result

end Algo2LeanProbability
