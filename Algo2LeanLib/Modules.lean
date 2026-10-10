import Algo2Lean

/-!
Execution of an independently compiled module inside another module.

The caller has one frame constructor for each imported module instance. It stores the
imported frame, its private control stack, and a continuation in the caller.
The heap is shared. One caller transition delegates any imported transition;
no imported instruction, frame, result, or proof is translated or regenerated.
-/

namespace Algo2LeanCore.ModuleCall

universe h f₁ r₁ f₂ r₂

variable {Heap : Type h} {SourceFrame : Type f₁} {SourceResult : Type r₁}
    {TargetFrame : Type f₂} {TargetResult : Type r₂}

/-- The caller's constructor for a suspended imported execution. -/
abbrev Wrapper (SourceFrame : Type f₁) (SourceResult : Type r₁)
    (TargetFrame : Type f₂) :=
  SourceFrame → Stack SourceFrame SourceResult → (SourceResult → TargetFrame) → TargetFrame

/-- Install a source state inside the caller. Returning resumes the caller in
    the same step, retaining its outer control stack and the whole source heap. -/
def config (wrap : Wrapper SourceFrame SourceResult TargetFrame)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult) :
    Config Heap SourceFrame SourceResult → Config Heap TargetFrame TargetResult
  | .active heap frame inner => .active heap (wrap frame inner resume) caller
  | .done heap result => .active heap (resume result) caller

@[simp] theorem config_active (wrap : Wrapper SourceFrame SourceResult TargetFrame)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult)
    (heap : Heap) (frame : SourceFrame) (inner : Stack SourceFrame SourceResult) :
    config wrap resume caller (.active heap frame inner) =
      .active heap (wrap frame inner resume) caller := rfl

@[simp] theorem config_done (wrap : Wrapper SourceFrame SourceResult TargetFrame)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult)
    (heap : Heap) (result : SourceResult) :
    config wrap resume caller (.done heap result) =
      .active heap (resume result) caller := rfl

/-- Wrapping a source configuration preserves its entire heap snapshot.
    Mutations and clock increments performed by source transitions remain visible. -/
@[simp] theorem heap (wrap : Wrapper SourceFrame SourceResult TargetFrame)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult)
    (state : Config Heap SourceFrame SourceResult) :
    (config wrap resume caller state).heap = state.heap := by
  cases state <;> rfl

/-- The caller's suspended calls remain untouched throughout an imported call. -/
@[simp] theorem stack (wrap : Wrapper SourceFrame SourceResult TargetFrame)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult)
    (state : Config Heap SourceFrame SourceResult) :
    (config wrap resume caller state).stack = caller := by
  cases state <;> rfl

/-- Every active source transition is delegated through one imported-module wrapper. -/
def Delegates (wrap : Wrapper SourceFrame SourceResult TargetFrame)
    (sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop)
    (targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop) : Prop :=
  ∀ heap frame inner resume caller after,
    sourceStep (.active heap frame inner) after →
    targetStep (.active heap (wrap frame inner resume) caller)
      (config wrap resume caller after)

/-- The same imported transition runs under every caller continuation and stack. -/
def Simulates (wrap : Wrapper SourceFrame SourceResult TargetFrame)
    (sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop)
    (targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop) : Prop :=
  ∀ resume caller ⦃before after⦄, sourceStep before after →
    targetStep (config wrap resume caller before) (config wrap resume caller after)

/-- Completed source states have no outgoing transitions, so the single active
    delegation rule supplies the entire simulation certificate. -/
theorem Delegates.simulates {wrap : Wrapper SourceFrame SourceResult TargetFrame}
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop}
    (delegates : Delegates wrap sourceStep targetStep)
    (terminal : ∀ heap result, Terminal sourceStep (.done heap result)) :
    Simulates wrap sourceStep targetStep := by
  intro resume caller before after transition
  cases before with
  | active heap frame inner => exact delegates heap frame inner resume caller after transition
  | done heap result => exact False.elim (terminal heap result after transition)

/-- Map any finite transcript, including a prefix that stops inside a diverging
    imported call. No termination or completed-call premise is needed. -/
theorem valid {wrap : Wrapper SourceFrame SourceResult TargetFrame}
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop}
    (simulation : Simulates wrap sourceStep targetStep)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult)
    {before after : Config Heap SourceFrame SourceResult}
    {states : List (Config Heap SourceFrame SourceResult)}
    (execution : Valid sourceStep before states after) :
    Valid targetStep (config wrap resume caller before)
      (states.map (config wrap resume caller)) (config wrap resume caller after) := by
  induction execution with
  | single state => exact .single _
  | cons transition tail ih => exact .cons (simulation resume caller transition) ih

/-- Reuse a completed or partial source execution without exposing its transcript. -/
theorem reaches {wrap : Wrapper SourceFrame SourceResult TargetFrame}
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop}
    (simulation : Simulates wrap sourceStep targetStep)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult)
    {before after : Config Heap SourceFrame SourceResult}
    (execution : Reaches sourceStep before after) :
    Reaches targetStep (config wrap resume caller before) (config wrap resume caller after) := by
  obtain ⟨states, execution⟩ := execution
  exact ⟨states.map (config wrap resume caller), valid simulation resume caller execution⟩

/-- Apply an existing imported summary directly at its call site. The imported
    result may have a different type from the caller's result; only its typed
    continuation consumes it. Heap effects and all clock effects are unchanged. -/
theorem summary {wrap : Wrapper SourceFrame SourceResult TargetFrame}
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop}
    (simulation : Simulates wrap sourceStep targetStep)
    (resume : SourceResult → TargetFrame) (caller : Stack TargetFrame TargetResult)
    {before after : Heap} {frame : SourceFrame} {result : SourceResult}
    (contract : Summary sourceStep before frame after result) :
    Reaches targetStep (.active before (wrap frame [] resume) caller)
      (.active after (resume result) caller) := by
  simpa only [start, config_active, config_done] using
    reaches simulation resume caller contract.root

end Algo2LeanCore.ModuleCall
