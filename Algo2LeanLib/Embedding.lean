import Algo2Lean

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Checked reuse of function summaries across compilation units.

A larger algorithm may compile the same function alongside additional functions.
Its frame and result types are then larger, although the heap representation and
function behavior are unchanged. A `CallEmbedding` records the type translation;
a checked one-step simulation lifts existing proofs without replaying them.
-/

namespace Algo2LeanCore

universe h f₁ r₁ f₂ r₂

/-- Translate a component's frames and return values into a larger program.
    Decoding is required only to translate suspended callers; returning an
    encoded result must recover the original value exactly. Results belonging
    only to the larger program decode to `none` and yield its invalid frame. -/
structure CallEmbedding (SourceFrame : Type f₁) (SourceResult : Type r₁)
    (TargetFrame : Type f₂) (TargetResult : Type r₂) where
  encodeFrame : SourceFrame → TargetFrame
  encodeResult : SourceResult → TargetResult
  decodeResult : TargetResult → Option SourceResult
  invalidFrame : TargetFrame
  decode_encode : ∀ result, decodeResult (encodeResult result) = some result

namespace CallEmbedding

variable {Heap : Type h} {SourceFrame : Type f₁} {SourceResult : Type r₁}
    {TargetFrame : Type f₂} {TargetResult : Type r₂}

/-- Extend one suspended component call to the larger result type. -/
def continuation (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (resume : SourceResult → SourceFrame) (result : TargetResult) : TargetFrame :=
  match embedding.decodeResult result with
  | some original => embedding.encodeFrame (resume original)
  | none => embedding.invalidFrame

/-- Translate suspended component calls. Additional target callers are kept
    separately so reused summaries remain valid in every calling context. -/
def stack (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (source : Stack SourceFrame SourceResult) : Stack TargetFrame TargetResult :=
  source.map embedding.continuation

/-- Embed an intermediate component state under arbitrary target callers.
    A completed component resumes its enclosing target caller. -/
def config (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (caller : Stack TargetFrame TargetResult) :
    Config Heap SourceFrame SourceResult → Config Heap TargetFrame TargetResult
  | .active heap frame suspended =>
      .active heap (embedding.encodeFrame frame) (embedding.stack suspended ++ caller)
  | .done heap result => resumeConfig heap (embedding.encodeResult result) caller

@[simp] theorem stack_nil (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult) :
    embedding.stack [] = [] := rfl

@[simp] theorem stack_cons (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (resume : SourceResult → SourceFrame) (rest : Stack SourceFrame SourceResult) :
    embedding.stack (resume :: rest) =
      embedding.continuation resume :: embedding.stack rest := rfl

@[simp] theorem stack_append (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (first second : Stack SourceFrame SourceResult) :
    embedding.stack (first ++ second) = embedding.stack first ++ embedding.stack second := by
  simp [stack]

@[simp] theorem config_active (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (caller : Stack TargetFrame TargetResult) (heap : Heap) (frame : SourceFrame)
    (suspended : Stack SourceFrame SourceResult) :
    embedding.config caller (.active heap frame suspended) =
      .active heap (embedding.encodeFrame frame) (embedding.stack suspended ++ caller) := rfl

@[simp] theorem config_done (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (caller : Stack TargetFrame TargetResult) (heap : Heap) (result : SourceResult) :
    embedding.config caller (.done heap result) =
      resumeConfig heap (embedding.encodeResult result) caller := rfl

/-- Returning through a translated component stack agrees with translating the
    original return. This is the only place the result round-trip law is needed. -/
@[simp] theorem resume (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (caller : Stack TargetFrame TargetResult) (heap : Heap) (result : SourceResult)
    (suspended : Stack SourceFrame SourceResult) :
    embedding.config caller (resumeConfig heap result suspended) =
      resumeConfig heap (embedding.encodeResult result) (embedding.stack suspended ++ caller) := by
  cases suspended with
  | nil => rfl
  | cons continuation rest => simp [resumeConfig, CallEmbedding.continuation, embedding.decode_encode]

/-- The embedding changes control representation, preserving the entire heap,
    including shared references and all named clocks. -/
@[simp] theorem heap (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (caller : Stack TargetFrame TargetResult) (state : Config Heap SourceFrame SourceResult) :
    (embedding.config caller state).heap = state.heap := by
  cases state with
  | active => rfl
  | done => cases caller <;> rfl

/-- Every source transition must be checked against an actual target transition.
    The arbitrary caller prevents an embedding certificate from being valid
    only for isolated top-level executions. -/
def Simulates (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    (sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop)
    (targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop) : Prop :=
  ∀ caller ⦃before after⦄, sourceStep before after →
    targetStep (embedding.config caller before) (embedding.config caller after)

/-- Map an explicit transcript once the local simulation has been checked. -/
theorem valid (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop}
    (simulation : embedding.Simulates sourceStep targetStep)
    (caller : Stack TargetFrame TargetResult)
    {before after : Config Heap SourceFrame SourceResult} {states : List (Config Heap SourceFrame SourceResult)}
    (execution : Valid sourceStep before states after) :
    Valid targetStep (embedding.config caller before)
      (states.map (embedding.config caller)) (embedding.config caller after) := by
  induction execution with
  | single state => exact .single _
  | cons transition tail ih => exact .cons (simulation caller transition) ih

/-- Reuse a completed or partial execution without exposing its transcript. -/
theorem reaches (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop}
    (simulation : embedding.Simulates sourceStep targetStep)
    (caller : Stack TargetFrame TargetResult)
    {before after : Config Heap SourceFrame SourceResult}
    (execution : Reaches sourceStep before after) :
    Reaches targetStep (embedding.config caller before) (embedding.config caller after) := by
  obtain ⟨states, valid⟩ := execution
  exact ⟨states.map (embedding.config caller), embedding.valid simulation caller valid⟩

/-- Reuse a function's already-proved summary in any larger program. The result,
    heap effects, and clock effects are preserved; no function proof is replayed. -/
theorem summary (embedding : CallEmbedding SourceFrame SourceResult TargetFrame TargetResult)
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Config Heap TargetFrame TargetResult → Config Heap TargetFrame TargetResult → Prop}
    (simulation : embedding.Simulates sourceStep targetStep)
    {before after : Heap} {frame : SourceFrame} {result : SourceResult}
    (contract : Summary sourceStep before frame after result) :
    Summary targetStep before (embedding.encodeFrame frame) after (embedding.encodeResult result) := by
  intro caller
  simpa [start] using embedding.reaches simulation caller contract.root

end CallEmbedding
end Algo2LeanCore
