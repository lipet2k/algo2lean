import Algo2LeanLib.Modules

/-!
Install an execution in an existing stack of suspended callers. Instructions
inside the call retain their local stack; returning from its outermost frame
resumes the supplied caller. Heap contents and clock counters are preserved.
-/

namespace Algo2LeanCore.CallContext

universe h f r f₂ r₂
variable {Heap : Type h} {Frame : Type f} {Result : Type r}

def config (caller : Stack Frame Result) :
    Config Heap Frame Result → Config Heap Frame Result
  | .active heap frame inner => .active heap frame (inner ++ caller)
  | .done heap result => resumeConfig heap result caller

@[simp] theorem active (caller inner : Stack Frame Result) (heap : Heap) (frame : Frame) :
    config caller (.active heap frame inner) = .active heap frame (inner ++ caller) := rfl

@[simp] theorem done (caller : Stack Frame Result) (heap : Heap) (result : Result) :
    config caller (.done heap result) = resumeConfig heap result caller := rfl

@[simp] theorem resume (caller inner : Stack Frame Result) (heap : Heap) (result : Result) :
    config caller (resumeConfig heap result inner) =
      resumeConfig heap result (inner ++ caller) := by
  cases inner <;> rfl

@[simp] theorem module_config {SourceFrame : Type f₂} {SourceResult : Type r₂}
    (wrap : ModuleCall.Wrapper SourceFrame SourceResult Frame)
    (resume : SourceResult → Frame) (inner caller : Stack Frame Result)
    (state : Config Heap SourceFrame SourceResult) :
    config caller (ModuleCall.config wrap resume inner state) =
      ModuleCall.config wrap resume (inner ++ caller) state := by
  cases state <;> rfl

end Algo2LeanCore.CallContext
