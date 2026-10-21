import Algo2LeanLib.Parallel
import Algo2LeanLib.Modules

namespace Algo2LeanParallel

/-- Reuse an imported parallel execution at the existing module-call boundary.
The original callee supplies both its serialization and its cost/access record. -/
theorem invocation_summary
    {Heap : Type u} {SourceFrame : Type v} {SourceResult : Type w}
    {TargetFrame : Type v'} {TargetResult : Type w'}
    {next : Heap → SourceFrame → Action Heap SourceFrame SourceResult}
    {sourceStep : Algo2LeanCore.Config Heap SourceFrame SourceResult →
      Algo2LeanCore.Config Heap SourceFrame SourceResult → Prop}
    {targetStep : Algo2LeanCore.Config Heap TargetFrame TargetResult →
      Algo2LeanCore.Config Heap TargetFrame TargetResult → Prop}
    {wrap : Algo2LeanCore.ModuleCall.Wrapper SourceFrame SourceResult TargetFrame}
    (source : Simulation next sourceStep)
    (module : Algo2LeanCore.ModuleCall.Simulates wrap sourceStep targetStep)
    {heap final : Heap} {frame : SourceFrame} {resume : SourceResult → TargetFrame}
    {following : TargetFrame} {cost : Cost} {access : Access}
    (run : (Eval.invocation next heap frame resume).run final following cost access)
    (caller : Algo2LeanCore.Stack TargetFrame TargetResult) :
    Algo2LeanCore.Reaches targetStep (.active heap (wrap frame [] resume) caller)
      (.active final following caller) := by
  obtain ⟨result, execution, rfl⟩ := run
  exact Algo2LeanCore.ModuleCall.summary module resume caller (execution.summary source)

end Algo2LeanParallel
