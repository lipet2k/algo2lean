import MyFuncGenerated

open Algo2LeanCore Algo2LeanGenerated

namespace MyFuncAnalysis

/-- The branch result is available under any caller stack, without changing the heap. -/
theorem summary (heap : Heap) (x y : Int) :
    myFunc.Call heap (x, y) heap (if x ≥ 1 then y else -y) := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.myFunc_pc6 ..))
  by_cases condition : x ≥ 1
  · apply Reaches.trans (Reaches.single (Step.myFunc_pc5_true _ _ _ (by simpa only [decide_eq_true_eq] using condition)))
    apply Reaches.trans (Reaches.single (Step.myFunc_pc2 ..))
    simpa [condition] using Reaches.single (Step.myFunc_pc1 heap _ stack)
  · apply Reaches.trans (Reaches.single (Step.myFunc_pc5_false _ _ _ (by simpa only [decide_eq_false_iff_not] using condition)))
    apply Reaches.trans (Reaches.single (Step.myFunc_pc4 ..))
    simpa [condition] using Reaches.single (Step.myFunc_pc3 heap _ stack)

/-- Exact characterization: every input terminates with this value, and no other
    value is an output. The instruction invariant is local to the proof. -/
theorem output_iff (x y output : Int) :
    myFunc.Returns (x, y) output ↔ output = (if x ≥ 1 then y else -y) := by
  constructor
  · rintro ⟨heap, _, run⟩
    let remaining (pc : Nat) (s : State_myFunc) : Int :=
      match pc with
      | 1 => s.t3
      | 2 => s.v1
      | 3 => s.t4
      | 4 => -s.v1
      | 5 => if s.t2 then s.v1 else -s.v1
      | _ => if s.v0 ≥ 1 then s.v1 else -s.v1
    let invariant : Configuration → Prop
      | .active _ (.fn_myFunc pc state) stack =>
          stack = [] ∧ remaining pc state = (if x ≥ 1 then y else -y)
      | .done _ (.fn_myFunc result) => result = (if x ≥ 1 then y else -y)
      | _ => False
    apply run.invariant invariant
    · simp [myFunc.initial, myFunc.load, start, invariant, remaining]
    · intro before after transition hypothesis
      cases transition <;> simp_all [invariant, remaining, resumeConfig]
  · intro value
    subst output
    exact ⟨{}, (summary {} x y).1, (summary {} x y).2.root⟩

end MyFuncAnalysis
