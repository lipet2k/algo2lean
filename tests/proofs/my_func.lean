private def myFuncRemaining (pc : Nat) (s : State_myFunc) : Int :=
  match pc with
  | 1 => s.t3
  | 2 => s.v1
  | 3 => s.t4
  | 4 => -s.v1
  | 5 => if s.t2 then s.v1 else -s.v1
  | _ => if s.v0 ≥ 1 then s.v1 else -s.v1

private def myFuncInvariant (expected : Int) : Configuration → Prop
  | .active _ (.fn_myFunc pc state) stack => stack = [] ∧ myFuncRemaining pc state = expected
  | .done _ (.fn_myFunc result) => result = expected
  | _ => False

private theorem myFunc_preserves (before after : Configuration) (step : Step before after)
    (h : myFuncInvariant expected before) : myFuncInvariant expected after := by
  cases step <;> simp_all [myFuncInvariant, myFuncRemaining, Algo2LeanCore.resumeConfig]

-- Exact characterization, including the exclusion of every invalid output.
theorem myFunc_output_iff (x y output : Int) :
    myFunc.Returns (x, y) output ↔
      (if x ≥ 1 then output = y else output = -y) := by
  constructor
  · rintro ⟨heap, _, run⟩
    have conclusion := run.invariant (myFuncInvariant (if x ≥ 1 then y else -y))
      (by simp [myFunc.initial, myFunc.load, Algo2LeanCore.start, myFuncInvariant, myFuncRemaining])
      (fun a b step h => myFunc_preserves a b step h)
    simpa only [myFuncInvariant, apply_ite (fun value => output = value)] using conclusion
  · intro h
    by_cases hx : x ≥ 1
    · rw [if_pos hx] at h
      subst output
      have condition : decide (x ≥ 1) = true := decide_eq_true hx
      unfold myFunc.Returns
      algo_steps
    · rw [if_neg hx] at h
      subst output
      have condition : decide (x ≥ 1) = false := decide_eq_false hx
      unfold myFunc.Returns
      algo_steps
