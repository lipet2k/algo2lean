import Algo2LeanLib.Determinism
import Algo2LeanProbability.Call

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Reuse finite deterministic executions in probabilistic analyses. Termination
comes from the original transcript, not from a separate probability argument.
The final heap and result can be observed jointly.
-/

noncomputable section
open MeasureTheory

namespace Algo2LeanProbability

/-- A possible, unique successor receives all of an instruction's mass.
This also covers a uniform choice whose outcomes coincide. -/
theorem choiceLaw_eq_pure_of_unique {State : Type*}
    (current after : State) (choice : Algo2LeanCore.Choice State)
    (possible : choice.Allows after)
    (unique : ∀ other, choice.Allows other → other = after) :
    choiceLaw current choice = PMF.pure (some after) := by
  have support : (choiceLaw current choice).support = {some after} := by
    cases choice with
    | next state =>
        have same : after = state := possible
        simp [same]
    | halt => cases possible
    | fail => cases possible
    | uniform lower upper resume =>
        obtain ⟨value, lowerBound, upperBound, same⟩ := possible
        rw [choiceLaw_uniform current lower upper resume (lt_of_le_of_lt lowerBound upperBound)]
        ext sampled
        rw [PMF.mem_support_map_iff]
        constructor
        · rintro ⟨draw, member, rfl⟩
          have bounds := (uniformInt_support lower upper draw _).mp member
          simp [unique (resume draw) ⟨draw, bounds.1, bounds.2, rfl⟩]
        · intro member
          have sampled_eq : sampled = some after := member
          exact ⟨value, (uniformInt_support lower upper value _).mpr
            ⟨lowerBound, upperBound⟩, by rw [sampled_eq, same]⟩
  ext sampled
  by_cases same : sampled = some after
  · subst sampled
    rw [(PMF.apply_eq_one_iff _ _).mpr support, PMF.pure_apply_self]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr (by simpa [support] using same),
      PMF.pure_apply_of_ne _ _ same]

/-- Reuse a terminating deterministic trace as a complete return law. The
observer must halt at every recognized return, so it cannot silently stop at
an earlier, nonterminal point of the trace. -/
theorem HasLaw.of_reaches_on {State Output : Type*}
    {step : State → State → Prop} (next : State → Algo2LeanCore.Choice State)
    (observe : State → Option Output)
    (agreement : ∀ before after, (next before).Allows after ↔ step before after)
    {safe : State → Prop} (region : Algo2LeanCore.DeterministicOn step safe)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    {initial final : State} {output : Output}
    (atStart : safe initial)
    (run : Algo2LeanCore.Reaches step initial final)
    (seen : observe final = some output) :
    HasLaw next observe initial (PMF.pure output) := by
  intro payoff
  change callExpected next observe initial payoff = pmfExpected (PMF.pure output) payoff
  rw [pmfExpected_pure]
  obtain ⟨states, valid⟩ := run
  induction valid with
  | single state => exact callExpected_return next observe state output seen payoff
  | @cons before after rest final advance tail ih =>
      have possible := (agreement before after).mpr advance
      have notReturned : observe before = none := by
        cases observed : observe before with
        | none => rfl
        | some value =>
            rw [halting before value observed] at possible
            cases possible
      have notBoundary : ¬ completed observe (some before) := by
        rintro ⟨current, value, same, observed⟩
        cases same
        simp [notReturned] at observed
      have pure := choiceLaw_eq_pure_of_unique before after (next before) possible
        (fun other allowed => region.unique atStart ((agreement before other).mp allowed) advance)
      change Stopped.expected (transition next) (completed observe)
        (returnReward observe payoff) (some before) = _
      rw [Stopped.expected_unfold, if_neg notBoundary]
      simp only [transition, pure, PMF.toMeasure_pure]
      rw [lintegral_dirac' _ Measurable.of_discrete]
      exact ih (region.preserved advance atStart) seen

/-- Whole-unit determinism is the special case with no restriction. -/
theorem HasLaw.of_reaches {State Output : Type*}
    {step : State → State → Prop} (next : State → Algo2LeanCore.Choice State)
    (observe : State → Option Output)
    (agreement : ∀ before after, (next before).Allows after ↔ step before after)
    (deterministic : Algo2LeanCore.Deterministic step)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    {initial final : State} {output : Output}
    (run : Algo2LeanCore.Reaches step initial final)
    (seen : observe final = some output) :
    HasLaw next observe initial (PMF.pure output) := by
  exact HasLaw.of_reaches_on next observe agreement
    (safe := fun _ => True) ⟨fun _ _ => trivial, fun _ => deterministic⟩ halting trivial run seen

end Algo2LeanProbability
