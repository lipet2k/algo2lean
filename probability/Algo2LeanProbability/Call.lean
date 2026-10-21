import Algo2LeanProbability

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Completed-call expectations are stopped expectations of the same local
probability laws that generate execution paths. The terminal reward may inspect
the complete final heap and returned value jointly. A run that never reaches
the boundary contributes zero; this is an unconditional expectation and does
not condition on termination.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Algo2LeanProbability


/-- Expectation under a discrete law without requiring a measurable-space
instance on the output type. -/
def pmfExpected {Output : Type*} (law : PMF Output) (payoff : Output → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' output, law output * payoff output

/-- Only possible outputs matter when rewriting a reward. This lets a caller
    use a callee's heap and result invariants inside a continuation. -/
theorem pmfExpected_congr_support {Output : Type*} (law : PMF Output)
    (first second : Output → ℝ≥0∞)
    (same : ∀ value ∈ law.support, first value = second value) :
    pmfExpected law first = pmfExpected law second := by
  unfold pmfExpected
  apply tsum_congr
  intro value
  by_cases possible : value ∈ law.support
  · rw [same value possible]
  · rw [(PMF.apply_eq_zero_iff _ _).2 possible]
    simp

@[simp] theorem pmfExpected_pure {Output : Type*} (output : Output)
    (payoff : Output → ℝ≥0∞) : pmfExpected (PMF.pure output) payoff = payoff output := by
  classical
  simp [pmfExpected, PMF.pure_apply]

theorem pmfExpected_bind {First Second : Type*} (law : PMF First)
    (continuation : First → PMF Second) (payoff : Second → ℝ≥0∞) :
    pmfExpected (law.bind continuation) payoff =
      pmfExpected law (fun first => pmfExpected (continuation first) payoff) := by
  simp only [pmfExpected, PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

theorem pmfExpected_map {First Second : Type*} (law : PMF First)
    (transform : First → Second) (payoff : Second → ℝ≥0∞) :
    pmfExpected (law.map transform) payoff = pmfExpected law (fun first => payoff (transform first)) := by
  rw [PMF.map, pmfExpected_bind]
  simp

/-- A uniform integer law reduces every nonnegative reward to a finite sum. -/
theorem pmfExpected_uniformInt (lower upper : Int) (bounds : lower < upper)
    (payoff : Int → ℝ≥0∞) :
    pmfExpected (uniformInt lower upper bounds) payoff =
      ∑ value ∈ Finset.Ico lower upper,
        payoff value * ((upper - lower).toNat : ℝ≥0∞)⁻¹ := by
  unfold pmfExpected
  rw [tsum_eq_sum (s := Finset.Ico lower upper) (fun value outside => by
    have absent : ¬ (lower ≤ value ∧ value < upper) := by
      simpa only [Finset.mem_Ico] using outside
    simp [uniformInt_apply, absent])]
  apply Finset.sum_congr rfl
  intro value member
  rw [uniformInt_mass lower upper value bounds (Finset.mem_Ico.mp member).1
    (Finset.mem_Ico.mp member).2, mul_comm]

namespace Stopped

variable {State : Type*} [MeasurableSpace State] [DiscreteMeasurableSpace State]

/-- Reward received on the first boundary visit within the given number of
transitions. Before a boundary is reached the reward is zero. -/
def within (step : State → PMF State) (boundary : State → Prop)
    (reward : State → ℝ≥0∞) : ℕ → State → ℝ≥0∞
  | 0, state => if boundary state then reward state else 0
  | n + 1, state => if boundary state then reward state else
      ∫⁻ after, within step boundary reward n after ∂(step state).toMeasure

/-- The unconditional reward at the first boundary visit, allowing arbitrarily
many transitions. Nontermination before the boundary contributes zero. -/
def expected (step : State → PMF State) (boundary : State → Prop)
    (reward : State → ℝ≥0∞) (initial : State) : ℝ≥0∞ :=
  ⨆ n : ℕ, within step boundary reward n initial

theorem within_mono_time (step : State → PMF State) (boundary : State → Prop)
    (reward : State → ℝ≥0∞) : Monotone (within step boundary reward) := by
  apply monotone_nat_of_le_succ
  intro n state
  induction n generalizing state with
  | zero =>
      simp only [within]
      split_ifs <;> simp
  | succ n ih =>
      simp only [within]
      split_ifs
      · exact le_rfl
      · exact lintegral_mono ih

@[simp] theorem expected_boundary (step : State → PMF State) (boundary : State → Prop)
    (reward : State → ℝ≥0∞) (state : State) (atBoundary : boundary state) :
    expected step boundary reward state = reward state := by
  have same : ∀ n, within step boundary reward n state = reward state := by
    intro n
    cases n <;> simp [within, atBoundary]
  simp [expected, same]

theorem expected_unfold (step : State → PMF State) (boundary : State → Prop)
    (reward : State → ℝ≥0∞) (state : State) :
    expected step boundary reward state =
      if boundary state then reward state else
        ∫⁻ after, expected step boundary reward after ∂(step state).toMeasure := by
  by_cases atBoundary : boundary state
  · simp [atBoundary, expected_boundary]
  · simp only [atBoundary, ↓reduceIte, expected]
    rw [lintegral_iSup (fun _ => Measurable.of_discrete)
      (within_mono_time step boundary reward)]
    apply le_antisymm
    · apply iSup_le
      intro n
      cases n with
      | zero => simp [within, atBoundary]
      | succ n =>
          simpa only [within, atBoundary, ↓reduceIte] using
            le_iSup (fun n => ∫⁻ after, within step boundary reward n after
              ∂(step state).toMeasure) n
    · apply iSup_le
      intro n
      simpa only [within, atBoundary, ↓reduceIte] using
        le_iSup (fun n => within step boundary reward n state) (n + 1)

/-- Induction rule for arbitrary-length calls. A nonnegative upper solution of
the local boundary/transition equations bounds the completed-call expectation. -/
theorem expected_le (step : State → PMF State) (boundary : State → Prop)
    (reward bound : State → ℝ≥0∞)
    (atBoundary : ∀ state, boundary state → reward state ≤ bound state)
    (advance : ∀ state, ¬ boundary state →
      (∫⁻ after, bound after ∂(step state).toMeasure) ≤ bound state)
    (initial : State) : expected step boundary reward initial ≤ bound initial := by
  apply iSup_le
  intro n
  induction n generalizing initial with
  | zero =>
      simp only [within]
      split_ifs with h
      · exact atBoundary initial h
      · exact bot_le
  | succ n ih =>
      simp only [within]
      split_ifs with h
      · exact atBoundary initial h
      · exact (lintegral_mono ih).trans (advance initial h)

theorem expected_mono (step : State → PMF State) (boundary : State → Prop)
    {first second : State → ℝ≥0∞} (bound : ∀ state, first state ≤ second state)
    (initial : State) : expected step boundary first initial ≤
      expected step boundary second initial := by
  apply expected_le
  · intro state atBoundary
    rw [expected_boundary step boundary second state atBoundary]
    exact bound state
  · intro state notBoundary
    rw [expected_unfold step boundary second state, if_neg notBoundary]

/-- First-return decomposition. Any final boundary contained in an earlier
boundary can be analyzed by first reaching the earlier boundary, then reusing
the continuation's expectation from the reached state. This remains true for
unbounded calls and when either stage can fail to terminate. -/
theorem expected_first_return (step : State → PMF State)
    (earlier final : State → Prop) (contained : ∀ state, final state → earlier state)
    (reward : State → ℝ≥0∞) (initial : State) :
    expected step final reward initial =
      expected step earlier (expected step final reward) initial := by
  apply le_antisymm
  · apply expected_le
    · intro state atFinal
      rw [expected_boundary step earlier _ state (contained state atFinal),
        expected_boundary step final reward state atFinal]
    · intro state notFinal
      by_cases atEarlier : earlier state
      · rw [expected_boundary step earlier _ state atEarlier]
        calc
          (∫⁻ after, expected step earlier (expected step final reward) after
              ∂(step state).toMeasure) ≤
              ∫⁻ after, expected step final reward after ∂(step state).toMeasure := by
            apply lintegral_mono
            intro after
            apply expected_le
            · intro state atEarlier
              exact le_rfl
            · intro state notEarlier
              rw [expected_unfold step final reward state,
                if_neg (fun h => notEarlier (contained state h))]
          _ = expected step final reward state := by
            rw [expected_unfold step final reward state, if_neg notFinal]
      · rw [expected_unfold step earlier _ state, if_neg atEarlier]
  · apply expected_le
    · intro state atEarlier
      exact le_rfl
    · intro state notEarlier
      rw [expected_unfold step final reward state,
        if_neg (fun h => notEarlier (contained state h))]

theorem within_mono_reward (step : State → PMF State) (boundary : State → Prop)
    {first second : State → ℝ≥0∞} (bound : ∀ state, first state ≤ second state)
    (time : ℕ) (state : State) :
    within step boundary first time state ≤ within step boundary second time state := by
  induction time generalizing state with
  | zero =>
      simp only [within]
      split_ifs
      · exact bound state
      · exact le_rfl
  | succ time ih =>
      simp only [within]
      split_ifs
      · exact bound state
      · exact lintegral_mono ih

/-- Enlarging the available time commutes with an increasing limit of rewards.
This supports unbounded nonnegative output and cost observations. -/
theorem expected_iSup (step : State → PMF State) (boundary : State → Prop)
    (reward : ℕ → State → ℝ≥0∞) (increasing : Monotone reward) (initial : State) :
    expected step boundary (fun state => ⨆ n, reward n state) initial =
      ⨆ n, expected step boundary (reward n) initial := by
  have finite : ∀ time state,
      within step boundary (fun state => ⨆ n, reward n state) time state =
        ⨆ n, within step boundary (reward n) time state := by
    intro time
    induction time with
    | zero =>
        intro state
        simp only [within]
        split_ifs <;> simp
    | succ time ih =>
        intro state
        by_cases stop : boundary state
        · simp [within, stop]
        · simp only [within, stop, ↓reduceIte, ih]
          apply lintegral_iSup (fun _ => Measurable.of_discrete)
          intro first second bound state
          exact within_mono_reward step boundary (increasing bound) time state
  simp only [expected, finite]
  exact iSup_comm

/-- Local probability-preserving embeddings preserve complete stopped-call
expectations. This is the reusable bridge for inserting a callee into a caller
stack without re-proving its output or cost analysis. -/
theorem expected_map {Target : Type*} [MeasurableSpace Target]
    [DiscreteMeasurableSpace Target]
    (step : State → PMF State) (targetStep : Target → PMF Target)
    (embed : State → Target)
    (boundary : State → Prop) (targetBoundary : Target → Prop)
    (steps : ∀ state, ¬ boundary state →
      targetStep (embed state) = (step state).map embed)
    (boundaries : ∀ state, targetBoundary (embed state) ↔ boundary state)
    (reward : State → ℝ≥0∞) (targetReward : Target → ℝ≥0∞)
    (rewards : ∀ state, boundary state → targetReward (embed state) = reward state)
    (initial : State) :
    expected targetStep targetBoundary targetReward (embed initial) =
      expected step boundary reward initial := by
  have finite : ∀ n state,
      within targetStep targetBoundary targetReward n (embed state) =
        within step boundary reward n state := by
    intro n
    induction n with
    | zero =>
        intro state
        simp only [within, boundaries]
        by_cases stop : boundary state
        · simp [stop, rewards state stop]
        · simp [stop]
    | succ n ih =>
        intro state
        simp only [within, boundaries]
        by_cases stop : boundary state
        · simp [stop, rewards state stop]
        · simp only [stop, ↓reduceIte, steps state stop]
          rw [← PMF.toMeasure_map embed _ Measurable.of_discrete,
            lintegral_map Measurable.of_discrete Measurable.of_discrete]
          exact lintegral_congr (fun after => ih after)
  simp only [expected, finite]

/-- Kernel underlying the local discrete transition distribution. -/
def kernel (step : State → PMF State) : Kernel State State where
  toFun state := (step state).toMeasure
  measurable' := Measurable.of_discrete

/-- At absorbing boundaries, bounded first-return rewards equal ordinary
finite-time rewards. This connects stopped reasoning to the path construction. -/
theorem within_eq_lintegral (step : State → PMF State) (boundary : State → Prop)
    (reward : State → ℝ≥0∞)
    (absorbing : ∀ state, boundary state → step state = PMF.pure state)
    (time : ℕ) (state : State) :
    within step boundary reward time state =
      ∫⁻ after, (if boundary after then reward after else 0)
        ∂((kernel step) ^ time) state := by
  induction time generalizing state with
  | zero =>
      change (if boundary state then reward state else 0) =
        ∫⁻ after, (if boundary after then reward after else 0) ∂Measure.dirac state
      rw [lintegral_dirac' _ Measurable.of_discrete]
  | succ time ih =>
      rw [pow_succ]
      change _ = ∫⁻ after, (if boundary after then reward after else 0)
        ∂(((kernel step) ^ time) ∘ₖ kernel step) state
      rw [Kernel.lintegral_comp _ _ _ Measurable.of_discrete]
      change _ = ∫⁻ after, (∫⁻ final, (if boundary final then reward final else 0)
        ∂((kernel step) ^ time) after) ∂(step state).toMeasure
      simp_rw [← ih]
      by_cases atBoundary : boundary state
      · rw [absorbing state atBoundary, PMF.toMeasure_pure,
          lintegral_dirac' _ Measurable.of_discrete]
        cases time <;> simp [within, atBoundary]
      · simp [within, atBoundary]

end Stopped

/-- Successful completion observed in a sampled configuration. -/
def completed {State Output : Type*} (observe : State → Option Output)
    (state : SampleState State) : Prop :=
  ∃ current output, state = some current ∧ observe current = some output

/-- A reward of the observed completed outcome, zero elsewhere. -/
def returnReward {State Output : Type*} (observe : State → Option Output)
    (payoff : Output → ℝ≥0∞) (state : SampleState State) : ℝ≥0∞ :=
  match state with
  | none => 0
  | some current => match observe current with
    | none => 0
    | some output => payoff output

/-- The expected value of an arbitrary nonnegative function of the completed
return. The observer normally returns the final heap together with the result. -/
def callExpected {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (payoff : Output → ℝ≥0∞) : ℝ≥0∞ :=
  Stopped.expected (transition next) (completed observe) (returnReward observe payoff)
    (some initial)

/-- Unconditional probability of a property of the completed return. -/
def callProbability {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (post : Output → Prop) : ℝ≥0∞ :=
  callExpected next observe initial (fun output => if post output then 1 else 0)

/-- A complete probability law for the joint final heap and output. Equality
for every nonnegative reward makes the contract reusable for probabilities,
expectations, and correlated output/cost observations. -/
def HasLaw {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (law : PMF Output) : Prop :=
  ∀ payoff : Output → ℝ≥0∞,
    callExpected next observe initial payoff = ∑' output, law output * payoff output

private theorem finiteKernel_eq_pow {State : Type*}
    (next : State → Algo2LeanCore.Choice State) (n : ℕ) :
    finiteKernel next n = (Stopped.kernel (transition next)) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [finiteKernel, ih, pow_succ']
      rfl

/-- At any finite horizon the stopped-call expectation is an ordinary marginal
expectation, provided successful returns halt. -/
theorem callExpected_eq_iSup {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    (initial : State) (payoff : Output → ℝ≥0∞) :
    callExpected next observe initial payoff =
      ⨆ time : ℕ, ∫⁻ state, returnReward observe payoff state ∂finiteLaw next initial time := by
  have absorbing : ∀ state, completed observe state →
      transition next state = PMF.pure state := by
    rintro state ⟨current, output, rfl, seen⟩
    simp [transition, halting current output seen]
  have reward_eq : (fun state : SampleState State => if completed observe state then
      returnReward observe payoff state else 0) = returnReward observe payoff := by
    funext state
    cases state with
    | none => simp [completed, returnReward]
    | some current =>
        cases seen : observe current with
        | none => simp [completed, returnReward, seen]
        | some output =>
            have yes : completed observe (some current) := ⟨current, output, rfl, seen⟩
            simp only [if_pos yes]
  unfold callExpected Stopped.expected
  apply iSup_congr
  intro time
  rw [Stopped.within_eq_lintegral _ _ _ absorbing, reward_eq]
  rw [finiteLaw, finiteKernel_eq_pow]

/-- Completed-call probabilities agree exactly with events in the full
infinite execution law. This is not a separately postulated call semantics. -/
theorem callProbability_eq_execution {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    (initial : State) (post : Output → Prop) :
    callProbability next observe initial post =
      probability (execution next initial) (Event.returnsWhere observe post) := by
  let property : SampleState State → Prop := fun state =>
    ∃ current output, state = some current ∧ observe current = some output ∧ post output
  have preserved : ∀ state, property state →
      ∀ᵐ after ∂(transition next state).toMeasure, property after := by
    rintro state ⟨current, output, rfl, seen, holds⟩
    simp only [transition, halting current output seen, choiceLaw_halt, PMF.toMeasure_pure]
    apply (ae_dirac_iff MeasurableSet.of_discrete).2
    exact ⟨current, output, rfl, seen, holds⟩
  change callExpected next observe initial (fun output => if post output then 1 else 0) =
    probability (execution next initial) (Event.ever property)
  rw [callExpected_eq_iSup next observe halting,
    probability_ever_of_preserved next initial property preserved]
  apply iSup_congr
  intro time
  have reward_eq : returnReward observe (fun output => if post output then 1 else 0) =
      Set.indicator {state | property state} (fun _ => (1 : ℝ≥0∞)) := by
    funext state
    cases state with
    | none => simp [returnReward, property, Set.indicator, SampleState]
    | some current =>
        cases seen : observe current with
        | none => simp [returnReward, property, seen, Set.indicator, SampleState]
        | some output => simp [returnReward, property, seen, Set.indicator, SampleState]
  rw [reward_eq]
  exact lintegral_indicator_one MeasurableSet.of_discrete

/-- Replace a complete callee execution by its return expectation inside a
caller. The local transition embedding is required only before return; the
caller may continue with entirely different instructions afterwards. -/
theorem callExpected_in_context {State Output Target : Type*}
    [MeasurableSpace Target] [DiscreteMeasurableSpace Target]
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (targetStep : Target → PMF Target)
    (embed : SampleState State → Target) (earlier final : Target → Prop)
    (contained : ∀ state, final state → earlier state)
    (steps : ∀ state, ¬ completed observe state →
      targetStep (embed state) = (transition next state).map embed)
    (boundaries : ∀ state, earlier (embed state) ↔ completed observe state)
    (reward : Target → ℝ≥0∞) (payoff : Output → ℝ≥0∞)
    (continuation : ∀ state output, observe state = some output →
      Stopped.expected targetStep final reward (embed (some state)) = payoff output) :
    Stopped.expected targetStep final reward (embed (some initial)) =
      callExpected next observe initial payoff := by
  rw [Stopped.expected_first_return targetStep earlier final contained]
  apply Stopped.expected_map (transition next) targetStep embed
    (completed observe) earlier steps boundaries (returnReward observe payoff)
    (Stopped.expected targetStep final reward)
  rintro sampled ⟨state, output, rfl, seen⟩
  simpa [returnReward, seen] using continuation state output seen

/-- A proved probabilistic call contract is substituted into a caller by
averaging that caller's continuation over the joint returned heap and value.
No fixed bound on the callee's number of transitions is required. -/
theorem HasLaw.in_context {State Output Target : Type*}
    [MeasurableSpace Target] [DiscreteMeasurableSpace Target]
    {next : State → Algo2LeanCore.Choice State} {observe : State → Option Output}
    {initial : State} {law : PMF Output} (contract : HasLaw next observe initial law)
    (targetStep : Target → PMF Target) (embed : SampleState State → Target)
    (earlier final : Target → Prop)
    (contained : ∀ state, final state → earlier state)
    (steps : ∀ state, ¬ completed observe state →
      targetStep (embed state) = (transition next state).map embed)
    (boundaries : ∀ state, earlier (embed state) ↔ completed observe state)
    (reward : Target → ℝ≥0∞) (payoff : Output → ℝ≥0∞)
    (continuation : ∀ state output, observe state = some output →
      Stopped.expected targetStep final reward (embed (some state)) = payoff output) :
    Stopped.expected targetStep final reward (embed (some initial)) =
      ∑' output, law output * payoff output := by
  rw [callExpected_in_context next observe initial targetStep embed earlier final contained
    steps boundaries reward payoff continuation]
  exact contract payoff

/-- A complete call law assigns total probability one to successful return. -/
theorem HasLaw.termination {State Output : Type*}
    {next : State → Algo2LeanCore.Choice State} {observe : State → Option Output}
    {initial : State} {law : PMF Output} (contract : HasLaw next observe initial law) :
    callProbability next observe initial (fun _ => True) = 1 := by
  simpa [callProbability, tsum_mul_right] using contract (fun _ => 1)

/-- A completed state immediately receives its return reward. -/
theorem callExpected_return {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (output : Output) (seen : observe initial = some output)
    (payoff : Output → ℝ≥0∞) :
    callExpected next observe initial payoff = payoff output := by
  unfold callExpected
  rw [Stopped.expected_boundary _ _ _ _ ⟨initial, output, rfl, seen⟩]
  simp [returnReward, seen]

/-- An ordinary instruction exposes the expectation at its successor. -/
theorem callExpected_next {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial after : State) (notReturned : observe initial = none)
    (advance : next initial = .next after) (payoff : Output → ℝ≥0∞) :
    callExpected next observe initial payoff = callExpected next observe after payoff := by
  have notBoundary : ¬ completed observe (some initial) := by
    rintro ⟨current, output, same, seen⟩
    cases same
    simp [notReturned] at seen
  unfold callExpected
  rw [Stopped.expected_unfold, if_neg notBoundary]
  simp only [transition, advance, choiceLaw_next, PMF.toMeasure_pure]
  exact lintegral_dirac' _ Measurable.of_discrete

/-- A uniform draw averages the continuation's complete return reward. -/
theorem callExpected_uniform {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (lower upper : Int) (resume : Int → State)
    (notReturned : observe initial = none)
    (draw : next initial = .uniform lower upper resume) (bounds : lower < upper)
    (payoff : Output → ℝ≥0∞) :
    callExpected next observe initial payoff =
      ∑ value ∈ Finset.Ico lower upper,
        callExpected next observe (resume value) payoff * ((upper - lower).toNat : ℝ≥0∞)⁻¹ := by
  have notBoundary : ¬ completed observe (some initial) := by
    rintro ⟨current, output, same, seen⟩
    cases same
    simp [notReturned] at seen
  unfold callExpected
  rw [Stopped.expected_unfold, if_neg notBoundary]
  simp only [transition, draw, choiceLaw_uniform initial lower upper resume bounds]
  rw [← PMF.toMeasure_map (β := SampleState State)
    (mβ := inferInstance) (fun value => (some (resume value) : SampleState State)) _
    Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete]
  exact uniformInt_expected lower upper bounds _

end Algo2LeanProbability
