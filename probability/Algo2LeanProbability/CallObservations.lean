import Algo2LeanProbability.Call
import Algo2LeanProbability.Observations

/-!
Connect successful-call rewards with total costs on complete execution paths.
The connection requires almost-sure successful termination and a counter that
does not decrease along supported source transitions. Failure and divergence
are never removed by conditioning or renormalization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Algo2LeanProbability

private theorem trajectory_current {State : Type*}
    (next : State → Algo2LeanCore.Choice State) (time : ℕ)
    (history : (i : Finset.Iic time) → SampleState State) :
    ((Kernel.traj (X := fun _ => SampleState State) (historyKernel next) time) history).map
      (fun run => run time) = Measure.dirac (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) := by
  have projection := Kernel.traj_map_frestrictLe (X := fun _ => SampleState State)
    (κ := historyKernel next) time time
  have mapped := congrArg
    (fun k => k.map (fun past => past ⟨time, Finset.mem_Iic.mpr le_rfl⟩)) projection
  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop), Kernel.partialTraj_self,
    Kernel.id_map (measurable_pi_apply _)] at mapped
  have applied := congrArg (fun k => k history) mapped
  change ((Kernel.traj (X := fun _ => SampleState State) (historyKernel next) time).map
    (fun run => run time)) history = _ at applied
  rw [Kernel.map_apply _ (measurable_pi_apply time)] at applied
  exact applied

/-- A measurable relation that holds almost surely for each local instruction
    holds at every adjacent time of almost every execution. -/
theorem execution_relation {State : Type*} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (relation : SampleState State → SampleState State → Prop)
    (measurable : MeasurableSet {pair : SampleState State × SampleState State |
      relation pair.1 pair.2})
    (locally : ∀ state, ∀ᵐ after ∂(transition next state).toMeasure, relation state after) :
    ∀ᵐ run ∂execution next initial, ∀ time, relation (run time) (run (time + 1)) := by
  apply ae_all_iff.mpr
  intro time
  let trajectories := Kernel.traj (X := fun _ => SampleState State) (historyKernel next) time
  have along_history : ∀ history, ∀ᵐ run ∂trajectories history,
      relation (run time) (run (time + 1)) := by
    intro history
    have current : ∀ᵐ run ∂trajectories history,
        run time = history ⟨time, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply ae_of_ae_map (μ := trajectories history)
        (f := fun run : Run State => run time)
        (p := fun state => state = history ⟨time, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply time).aemeasurable
      rw [trajectory_current next time history]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 rfl
    have future : ∀ᵐ run ∂trajectories history,
        relation (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) (run (time + 1)) := by
      apply ae_of_ae_map (μ := trajectories history)
        (f := fun run : Run State => run (time + 1))
        (p := relation (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩))
        (measurable_pi_apply (time + 1)).aemeasurable
      have projection := Kernel.map_traj_succ_self (X := fun _ => SampleState State)
        (κ := historyKernel next) (a := time)
      have applied := congrArg (fun k => k history) projection
      rw [Kernel.map_apply _ (measurable_pi_apply (time + 1))] at applied
      rw [applied]
      exact locally _
    filter_upwards [current, future] with run same follows
    simpa only [same] using follows
  have relation_measurable : MeasurableSet {run : Run State |
      relation (run time) (run (time + 1))} :=
    measurable.preimage (show Measurable (fun run : Run State => (run time, run (time + 1))) from
      (measurable_pi_apply time).prodMk (measurable_pi_apply (time + 1)))
  have composed := Kernel.ae_comp_of_ae_ae
    (κ := Kernel.partialTraj (X := fun _ => SampleState State) (historyKernel next) 0 time)
    (η := trajectories) (a := fun _ => some initial) relation_measurable (ae_of_all _ along_history)
  simpa only [trajectories, Kernel.traj_comp_partialTraj (Nat.zero_le time), execution]
    using composed

/-- Local monotonicity of a scalar observation implies monotonicity along
    almost every complete execution. Impossible ambient paths need no proof. -/
theorem execution_observation_mono {State : Type*}
    (next : State → Algo2LeanCore.Choice State) (initial : State)
    (value : SampleState State → ℝ≥0∞)
    (locally : ∀ state, ∀ᵐ after ∂(transition next state).toMeasure, value state ≤ value after) :
    ∀ᵐ run ∂execution next initial, Monotone (fun time => value (run time)) := by
  have measurable : MeasurableSet {pair : SampleState State × SampleState State |
      value pair.1 ≤ value pair.2} :=
    measurableSet_le (Measurable.of_discrete.comp measurable_fst)
      (Measurable.of_discrete.comp measurable_snd)
  filter_upwards [execution_relation next initial (fun first second => value first ≤ value second)
    measurable locally] with run adjacent
  exact monotone_nat_of_le_succ adjacent

private theorem ae_pmf_support {Value : Type*} [MeasurableSpace Value]
    [DiscreteMeasurableSpace Value] (law : PMF Value) :
    ∀ᵐ value ∂law.toMeasure, value ∈ law.support := by
  exact (mem_ae_iff_prob_eq_one MeasurableSet.of_discrete).2
    ((law.toMeasure_apply_eq_one_iff MeasurableSet.of_discrete).2 (Set.Subset.refl _))

private def extendedCounter {State : Type*} (counter : State → ℕ) : SampleState State → ℝ≥0∞
  | none => ∞
  | some state => counter state

private theorem counter_mono {State : Type*}
    (next : State → Algo2LeanCore.Choice State) (initial : State) (counter : State → ℕ)
    (advance : ∀ before after, (next before).Allows after → counter before ≤ counter after) :
    ∀ᵐ run ∂execution next initial, Monotone (fun time => extendedCounter counter (run time)) := by
  apply execution_observation_mono next initial (extendedCounter counter)
  intro state
  cases state with
  | none =>
      simp only [transition, PMF.toMeasure_pure]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 le_rfl
  | some before =>
      filter_upwards [ae_pmf_support (transition next (some before))] with after supported
      cases after with
      | none => exact le_top
      | some after =>
          have alternatives := (choiceLaw_support before after (next before)).mp supported
          rcases alternatives with allowed | ⟨_, rfl⟩
          · change (counter before : ℝ≥0∞) ≤ counter after
            exact_mod_cast advance before after allowed
          · exact le_rfl

private theorem return_reward_mono {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    (initial : State) (payoff : Output → ℝ≥0∞) :
    ∀ᵐ run ∂execution next initial, Monotone (fun time => returnReward observe payoff (run time)) := by
  apply execution_observation_mono next initial (returnReward observe payoff)
  intro state
  cases state with
  | none => exact ae_of_all _ (fun _ => zero_le)
  | some current =>
      cases seen : observe current with
      | none => exact ae_of_all _ (fun after => by simp [returnReward, seen])
      | some output =>
          simp only [transition, halting current output seen, choiceLaw_halt, PMF.toMeasure_pure]
          exact (ae_dirac_iff MeasurableSet.of_discrete).2 le_rfl

private def completionCounter {State Output : Type*} (observe : State → Option Output)
    (counter : State → ℕ) (sample : SampleState State) : ℕ :=
  match sample with
  | none => 0
  | some state => if (observe state).isSome then counter state + 1 else 0

private theorem completion_counter_stable {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    (initial : State) (counter : State → ℕ) :
    ∀ᵐ run ∂execution next initial, ∀ time,
      completionCounter observe counter (run time) ≠ 0 →
      completionCounter observe counter (run (time + 1)) =
        completionCounter observe counter (run time) := by
  apply execution_relation next initial (fun before after =>
    completionCounter observe counter before ≠ 0 →
      completionCounter observe counter after = completionCounter observe counter before)
  · have measurable : MeasurableSet {pair : ℕ × ℕ | pair.1 ≠ 0 → pair.2 = pair.1} :=
      MeasurableSet.of_discrete
    exact measurable.preimage
      (((show Measurable (completionCounter observe counter) from Measurable.of_discrete).comp
          measurable_fst).prodMk
        ((show Measurable (completionCounter observe counter) from Measurable.of_discrete).comp
          measurable_snd))
  · intro sample
    cases sample with
    | none => exact ae_of_all _ (fun _ impossible => False.elim (impossible rfl))
    | some state =>
        cases seen : observe state with
        | none =>
            exact ae_of_all _ (fun _ impossible => False.elim (impossible (by
              simp [completionCounter, seen])))
        | some output =>
            simp only [transition, halting state output seen, choiceLaw_halt, PMF.toMeasure_pure]
            exact (ae_dirac_iff MeasurableSet.of_discrete).2 (fun _ => rfl)

private theorem completion_counter_later {State Output : Type*}
    (observe : State → Option Output) (counter : State → ℕ) (run : Run State)
    (stable : ∀ time, completionCounter observe counter (run time) ≠ 0 →
      completionCounter observe counter (run (time + 1)) = completionCounter observe counter (run time))
    {time later : ℕ} (bound : time ≤ later)
    (nonzero : completionCounter observe counter (run time) ≠ 0) :
    completionCounter observe counter (run later) = completionCounter observe counter (run time) := by
  induction later, bound using Nat.le_induction with
  | base => rfl
  | succ later _ ih => rw [stable later (by simpa [ih] using nonzero), ih]

private theorem total_at_completion {State Output : Type*}
    (observe : State → Option Output) (counter : State → ℕ) (run : Run State)
    (monotone : Monotone (fun time => extendedCounter counter (run time)))
    (stable : ∀ time, completionCounter observe counter (run time) ≠ 0 →
      completionCounter observe counter (run (time + 1)) = completionCounter observe counter (run time))
    (time : ℕ) (state : State) (output : Output)
    (atTime : run time = some state) (seen : observe state = some output) :
    (Observable.total counter).value run = (counter state : ℝ≥0∞) ∧
      ∀ other current value, run other = some current → observe current = some value →
        counter current = counter state := by
  have completed : completionCounter observe counter (run time) = counter state + 1 := by
    simp [completionCounter, atTime, seen]
  have nonzero : completionCounter observe counter (run time) ≠ 0 := by omega
  have later (other : ℕ) (bound : time ≤ other) :
      completionCounter observe counter (run other) = counter state + 1 :=
    (completion_counter_later observe counter run stable bound nonzero).trans completed
  constructor
  · apply le_antisymm
    · apply iSup_le
      intro other
      by_cases before : other ≤ time
      · have ordered := monotone before
        dsimp only at ordered
        rw [atTime] at ordered
        cases found : run other with
        | none => simp
        | some current => simpa [extendedCounter, found] using ordered
      · have finished := later other (Nat.le_of_not_ge before)
        cases found : run other with
        | none => simp [completionCounter, found] at finished
        | some current =>
            cases observed : observe current with
            | none => simp [completionCounter, found, observed] at finished
            | some result =>
                have same : counter current = counter state := by
                  simpa [completionCounter, found, observed] using finished
                simp [same]
    · exact le_iSup_of_le time (by simp [atTime])
  · intro other current value found observed
    by_cases before : other ≤ time
    · have current_nonzero : completionCounter observe counter (run other) ≠ 0 := by
        simp [completionCounter, found, observed]
      have equal := completion_counter_later observe counter run stable before current_nonzero
      simpa [completionCounter, atTime, seen, found, observed] using equal.symm
    · have equal := later other (Nat.le_of_not_ge before)
      simpa [completionCounter, found, observed] using equal

/-- Under almost-sure successful termination, every measurable nonnegative
    function of total charged cost agrees with its final-counter return reward.
    The local monotonicity premise concerns supported source transitions only;
    arbitrary sequences in the ambient path space need not be monotone. -/
theorem expected_total_eq_callExpected {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    (initial : State) (counter : State → ℕ) (finalCounter : Output → ℕ)
    (advance : ∀ before after, (next before).Allows after → counter before ≤ counter after)
    (agrees : ∀ state output, observe state = some output → counter state = finalCounter output)
    (terminates : callProbability next observe initial (fun _ => True) = 1)
    (reward : ℝ≥0∞ → ℝ≥0∞) (measurable : Measurable reward) :
    expected (execution next initial) ((Observable.total counter).map reward measurable) =
      callExpected next observe initial (fun output => reward (finalCounter output)) := by
  let payoff : Output → ℝ≥0∞ := fun output => reward (finalCounter output)
  have eventual : ∀ᵐ run ∂execution next initial,
      ∃ time state output, run time = some state ∧ observe state = some output := by
    have probability_one := terminates
    rw [callProbability_eq_execution next observe halting] at probability_one
    have occurs := (mem_ae_iff_prob_eq_one (Event.returnsWhere observe (fun _ => True)).measurable).2
      probability_one
    filter_upwards [occurs] with run occurs
    obtain ⟨time, state, output, found, seen, _⟩ := occurs
    exact ⟨time, state, output, found, seen⟩
  have same : ∀ᵐ run ∂execution next initial,
      reward ((Observable.total counter).value run) =
        ⨆ time : ℕ, returnReward observe payoff (run time) := by
    filter_upwards [eventual, counter_mono next initial counter advance,
      completion_counter_stable next observe halting initial counter]
      with run completed monotone stable
    obtain ⟨time, state, output, atTime, seen⟩ := completed
    obtain ⟨total, identical⟩ := total_at_completion observe counter run monotone stable
      time state output atTime seen
    rw [total]
    apply le_antisymm
    · exact le_iSup_of_le time (by simp [returnReward, atTime, seen, payoff, agrees state output seen])
    · apply iSup_le
      intro other
      cases found : run other with
      | none => exact zero_le
      | some current =>
          cases observed : observe current with
          | none => simp [returnReward, observed]
          | some value =>
              have equal := identical other current value found observed
              simp [returnReward, observed, payoff, ← agrees current value observed, equal]
  change (∫⁻ run, reward ((Observable.total counter).value run) ∂execution next initial) = _
  rw [lintegral_congr_ae same,
    lintegral_iSup' (f := fun (time : ℕ) (run : Run State) => returnReward observe payoff (run time))
      (fun time =>
      ((show Measurable (returnReward observe payoff) from Measurable.of_discrete).comp
        (measurable_pi_apply time)).aemeasurable)
      (return_reward_mono next observe halting initial payoff),
    callExpected_eq_iSup next observe halting initial]
  apply iSup_congr
  intro time
  exact expected_atTime next initial time (returnReward observe payoff)

/-- The total-runtime tail equals a property of the completed call when the
    call succeeds almost surely and its charged counter never decreases. -/
theorem costProbability_eq_callProbability {State Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (halting : ∀ state output, observe state = some output → next state = .halt)
    (initial : State) (counter : State → ℕ) (finalCounter : Output → ℕ)
    (advance : ∀ before after, (next before).Allows after → counter before ≤ counter after)
    (agrees : ∀ state output, observe state = some output → counter state = finalCounter output)
    (terminates : callProbability next observe initial (fun _ => True) = 1)
    (threshold : ℝ≥0∞) :
    costProbability (execution next initial) counter threshold =
      callProbability next observe initial (fun output => threshold < (finalCounter output : ℝ≥0∞)) := by
  classical
  let reward : ℝ≥0∞ → ℝ≥0∞ := Set.indicator {value | threshold < value} (fun _ => 1)
  have measurable : Measurable reward :=
    measurable_const.indicator (measurableSet_lt measurable_const measurable_id)
  have bridge := expected_total_eq_callExpected next observe halting initial counter
    finalCounter advance agrees terminates reward measurable
  have left : expected (execution next initial) ((Observable.total counter).map reward measurable) =
      costProbability (execution next initial) counter threshold := by
    change (∫⁻ run, reward ((Observable.total counter).value run) ∂execution next initial) = _
    have same : (fun run : Run State => reward ((Observable.total counter).value run)) =
        (Event.exceeds (Observable.total counter) threshold).states.indicator (fun _ => 1) := by
      funext run
      simp [reward, Set.indicator_apply, Event.exceeds]
    rw [same]
    exact lintegral_indicator_one (Event.exceeds (Observable.total counter) threshold).measurable
  rw [left] at bridge
  refine bridge.trans ?_
  unfold callProbability
  apply congrArg (callExpected next observe initial)
  funext output
  by_cases exceeded : threshold < (finalCounter output : ℝ≥0∞) <;>
    simp [reward, exceeded]

end Algo2LeanProbability
