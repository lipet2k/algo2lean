import Algo2LeanLib.Choice
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Order.Interval.Finset.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Probability laws for Algo2Lean's finite-choice instructions. A run is an infinite
sequence: successful termination repeats the final state, and failure enters
`none` permanently. This padding does not add source transitions or ticks.
The generated algorithm remains independent of Mathlib; importing this optional
module supplies probability and expectation on its executions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Algo2LeanProbability

universe u

/-- A configuration, or the absorbing error state. The discrete measurable
    structure permits arbitrary observations of one mathematical heap. -/
def SampleState (State : Type u) := Option State

instance (State : Type u) : MeasurableSpace (SampleState State) := ⊤
instance (State : Type u) : DiscreteMeasurableSpace (SampleState State) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Infinite executions include finite terminated executions padded at the end. -/
abbrev Run (State : Type u) := ℕ → SampleState State

/-- A genuinely uniform integer, including the lower bound and excluding the upper bound. -/
def uniformInt (lower upper : Int) (bounds : lower < upper) : PMF Int :=
  PMF.uniformOfFinset (Finset.Ico lower upper) ⟨lower, by simp [bounds]⟩

@[simp] theorem uniformInt_apply (lower upper value : Int) (bounds : lower < upper) :
    uniformInt lower upper bounds value =
      if lower ≤ value ∧ value < upper then
        ((Finset.Ico lower upper).card : ℝ≥0∞)⁻¹ else 0 := by
  simpa only [uniformInt, Finset.mem_Ico] using
    (PMF.uniformOfFinset_apply (s := Finset.Ico lower upper)
      ⟨lower, by simp [bounds]⟩ value)

@[simp] theorem uniformInt_support (lower upper value : Int) (bounds : lower < upper) :
    value ∈ (uniformInt lower upper bounds).support ↔ lower ≤ value ∧ value < upper := by
  simpa only [uniformInt, Finset.mem_Ico] using
    (PMF.mem_support_uniformOfFinset_iff (s := Finset.Ico lower upper)
      ⟨lower, by simp [bounds]⟩ value)

theorem uniformInt_mass (lower upper value : Int) (bounds : lower < upper)
    (lowerBound : lower ≤ value) (upperBound : value < upper) :
    uniformInt lower upper bounds value = ((upper - lower).toNat : ℝ≥0∞)⁻¹ := by
  simp [uniformInt_apply, lowerBound, upperBound]

/-- Compute a uniform draw's nonnegative expectation by a finite arithmetic sum. -/
theorem uniformInt_expected (lower upper : Int) (bounds : lower < upper)
    (value : Int → ℝ≥0∞) :
    (∫⁻ sample, value sample ∂(uniformInt lower upper bounds).toMeasure) =
      ∑ sample ∈ Finset.Ico lower upper,
        value sample * ((upper - lower).toNat : ℝ≥0∞)⁻¹ := by
  let samples := uniformInt lower upper bounds
  have support : samples.support = (Finset.Ico lower upper : Set Int) := by
    ext sample
    simpa only [Finset.mem_coe, Finset.mem_Ico] using
      uniformInt_support lower upper sample bounds
  calc
    (∫⁻ sample, value sample ∂samples.toMeasure) =
        ∫⁻ sample in Finset.Ico lower upper, value sample ∂samples.toMeasure := by
      rw [← support, PMF.restrict_toMeasure_support]
    _ = ∑ sample ∈ Finset.Ico lower upper, value sample * samples.toMeasure {sample} :=
      lintegral_finset _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sample member
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      rw [uniformInt_mass lower upper sample bounds (Finset.mem_Ico.mp member).1
        (Finset.mem_Ico.mp member).2]

/-- The probability law of one instruction. A failed interval is an error, not
    an arbitrary value. `halt` keeps the current successful final state. -/
def choiceLaw {State : Type u} (current : State) :
    Algo2LeanCore.Choice State → PMF (SampleState State)
  | .next after => PMF.pure (some after)
  | .uniform lower upper resume =>
      if bounds : lower < upper then
        (uniformInt lower upper bounds).map (fun value => some (resume value))
      else PMF.pure none
  | .halt => PMF.pure (some current)
  | .fail => PMF.pure none

@[simp] theorem choiceLaw_next {State : Type u} (current after : State) :
    choiceLaw current (.next after) = PMF.pure (some after) := rfl

@[simp] theorem choiceLaw_halt {State : Type u} (current : State) :
    choiceLaw current .halt = PMF.pure (some current) := rfl

@[simp] theorem choiceLaw_fail {State : Type u} (current : State) :
    choiceLaw current .fail = PMF.pure none := rfl

theorem choiceLaw_uniform {State : Type u} (current : State) (lower upper : Int)
    (resume : Int → State) (bounds : lower < upper) :
    choiceLaw current (.uniform lower upper resume) =
      (uniformInt lower upper bounds).map (fun value => some (resume value)) := by
  simp only [choiceLaw, dif_pos bounds]

/-- Possible source transitions are exactly the supported outcomes, except for
    the explicit absorbing padding of a successful halt. -/
theorem choiceLaw_support {State : Type u} (current after : State)
    (choice : Algo2LeanCore.Choice State) :
    some after ∈ (choiceLaw current choice).support ↔
      choice.Allows after ∨ choice = .halt ∧ after = current := by
  cases choice with
  | next state => simp [choiceLaw, Algo2LeanCore.Choice.Allows, eq_comm]
  | uniform lower upper resume =>
      by_cases bounds : lower < upper
      · rw [choiceLaw_uniform current lower upper resume bounds, PMF.mem_support_map_iff]
        simp only [uniformInt_support, Option.some.injEq, Algo2LeanCore.Choice.Allows,
          reduceCtorEq, false_and, or_false]
        constructor
        · rintro ⟨value, ⟨lowerBound, upperBound⟩, same⟩
          exact ⟨value, lowerBound, upperBound, same.symm⟩
        · rintro ⟨value, lowerBound, upperBound, same⟩
          exact ⟨value, ⟨lowerBound, upperBound⟩, same.symm⟩
      · have impossible : ¬ ∃ value, lower ≤ value ∧ value < upper ∧ after = resume value := by
          rintro ⟨value, lowerBound, upperBound, _⟩
          exact bounds (lt_of_le_of_lt lowerBound upperBound)
        simp [choiceLaw, bounds, Algo2LeanCore.Choice.Allows, impossible]
  | halt => simp [choiceLaw, Algo2LeanCore.Choice.Allows, eq_comm]
  | fail => simp [choiceLaw, Algo2LeanCore.Choice.Allows]

/-- Caller embeddings preserve the complete one-instruction distribution, not
    just its support. Coincident embedded outcomes have their masses added. -/
theorem choiceLaw_map {State : Type u} {Target : Type*} (embed : State → Target)
    (current : State) (choice : Algo2LeanCore.Choice State) :
    choiceLaw (embed current) (choice.map embed) =
      (choiceLaw current choice).map (Option.map embed) := by
  cases choice with
  | next state => simp [Algo2LeanCore.Choice.map, choiceLaw, PMF.pure_map]
  | uniform lower upper resume =>
      by_cases bounds : lower < upper
      · simp only [Algo2LeanCore.Choice.map, choiceLaw, dif_pos bounds, PMF.map_comp]
        rfl
      · simp [Algo2LeanCore.Choice.map, choiceLaw, bounds, PMF.pure_map]
  | halt => simp [Algo2LeanCore.Choice.map, choiceLaw, PMF.pure_map]
  | fail => simp [Algo2LeanCore.Choice.map, choiceLaw, PMF.pure_map]

/-- One probabilistic transition, with error made absorbing. -/
def transition {State : Type u} (next : State → Algo2LeanCore.Choice State) :
    SampleState State → PMF (SampleState State)
  | none => PMF.pure none
  | some state => choiceLaw state (next state)

def kernel {State : Type u} (next : State → Algo2LeanCore.Choice State) :
    Kernel (SampleState State) (SampleState State) where
  toFun state := (transition next state).toMeasure
  measurable' := Measurable.of_discrete

instance {State : Type u} (next : State → Algo2LeanCore.Choice State) :
    IsMarkovKernel (kernel next) := ⟨fun _ => by dsimp [kernel]; infer_instance⟩

/-- The next-state law depends on the current configuration. Earlier draws
    influence it only through that configuration, including the call stack. -/
def historyKernel {State : Type u} (next : State → Algo2LeanCore.Choice State) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → SampleState State) (SampleState State) :=
  (kernel next).comap (fun history => history ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n))

instance {State : Type u} (next : State → Algo2LeanCore.Choice State) (n : ℕ) :
    IsMarkovKernel (historyKernel next n) := by unfold historyKernel; infer_instance

/-- The complete execution law, constructed by Mathlib's Ionescu–Tulcea theorem.
    No countability assumption is imposed on heaps or continuations. -/
def execution {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) : Measure (Run State) :=
  Kernel.traj (X := fun _ => SampleState State) (historyKernel next) 0 (fun _ => some initial)

instance {State : Type u} (next : State → Algo2LeanCore.Choice State) (initial : State) :
    IsProbabilityMeasure (execution next initial) := by
  unfold execution
  exact IsMarkovKernel.isProbabilityMeasure
    (κ := Kernel.traj (X := fun _ => SampleState State) (historyKernel next) 0) _

/-- The law after a fixed number of instructions; this recursion is convenient
    for finite calculations and agrees with the full execution below. -/
def finiteKernel {State : Type u} (next : State → Algo2LeanCore.Choice State) :
    ℕ → Kernel (SampleState State) (SampleState State)
  | 0 => Kernel.id
  | n + 1 => (kernel next) ∘ₖ (finiteKernel next n)

instance {State : Type u} (next : State → Algo2LeanCore.Choice State) (n : ℕ) :
    IsMarkovKernel (finiteKernel next n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih => change IsMarkovKernel ((kernel next) ∘ₖ (finiteKernel next n)); infer_instance

def finiteLaw {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (time : ℕ) : Measure (SampleState State) :=
  finiteKernel next time (some initial)

@[simp] theorem finiteLaw_zero {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) : finiteLaw next initial 0 =
      @Measure.dirac (SampleState State) inferInstance (some initial) := rfl

@[simp] theorem finiteLaw_one {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) : finiteLaw next initial 1 = (choiceLaw initial (next initial)).toMeasure := by
  simp [finiteLaw, finiteKernel, Kernel.comp_id, kernel, transition]

/-- Finite-step probability propagates by the conditional next-state law. -/
theorem finiteLaw_succ {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (time : ℕ) (event : Set (SampleState State)) :
    finiteLaw next initial (time + 1) event =
      ∫⁻ state, (transition next state).toMeasure event ∂finiteLaw next initial time :=
  Kernel.comp_apply' _ _ _ MeasurableSet.of_discrete

private theorem pmf_lintegral {State : Type*} (p : PMF (SampleState State))
    (value : SampleState State → ℝ≥0∞) :
    (∫⁻ state, value state ∂p.toMeasure) = ∑' state, p state * value state := by
  have atomic : p.toMeasure = Measure.sum (fun state => p state • Measure.dirac state) := by
    ext event measurable
    rw [PMF.toMeasure_apply_eq_tsum, Measure.sum_apply _ measurable]
    apply tsum_congr
    intro state
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurable]
    by_cases member : state ∈ event <;> simp [member]
  rw [atomic, lintegral_sum_measure]
  apply tsum_congr
  intro state
  rw [lintegral_smul_measure, lintegral_dirac' _ Measurable.of_discrete]
  rfl

/-- Finite-step distributions can be calculated with ordinary probability-mass bind. -/
def finitePMF {State : Type*} (next : State → Algo2LeanCore.Choice State)
    (initial : State) : ℕ → PMF (SampleState State)
  | 0 => PMF.pure (some initial)
  | time + 1 => (finitePMF next initial time).bind (transition next)

theorem finiteLaw_eq_toMeasure {State : Type*} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (time : ℕ) :
    finiteLaw next initial time = (finitePMF next initial time).toMeasure := by
  induction time with
  | zero => rw [finiteLaw_zero, finitePMF, PMF.toMeasure_pure]
  | succ time ih =>
      ext event measurable
      rw [finiteLaw_succ, ih, pmf_lintegral]
      exact (PMF.toMeasure_bind_apply _ _ event measurable).symm


/-- Once every reachable state is absorbing, later state laws stay unchanged.
    This reduces eventual return calculations for bounded algorithms to a finite horizon. -/
theorem finiteLaw_stable {State : Type*} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (time : ℕ)
    (stopped : ∀ᵐ state ∂finiteLaw next initial time, transition next state = PMF.pure state)
    (extra : ℕ) : finiteLaw next initial (time + extra) = finiteLaw next initial time := by
  induction extra with
  | zero => simp
  | succ n ih =>
      ext event measurable
      rw [Nat.add_succ, finiteLaw_succ, ih]
      calc
        (∫⁻ state, (transition next state).toMeasure event ∂finiteLaw next initial time) =
            ∫⁻ state, event.indicator (fun _ => (1 : ℝ≥0∞)) state ∂finiteLaw next initial time := by
          apply lintegral_congr_ae
          filter_upwards [stopped] with state same
          rw [same, PMF.toMeasure_pure, Measure.dirac_apply' _ measurable]
          rfl
        _ = _ := lintegral_indicator_one measurable

private theorem partial_marginal {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (time : ℕ) :
    (Kernel.partialTraj (X := fun _ => SampleState State) (historyKernel next) 0 time).map
      (fun history => history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) =
    (finiteKernel next time).comap
      (fun history : (i : Finset.Iic 0) → SampleState State => history ⟨0, by simp⟩)
      (measurable_pi_apply _) := by
  induction time with
  | zero =>
      simp only [Kernel.partialTraj_self, finiteKernel]
      rw [← Kernel.deterministic_comp_eq_map (measurable_pi_apply _), Kernel.comp_id,
        ← Kernel.comp_deterministic_eq_comap, Kernel.id_comp]
  | succ time ih =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le time), Kernel.map_comp,
        Kernel.map_partialTraj_succ_self]
      change (kernel next).comap _ _ ∘ₖ _ = _
      rw [← Kernel.comp_map, ih]
      simp only [finiteKernel, ← Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc]

/-- Full-path and finite-step reasoning describe exactly the same experiment. -/
theorem execution_marginal {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (time : ℕ) :
    (execution next initial).map (fun run => run time) = finiteLaw next initial time := by
  have finite := partial_marginal next time
  have projection := Kernel.traj_map_frestrictLe (X := fun _ => SampleState State)
    (κ := historyKernel next) 0 time
  have mapped := congrArg
    (fun k => k.map (fun history => history ⟨time, Finset.mem_Iic.mpr le_rfl⟩)) projection
  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop), finite] at mapped
  have applied := congrArg (fun k => k (fun _ => some initial)) mapped
  change ((Kernel.traj (X := fun _ => SampleState State) (historyKernel next) 0).map
    (fun run => run time)) (fun _ => some initial) = finiteLaw next initial time at applied
  rw [Kernel.map_apply _ (measurable_pi_apply time)] at applied
  exact applied

private theorem traj_current {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (time : ℕ) (history : (i : Finset.Iic time) → SampleState State) :
    ((Kernel.traj (X := fun _ => SampleState State) (historyKernel next) time) history).map
      (fun run => run time) =
        @Measure.dirac (SampleState State) inferInstance (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) := by
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

/-- A property preserved with probability one by each local instruction is
    preserved at every adjacent time of almost every complete execution. -/
theorem execution_preserves {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (property : SampleState State → Prop)
    (preserve : ∀ state, property state →
      ∀ᵐ after ∂(transition next state).toMeasure, property after) :
    ∀ᵐ run ∂execution next initial, ∀ time, property (run time) → property (run (time + 1)) := by
  apply (ae_all_iff).2
  intro time
  let trajectories := Kernel.traj (X := fun _ => SampleState State) (historyKernel next) time
  have locally : ∀ history, ∀ᵐ run ∂trajectories history,
      property (run time) → property (run (time + 1)) := by
    intro history
    have current : ∀ᵐ run ∂trajectories history,
        run time = history ⟨time, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply ae_of_ae_map (μ := trajectories history)
        (f := fun run : Run State => run time)
        (p := fun state => state = history ⟨time, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply time).aemeasurable
      rw [traj_current next time history]
      exact (ae_dirac_iff MeasurableSet.of_discrete).2 rfl
    by_cases holds : property (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩)
    · have future : ∀ᵐ run ∂trajectories history, property (run (time + 1)) := by
        apply ae_of_ae_map (μ := trajectories history)
          (f := fun run : Run State => run (time + 1)) (p := property)
          (measurable_pi_apply (time + 1)).aemeasurable
        have projection := Kernel.map_traj_succ_self (X := fun _ => SampleState State)
          (κ := historyKernel next) (a := time)
        have applied := congrArg (fun k => k history) projection
        rw [Kernel.map_apply _ (measurable_pi_apply (time + 1))] at applied
        rw [applied]
        exact preserve _ holds
      filter_upwards [future] with run done using fun _ => done
    · filter_upwards [current] with run same
      simpa only [same] using fun impossible => False.elim (holds impossible)
  have measurable : MeasurableSet {run : Run State |
      property (run time) → property (run (time + 1))} := by
    have first : MeasurableSet {run : Run State | property (run time)} :=
      (show Measurable (fun run : Run State => run time) from measurable_pi_apply time)
        MeasurableSet.of_discrete
    have second : MeasurableSet {run : Run State | property (run (time + 1))} :=
      (show Measurable (fun run : Run State => run (time + 1)) from measurable_pi_apply (time + 1))
        MeasurableSet.of_discrete
    convert first.compl.union second using 1
    ext run
    simp [imp_iff_not_or]
  have composed := Kernel.ae_comp_of_ae_ae
    (κ := Kernel.partialTraj (X := fun _ => SampleState State) (historyKernel next) 0 time)
    (η := trajectories) (a := fun _ => some initial) measurable (ae_of_all _ locally)
  simpa only [trajectories, Kernel.traj_comp_partialTraj (Nat.zero_le time), execution] using composed

/-- A user event carries the measurability required for its probability. -/
structure Event (State : Type u) where
  states : Set (Run State)
  measurable : MeasurableSet states

namespace Event

variable {State : Type u}

/-- Any predicate of the configuration at one fixed time is an event. -/
def atTime (time : ℕ) (property : SampleState State → Prop) : Event State where
  states := {run | property (run time)}
  measurable := (MeasurableSet.of_discrete (s := {state | property state})).preimage
    (measurable_pi_apply time)

/-- Eventually the run satisfies a local predicate, including on a diverging run. -/
def ever (property : SampleState State → Prop) : Event State where
  states := {run | ∃ time, property (run time)}
  measurable := by
    simpa only [atTime, Set.ofPred_exists] using
      (MeasurableSet.iUnion fun time => (atTime time property).measurable)

/-- Every configuration satisfies a local predicate. -/
def always (property : SampleState State → Prop) : Event State where
  states := {run | ∀ time, property (run time)}
  measurable := by
    simpa only [atTime, Set.ofPred_forall] using
      (MeasurableSet.iInter fun time => (atTime time property).measurable)

/-- A local event has occurred by the supplied finite time bound. -/
def within (steps : ℕ) (property : SampleState State → Prop) : Event State where
  states := {run | ∃ time, time ≤ steps ∧ property (run time)}
  measurable := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro time
    by_cases bound : time ≤ steps
    · simpa only [bound, true_and, atTime] using (atTime time property).measurable
    · simp [bound]

def and (first second : Event State) : Event State :=
  ⟨first.states ∩ second.states, first.measurable.inter second.measurable⟩

def or (first second : Event State) : Event State :=
  ⟨first.states ∪ second.states, first.measurable.union second.measurable⟩

def not (event : Event State) : Event State := ⟨event.statesᶜ, event.measurable.compl⟩

/-- A return observer is supplied by the generated function interface and is
    `some` precisely at successful top-level returns of that function. -/
def returns {Output : Type*} (observe : State → Option Output) (output : Output) : Event State :=
  ever fun state => ∃ current, state = some current ∧ observe current = some output

/-- Return properties may refer jointly to the final heap and output. -/
def returnsWhere {Output : Type*} (observe : State → Option Output)
    (post : Output → Prop) : Event State :=
  ever fun state => ∃ current output,
    state = some current ∧ observe current = some output ∧ post output

def failure : Event State := ever fun state => state = none

end Event

def probability {State : Type u} (law : Measure (Run State)) (event : Event State) : ℝ≥0∞ :=
  law event.states

theorem probability_atTime {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (time : ℕ) (property : SampleState State → Prop) :
    probability (execution next initial) (Event.atTime time property) =
      finiteLaw next initial time {state | property state} := by
  rw [← execution_marginal next initial time,
    Measure.map_apply (measurable_pi_apply time) MeasurableSet.of_discrete]
  rfl

/-- Eventual success is the increasing limit of bounded-time success. No
    assumption of termination, or conditioning on success, enters this identity. -/
theorem probability_ever {State : Type u} (law : Measure (Run State))
    (property : SampleState State → Prop) :
    probability law (Event.ever property) =
      ⨆ steps : ℕ, probability law (Event.within steps property) := by
  have increasing : Monotone (fun steps => (Event.within steps property).states) := by
    intro first second bound run occurs
    obtain ⟨time, before, holds⟩ := occurs
    exact ⟨time, le_trans before bound, holds⟩
  have union : (Event.ever property).states = ⋃ steps, (Event.within steps property).states := by
    ext run
    simp only [Event.ever, Event.within, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨time, holds⟩
      exact ⟨time, time, le_rfl, holds⟩
    · rintro ⟨steps, time, _, holds⟩
      exact ⟨time, holds⟩
  exact (congrArg law union).trans increasing.measure_iUnion

/-- For a locally preserved property, eventual probability is the supremum of
    its probabilities in the finite state laws. Successful return predicates
    satisfy the premise because successful final states are absorbing. -/
theorem probability_ever_of_preserved {State : Type u}
    (next : State → Algo2LeanCore.Choice State) (initial : State)
    (property : SampleState State → Prop)
    (preserve : ∀ state, property state →
      ∀ᵐ after ∂(transition next state).toMeasure, property after) :
    probability (execution next initial) (Event.ever property) =
      ⨆ time : ℕ, finiteLaw next initial time {state | property state} := by
  have preserved := execution_preserves next initial property preserve
  have bounded (steps : ℕ) :
      probability (execution next initial) (Event.within steps property) =
        probability (execution next initial) (Event.atTime steps property) := by
    apply measure_congr
    filter_upwards [preserved] with run follows
    apply propext
    change (∃ time, time ≤ steps ∧ property (run time)) ↔ property (run steps)
    constructor
    · rintro ⟨time, bound, holds⟩
      induction steps, bound using Nat.le_induction with
      | base => exact holds
      | succ n _ ih => exact follows n ih
    · intro holds
      exact ⟨steps, le_rfl, holds⟩
  rw [probability_ever]
  congr 1
  funext time
  rw [bounded, probability_atTime]

theorem probability_ever_eq_of_finite_bound {State : Type u}
    (next : State → Algo2LeanCore.Choice State) (initial : State)
    (property : SampleState State → Prop)
    (preserve : ∀ state, property state →
      ∀ᵐ after ∂(transition next state).toMeasure, property after)
    (value : ℝ≥0∞) (bound : ∀ time, finiteLaw next initial time {state | property state} ≤ value)
    (time : ℕ) (attained : finiteLaw next initial time {state | property state} = value) :
    probability (execution next initial) (Event.ever property) = value := by
  rw [probability_ever_of_preserved next initial property preserve]
  apply le_antisymm (iSup_le (f := fun n =>
    finiteLaw next initial n {state | property state}) bound)
  rw [← attained]
  exact le_iSup (fun n => finiteLaw next initial n {state | property state}) time

/-- Probabilities of locally preserved predicates increase with time. -/
theorem finiteLaw_monotone_of_preserved {State : Type*}
    (next : State → Algo2LeanCore.Choice State) (initial : State)
    (property : SampleState State → Prop)
    (preserve : ∀ state, property state →
      ∀ᵐ after ∂(transition next state).toMeasure, property after) :
    Monotone (fun time => finiteLaw next initial time {state | property state}) := by
  intro earlier later bound
  dsimp only
  rw [← probability_atTime, ← probability_atTime]
  apply measure_mono_ae
  filter_upwards [execution_preserves next initial property preserve] with run follows
  intro holds
  change property (run later)
  change property (run earlier) at holds
  induction later, bound using Nat.le_induction with
  | base => exact holds
  | succ n _ ih => exact follows n ih

theorem probability_ever_of_stopped {State : Type*}
    (next : State → Algo2LeanCore.Choice State) (initial : State)
    (property : SampleState State → Prop)
    (preserve : ∀ state, property state →
      ∀ᵐ after ∂(transition next state).toMeasure, property after)
    (time : ℕ)
    (stopped : ∀ᵐ state ∂finiteLaw next initial time, transition next state = PMF.pure state) :
    probability (execution next initial) (Event.ever property) =
      finiteLaw next initial time {state | property state} := by
  apply probability_ever_eq_of_finite_bound next initial property preserve
  · intro other
    by_cases bound : other ≤ time
    · exact finiteLaw_monotone_of_preserved next initial property preserve bound
    · have later : time ≤ other := Nat.le_of_not_ge bound
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le later
      rw [finiteLaw_stable next initial time stopped extra]
  · rfl

/-- Unconditional return probability; nontermination is not discarded by
    renormalizing the probabilities of successful outputs. -/
def returnProbability {State : Type u} {Output : Type*}
    (next : State → Algo2LeanCore.Choice State) (initial : State)
    (observe : State → Option Output) (output : Output) : ℝ≥0∞ :=
  probability (execution next initial) (Event.returns observe output)

/-- An arbitrary measurable, nonnegative observation of an entire run. -/
structure Observable (State : Type u) where
  value : Run State → ℝ≥0∞
  measurable : Measurable value

namespace Observable

variable {State : Type u}

def atTime (time : ℕ) (value : SampleState State → ℝ≥0∞) : Observable State :=
  ⟨fun run => value (run time), Measurable.of_discrete.comp (measurable_pi_apply time)⟩

def add (first second : Observable State) : Observable State :=
  ⟨fun run => first.value run + second.value run, first.measurable.add second.measurable⟩

/-- The supremum of a nonnegative counter across all finite prefixes. For a
    monotone tick counter this is its total cost, including infinite runs. -/
def total (value : State → ℕ) : Observable State where
  value run := ⨆ time : ℕ, ((match run time with | none => 0 | some state => value state) : ℝ≥0∞)
  measurable := Measurable.iSup fun time =>
    (atTime time (fun state => ((match state with | none => 0 | some current => value current) : ℝ≥0∞))).measurable

end Observable

/-- Nonnegative expectation is always defined and may be infinite. -/
def expected {State : Type u} (law : Measure (Run State)) (observation : Observable State) : ℝ≥0∞ :=
  ∫⁻ run, observation.value run ∂law

theorem expected_add {State : Type u} (law : Measure (Run State))
    (first second : Observable State) :
    expected law (first.add second) = expected law first + expected law second :=
  lintegral_add_left first.measurable second.value

theorem expected_mono {State : Type u} (law : Measure (Run State))
    (first second : Observable State) (bound : ∀ run, first.value run ≤ second.value run) :
    expected law first ≤ expected law second := lintegral_mono bound

theorem expected_atTime {State : Type u} (next : State → Algo2LeanCore.Choice State)
    (initial : State) (time : ℕ) (value : SampleState State → ℝ≥0∞) :
    expected (execution next initial) (Observable.atTime time value) =
      ∫⁻ state, value state ∂finiteLaw next initial time := by
  rw [← execution_marginal next initial time,
    lintegral_map Measurable.of_discrete (measurable_pi_apply time)]
  rfl

/-- Signed real expectation requires integrability; it cannot silently use
    Lean's default integral value for a nonintegrable quantity. -/
def expectedReal {State : Type u} (law : Measure (Run State)) (value : Run State → ℝ)
    (_integrable : Integrable value law) : ℝ := ∫ run, value run ∂law

end Algo2LeanProbability
