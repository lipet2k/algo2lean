import Algo2LeanProbability.Call

/-!
Linearity and tail sums for unconditional completed-call rewards. The formulas
allow unbounded nonnegative rewards and divergent calls: a run that does not
return contributes zero on both sides, without any termination assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable
open MeasureTheory
open scoped ENNReal

namespace Algo2LeanProbability
namespace Stopped

variable {State : Type*} [MeasurableSpace State] [DiscreteMeasurableSpace State]

@[simp] theorem expected_zero (step : State → PMF State) (boundary : State → Prop)
    (initial : State) : expected step boundary (fun _ => 0) initial = 0 := by
  apply le_antisymm _ bot_le
  exact expected_le step boundary (fun _ => 0) (fun _ => 0)
    (by simp) (by simp) initial

/-- Nonnegative completed rewards add, including when either expectation is infinite. -/
theorem expected_add (step : State → PMF State) (boundary : State → Prop)
    (first second : State → ℝ≥0∞) (initial : State) :
    expected step boundary (fun state => first state + second state) initial =
      expected step boundary first initial + expected step boundary second initial := by
  have finite : ∀ time state,
      within step boundary (fun state => first state + second state) time state =
        within step boundary first time state + within step boundary second time state := by
    intro time
    induction time with
    | zero => intro state; by_cases stop : boundary state <;> simp [within, stop]
    | succ time ih =>
        intro state
        by_cases stop : boundary state
        · simp [within, stop]
        · simp only [within, stop, ↓reduceIte, ih]
          exact lintegral_add_left Measurable.of_discrete _
  simp only [expected, finite]
  exact (ENNReal.iSup_add_iSup_of_monotone
    (fun _ _ bound => within_mono_time step boundary first bound initial)
    (fun _ _ bound => within_mono_time step boundary second bound initial)).symm

theorem expected_finset_sum {Index : Type*} (step : State → PMF State) (boundary : State → Prop)
    (indices : Finset Index) (reward : Index → State → ℝ≥0∞) (initial : State) :
    expected step boundary (fun state => ∑ index ∈ indices, reward index state) initial =
      ∑ index ∈ indices, expected step boundary (reward index) initial := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices absent ih =>
      simp only [Finset.sum_insert absent]
      rw [expected_add, ih]

/-- Countable sums of nonnegative completed rewards can be evaluated termwise. -/
theorem expected_tsum {Index : Type*} [Countable Index]
    (step : State → PMF State) (boundary : State → Prop)
    (reward : Index → State → ℝ≥0∞) (initial : State) :
    expected step boundary (fun state => ∑' index, reward index state) initial =
      ∑' index, expected step boundary (reward index) initial := by
  apply le_antisymm
  · apply expected_le step boundary _ (fun state => ∑' index, expected step boundary (reward index) state)
    · intro state stop
      simp only [expected_boundary step boundary _ state stop]
      exact le_rfl
    · intro state outside
      rw [lintegral_tsum (fun _ => Measurable.of_discrete.aemeasurable)]
      apply le_of_eq
      apply tsum_congr
      intro index
      rw [expected_unfold step boundary (reward index) state, if_neg outside]
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro indices
    rw [← expected_finset_sum]
    exact expected_mono step boundary (fun _ => ENNReal.sum_le_tsum indices) initial

end Stopped

variable {State Output : Type*}

theorem callExpected_add (next : State → Algo2LeanCore.Choice State)
    (observe : State → Option Output) (initial : State) (first second : Output → ℝ≥0∞) :
    callExpected next observe initial (fun value => first value + second value) =
      callExpected next observe initial first + callExpected next observe initial second := by
  have rewards : returnReward observe (fun value => first value + second value) =
      fun state => returnReward observe first state + returnReward observe second state := by
    funext state
    cases state with
    | none => simp [returnReward]
    | some current => cases seen : observe current <;> simp [returnReward, seen]
  simp only [callExpected, rewards]
  exact Stopped.expected_add _ _ _ _ _

theorem callExpected_tsum {Index : Type*} [Countable Index]
    (next : State → Algo2LeanCore.Choice State) (observe : State → Option Output)
    (initial : State) (reward : Index → Output → ℝ≥0∞) :
    callExpected next observe initial (fun value => ∑' index, reward index value) =
      ∑' index, callExpected next observe initial (reward index) := by
  have rewards : returnReward observe (fun value => ∑' index, reward index value) =
      fun state => ∑' index, returnReward observe (reward index) state := by
    funext state
    cases state with
    | none => simp [returnReward]
    | some current => cases seen : observe current <;> simp [returnReward, seen]
  simp only [callExpected, rewards]
  exact Stopped.expected_tsum _ _ _ _

/-- A natural-valued completed output equals the sum of its strict tail
probabilities. The identity also holds for infinite means and partial calls. -/
theorem callExpected_nat_tail_sum (next : State → Algo2LeanCore.Choice State)
    (observe : State → Option Output) (initial : State) (value : Output → Nat) :
    callExpected next observe initial (fun result => (value result : ℝ≥0∞)) =
      ∑' threshold : Nat, callExpected next observe initial
        (fun result => if threshold < value result then 1 else 0) := by
  have count : ∀ size : Nat, (size : ℝ≥0∞) = ∑' threshold : Nat,
      if threshold < size then (1 : ℝ≥0∞) else 0 := by
    intro size
    rw [tsum_eq_sum (s := Finset.range size) (fun threshold outside => by
      simp only [Finset.mem_range] at outside
      simp [outside])]
    symm
    calc
      _ = ∑ _threshold ∈ Finset.range size, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro threshold member
        exact if_pos (Finset.mem_range.mp member)
      _ = _ := by simp
  conv_lhs => arg 4; ext result; rw [count]
  exact callExpected_tsum next observe initial _

end Algo2LeanProbability

namespace Algo2LeanProbability

/-- A constant reward has its stated value under any complete discrete law. -/
@[simp] theorem pmfExpected_const {Output : Type*} (law : PMF Output) (constant : ℝ≥0∞) :
    pmfExpected law (fun _ => constant) = constant := by
  unfold pmfExpected
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Nonnegative rewards add, including when either expectation is infinite. -/
theorem pmfExpected_add {Output : Type*} (law : PMF Output) (first second : Output → ℝ≥0∞) :
    pmfExpected law (fun output => first output + second output) =
      pmfExpected law first + pmfExpected law second := by
  unfold pmfExpected
  simp_rw [mul_add]
  rw [ENNReal.tsum_add]

/-- A nonnegative weight factors out of a discrete expectation. -/
theorem pmfExpected_mul {Output : Type*} (law : PMF Output)
    (weight : ℝ≥0∞) (payoff : Output → ℝ≥0∞) :
    pmfExpected law (fun output => weight * payoff output) = weight * pmfExpected law payoff := by
  unfold pmfExpected
  simp_rw [← mul_assoc, mul_comm _ weight, mul_assoc]
  rw [ENNReal.tsum_mul_left]

/-- A reward bound is needed only for outcomes that can occur. This allows
callee invariants to bound a caller's continuation without assumptions on
impossible heaps or outputs. -/
theorem pmfExpected_mono_support {Output : Type*} (law : PMF Output)
    (first second : Output → ℝ≥0∞)
    (bound : ∀ output ∈ law.support, first output ≤ second output) :
    pmfExpected law first ≤ pmfExpected law second := by
  unfold pmfExpected
  apply ENNReal.tsum_le_tsum
  intro output
  by_cases possible : output ∈ law.support
  · have inequality := bound output possible
    gcongr
  · rw [(PMF.apply_eq_zero_iff _ _).2 possible]
    simp

/-- A property of every possible joint return holds with probability one.
The complete call law already includes almost-sure termination. -/
theorem HasLaw.probability_one {State Output : Type*}
    {next : State → Algo2LeanCore.Choice State} {observe : State → Option Output}
    {initial : State} {law : PMF Output} (contract : HasLaw next observe initial law)
    (post : Output → Prop) (holds : ∀ output ∈ law.support, post output) :
    callProbability next observe initial post = 1 := by
  rw [callProbability, contract]
  change pmfExpected law (fun output => if post output then 1 else 0) = 1
  calc
    _ = pmfExpected law (fun _ => 1) := by
      apply pmfExpected_congr_support
      intro output possible
      exact if_pos (holds output possible)
    _ = 1 := pmfExpected_const law 1

end Algo2LeanProbability
