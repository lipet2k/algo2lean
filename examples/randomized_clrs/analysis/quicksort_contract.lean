import Algo.quicksort.Points
import Algo.quicksort.Probability
import Algo.partition.Analysis
import Algo.quicksort_model.Analysis
import Algo2LeanProbability.CallContext

/-!
Quicksort composes the imported randomized-partition law with two recursive
calls. Helpers at the named recursive-call sites describe their continuations;
only the helper implementations inspect generated local states.
-/

noncomputable section
namespace QuicksortAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis
open Algo.quicksort Algo.quicksort.Algo2LeanGenerated
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local macro "advanceSort" : tactic =>
  `(tactic| rw [callExpected_next nextChoice randomized_quicksort.outcome _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; split <;> simp_all <;> rfl))])

/-- At the right-recursion line, its completed call is all remaining work. -/
theorem right_expected (state : Configuration) (ref : SeqRef) (pivot hi : Int)
    (law : PMF Heap) (reward : Heap → Unit → ℝ≥0∞)
    (location : randomized_quicksort.At.right state)
    (readRef : randomized_quicksort.Local.a state = some ref)
    (readPivot : randomized_quicksort.Local.pivot state = some pivot)
    (readHi : randomized_quicksort.Local.hi state = some hi)
    (valid : ref < state.heap.nextRef)
    (complete : ∀ payoff, randomized_quicksort.expectedReturn state.heap (ref, pivot + 1, hi) payoff =
      pmfExpected law (fun final => payoff final ())) :
    randomized_quicksort.expectedFrom state reward = pmfExpected law (fun final => reward final ()) := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have recursive_in_caller (heap : Heap) (ref : SeqRef) (lo hi : Int)
      (resume : Result → Frame) (valid : ref < heap.nextRef) (reward : Heap × Unit → ℝ≥0∞) :
      callExpected nextChoice randomized_quicksort.outcome
        (.active heap (entry_randomized_quicksort (ref, lo, hi)) [resume]) reward =
      randomized_quicksort.expectedReturn heap (ref, lo, hi)
        (fun final output => callExpected nextChoice randomized_quicksort.outcome
          (.active final (resume (.fn_randomized_quicksort output)) []) reward) := by
    have reuse := callExpected_with_stack nextChoice randomized_quicksort.outcome randomized_quicksort.outcome
      nextChoice_context (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      heap (entry_randomized_quicksort (ref, lo, hi)) resume [] reward
      (fun output => callExpected nextChoice randomized_quicksort.outcome
        (.active output.1 (resume (.fn_randomized_quicksort output.2)) []) reward)
      (by intro final result; cases result; rfl)
    simpa only [randomized_quicksort.expectedReturn, randomized_quicksort.ValidInput,
      if_pos valid, randomized_quicksort.initial, start, entry_randomized_quicksort] using reuse
  cases state with
  | done => cases location
  | active heap frame stack =>
      cases frame <;> try cases location
      case fn_randomized_quicksort pc s =>
        have counter : pc = 6 := by
          unfold randomized_quicksort.At.right at location
          split at location <;> simp_all
        subst pc
        change ref < heap.nextRef at valid
        simp [randomized_quicksort.Local.a, randomized_quicksort.Local.pivot,
          randomized_quicksort.Local.hi] at readRef readPivot readHi
        simp only [randomized_quicksort.expectedFrom]
        advanceSort
        advanceSort
        advanceSort
        advanceSort
        have reuse := recursive_in_caller heap ref (pivot + 1) hi
          (fun value => match value with
            | .fn_randomized_quicksort result => .fn_randomized_quicksort 2 {s with t6 := result, t7 := ref, t8 := pivot + 1, t9 := hi})
          valid (fun result => reward result.1 result.2)
        simp only [readRef, readPivot, readHi, entry_randomized_quicksort] at reuse ⊢
        trans randomized_quicksort.expectedReturn heap (ref, pivot + 1, hi)
          (fun final output => callExpected nextChoice randomized_quicksort.outcome
            (.active final (.fn_randomized_quicksort 2 {s with v0 := ref, v2 := hi, v3 := pivot, t6 := output, t7 := ref, t8 := pivot + 1, t9 := hi}) [])
            (fun result => reward result.1 result.2))
        · convert reuse using 1
        simp only [Config.heap] at complete
        rw [complete]
        apply congrArg (pmfExpected law)
        funext final
        advanceSort
        advanceSort
        rw [callExpected_return nextChoice randomized_quicksort.outcome _ _ rfl]

/-- At the left-recursion line, sequential composition passes the actual left
output heap to the right call, preserving their dependencies and counter effects. -/
theorem left_expected (state : Configuration) (ref : SeqRef) (lo pivot hi : Int)
    (leftLaw : PMF Heap) (rightLaw : Heap → PMF Heap) (reward : Heap → Unit → ℝ≥0∞)
    (location : randomized_quicksort.At.left state)
    (readRef : randomized_quicksort.Local.a state = some ref)
    (readLo : randomized_quicksort.Local.lo state = some lo)
    (readPivot : randomized_quicksort.Local.pivot state = some pivot)
    (readHi : randomized_quicksort.Local.hi state = some hi)
    (valid : ref < state.heap.nextRef)
    (validLeft : ∀ left ∈ leftLaw.support, ref < left.nextRef)
    (completeLeft : ∀ payoff, randomized_quicksort.expectedReturn state.heap (ref, lo, pivot) payoff =
      pmfExpected leftLaw (fun final => payoff final ()))
    (completeRight : ∀ left ∈ leftLaw.support, ∀ payoff,
      randomized_quicksort.expectedReturn left (ref, pivot + 1, hi) payoff =
        pmfExpected (rightLaw left) (fun final => payoff final ())) :
    randomized_quicksort.expectedFrom state reward =
      pmfExpected (leftLaw.bind rightLaw) (fun final => reward final ()) := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have recursive_in_caller (heap : Heap) (ref : SeqRef) (lo hi : Int)
      (resume : Result → Frame) (valid : ref < heap.nextRef) (reward : Heap × Unit → ℝ≥0∞) :
      callExpected nextChoice randomized_quicksort.outcome
        (.active heap (entry_randomized_quicksort (ref, lo, hi)) [resume]) reward =
      randomized_quicksort.expectedReturn heap (ref, lo, hi)
        (fun final output => callExpected nextChoice randomized_quicksort.outcome
          (.active final (resume (.fn_randomized_quicksort output)) []) reward) := by
    have reuse := callExpected_with_stack nextChoice randomized_quicksort.outcome randomized_quicksort.outcome
      nextChoice_context (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      heap (entry_randomized_quicksort (ref, lo, hi)) resume [] reward
      (fun output => callExpected nextChoice randomized_quicksort.outcome
        (.active output.1 (resume (.fn_randomized_quicksort output.2)) []) reward)
      (by intro final result; cases result; rfl)
    simpa only [randomized_quicksort.expectedReturn, randomized_quicksort.ValidInput,
      if_pos valid, randomized_quicksort.initial, start, entry_randomized_quicksort] using reuse
  cases state with
  | done => cases location
  | active heap frame stack =>
      cases frame <;> try cases location
      case fn_randomized_quicksort pc s =>
        have counter : pc = 10 := by
          unfold randomized_quicksort.At.left at location
          split at location <;> simp_all
        subst pc
        change ref < heap.nextRef at valid
        simp [randomized_quicksort.Local.a, randomized_quicksort.Local.lo,
          randomized_quicksort.Local.pivot, randomized_quicksort.Local.hi]
          at readRef readLo readPivot readHi
        simp only [randomized_quicksort.expectedFrom]
        advanceSort
        advanceSort
        advanceSort
        advanceSort
        have reuse := recursive_in_caller heap ref lo pivot
          (fun value => match value with
            | .fn_randomized_quicksort result => .fn_randomized_quicksort 6 {s with t10 := result, t11 := ref, t12 := lo, t13 := pivot})
          valid (fun result => reward result.1 result.2)
        simp only [readRef, readLo, readPivot, readHi, entry_randomized_quicksort] at reuse ⊢
        trans randomized_quicksort.expectedReturn heap (ref, lo, pivot)
          (fun final output => callExpected nextChoice randomized_quicksort.outcome
            (.active final (.fn_randomized_quicksort 6
              {s with v0 := ref, v1 := lo, v2 := hi, v3 := pivot, t10 := output, t11 := ref, t12 := lo, t13 := pivot}) [])
            (fun result => reward result.1 result.2))
        · convert reuse using 1
        simp only [Config.heap] at completeLeft
        rw [completeLeft, pmfExpected_bind]
        apply pmfExpected_congr_support
        intro left possible
        have continuation := right_expected
          (.active left (.fn_randomized_quicksort 6
            {s with v0 := ref, v1 := lo, v2 := hi, v3 := pivot, t10 := (), t11 := ref, t12 := lo, t13 := pivot}) [])
          ref pivot hi (rightLaw left) reward True.intro rfl rfl rfl
          (validLeft left possible) (completeRight left possible)
        simpa only [randomized_quicksort.expectedFrom, Config.heap] using continuation

/-- The generated algorithm realizes its finite recursive heap law whenever the
depth bound is at least the input interval length. -/
theorem expected_return (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (enough : (hi - lo).toNat ≤ fuel)
    (reward : Heap → Unit → ℝ≥0∞) :
    randomized_quicksort.expectedReturn heap (ref, lo, hi) reward =
      pmfExpected (quicksortLaw fuel heap ref lo hi) (fun final => reward final ()) := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have partition_in_caller (heap : Heap) (ref : SeqRef) (lo hi : Int)
      (locals : State_randomized_quicksort) (valid : ref < heap.nextRef) (nonempty : lo < hi)
      (reward : Heap × Unit → ℝ≥0∞) :
      callExpected nextChoice randomized_quicksort.outcome
        (.active heap (.import_0 (Algo.partition.entry_randomized_partition (ref, lo, hi)) []
          (fun result => match result with
            | .fn_randomized_partition value => .fn_randomized_quicksort 11 {locals with t14 := value}
            | _ => .invalid)) []) reward =
        pmfExpected (randomizedPartitionLaw heap ref lo hi nonempty)
          (fun result => callExpected nextChoice randomized_quicksort.outcome
            (.active result.1 (.fn_randomized_quicksort 11 {locals with t14 := result.2}) []) reward) := by
    let insidePartition : Frame → Bool
      | .import_0 _ _ _ => true
      | _ => false
    let resume : Algo.partition.Algo2LeanGenerated.Result → Frame := fun result => match result with
      | .fn_randomized_partition value => .fn_randomized_quicksort 11 {locals with t14 := value}
      | _ => .invalid
    let payoff : Heap × Int → ℝ≥0∞ := fun result => callExpected nextChoice randomized_quicksort.outcome
      (.active result.1 (.fn_randomized_quicksort 11 {locals with t14 := result.2}) []) reward
    have reuse := callExpected_import Algo.partition.Algo2LeanGenerated.nextChoice nextChoice
      Algo.partition.randomized_partition.outcome randomized_quicksort.outcome
      Frame.import_0 insidePartition resume []
      (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ => rfl) (by intro result; cases result <;> rfl)
      heap (Algo.partition.entry_randomized_partition (ref, lo, hi)) reward payoff
      (by
        intro final result
        cases result with
        | fn_partition => exact callExpected_fail _ _ _ rfl rfl _
        | fn_randomized_partition => rfl)
    apply reuse.trans
    have contract := randomized_partition_law heap ref lo hi valid nonempty payoff
    simpa only [Algo.partition.randomized_partition.ValidInput, if_pos valid,
      Algo.partition.randomized_partition.initial, start, Algo.partition.entry_randomized_partition, pmfExpected, payoff] using contract
  induction fuel generalizing heap lo hi reward with
  | zero =>
      have small : ¬ 1 < hi - lo := by omega
      have decision : decide (1 < hi - lo) = false := by simp [small]
      simp only [randomized_quicksort.expectedReturn, randomized_quicksort.ValidInput,
        valid, ↓reduceIte, randomized_quicksort.initial, start]
      advanceSort
      advanceSort
      simp only [decision]
      advanceSort
      advanceSort
      advanceSort
      rw [callExpected_return nextChoice randomized_quicksort.outcome _ _ rfl]
      simp [quicksortLaw]
  | succ fuel ih =>
      simp only [randomized_quicksort.expectedReturn, randomized_quicksort.ValidInput,
        valid, ↓reduceIte, randomized_quicksort.initial, start]
      advanceSort
      advanceSort
      by_cases large : 1 < hi - lo
      · have decision : decide (1 < hi - lo) = true := by simp [large]
        simp only [decision]
        advanceSort
        advanceSort
        advanceSort
        advanceSort
        advanceSort
        have imported := partition_in_caller (heap.tick "quicksort_calls") ref lo hi
          {v0 := ref, v1 := lo, v2 := hi, t5 := true, t15 := ref, t16 := lo, t17 := hi}
          valid (by omega) (fun result => reward result.1 result.2)
        simp only [Algo.partition.entry_randomized_partition] at imported ⊢
        trans pmfExpected (randomizedPartitionLaw (heap.tick "quicksort_calls") ref lo hi (by omega))
          (fun result => callExpected nextChoice randomized_quicksort.outcome
            (.active result.1 (.fn_randomized_quicksort 11 {v0 := ref, v1 := lo, v2 := hi, t5 := true, t14 := result.2, t15 := ref, t16 := lo, t17 := hi}) [])
            (fun result => reward result.1 result.2))
        · convert imported using 1
          congr 1
        simp only [quicksortLaw, dif_pos large, pmfExpected_bind]
        apply pmfExpected_congr_support
        intro partitioned possible
        have split := randomizedPartitionLaw_correct (heap.tick "quicksort_calls") ref lo hi
          (by omega) partitioned possible
        have bounds := split.1.1
        have upper := split.1.2.1
        have validPartition : ref < partitioned.1.nextRef := by rw [split.2.2.1]; exact valid
        have leftEnough : (partitioned.2 - lo).toNat ≤ fuel := by omega
        have rightEnough : (hi - (partitioned.2 + 1)).toNat ≤ fuel := by omega
        advanceSort
        have continuation := left_expected
          (.active partitioned.1 (.fn_randomized_quicksort 10
            {v0 := ref, v1 := lo, v2 := hi, v3 := partitioned.2, t5 := true, t14 := partitioned.2, t15 := ref, t16 := lo, t17 := hi}) [])
          ref lo partitioned.2 hi (quicksortLaw fuel partitioned.1 ref lo partitioned.2)
          (fun left => quicksortLaw fuel left ref (partitioned.2 + 1) hi) reward
          True.intro rfl rfl rfl rfl validPartition
          (by
            intro left possible
            rw [(quicksortLaw_frame fuel partitioned.1 ref lo partitioned.2 left possible).1]
            exact validPartition)
          (by intro payoff; exact ih partitioned.1 lo partitioned.2 validPartition leftEnough payoff)
          (by
            intro left possible payoff
            have validLeft : ref < left.nextRef := by
              rw [(quicksortLaw_frame fuel partitioned.1 ref lo partitioned.2 left possible).1]
              exact validPartition
            exact ih left (partitioned.2 + 1) hi validLeft rightEnough payoff)
        simpa only [randomized_quicksort.expectedFrom, Config.heap, pmfExpected_bind] using continuation
      · have decision : decide (1 < hi - lo) = false := by simp [large]
        simp only [decision]
        advanceSort
        advanceSort
        advanceSort
        rw [callExpected_return nextChoice randomized_quicksort.outcome _ _ rfl]
        simp [quicksortLaw, large]

/-- The complete quicksort law is reusable with every caller's initial heap and clocks. -/
theorem quicksort_law (heap : Heap) (ref : SeqRef) (lo hi : Int) (valid : ref < heap.nextRef) :
    randomized_quicksort.HasLaw heap (ref, lo, hi)
      ((quicksortLaw (hi - lo).toNat heap ref lo hi).map (fun final => (final, ()))) := by
  intro reward
  change randomized_quicksort.expectedReturn heap (ref, lo, hi) (fun final output => reward (final, output)) = _
  rw [expected_return (hi - lo).toNat heap ref lo hi valid le_rfl]
  exact (pmfExpected_map _ _ _).symm

end QuicksortAnalysis
