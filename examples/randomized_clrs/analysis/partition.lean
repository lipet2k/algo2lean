import Algo.partition_deterministic.Analysis
import Algo.partition_random_model.Analysis
import Algo.partition_rank.Analysis
import Algo2LeanProbability.CallContext

/-!
Randomized partition composes one uniform pivot draw with the independently
proved deterministic partition contract. The caller never inspects the callee's
loop transitions: the shared call-context rule transports its complete law.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace PartitionAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability
open Algo.partition Algo.partition.Algo2LeanGenerated
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local macro "advanceRandomPartition" : tactic =>
  `(tactic| rw [callExpected_next nextChoice randomized_partition.outcome _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; split <;> simp_all <;> rfl))])

/-- At the named call line, the proved partition contract determines all remaining
work and output; the earlier random pivot choice is already stored in the heap. -/
theorem after_pivot_expected (state : Configuration) (ref : SeqRef) (lo hi : Int)
    (reward : Heap → Int → ℝ≥0∞) (location : randomized_partition.At.partition state)
    (readRef : randomized_partition.Local.a state = some ref)
    (readLo : randomized_partition.Local.lo state = some lo)
    (readHi : randomized_partition.Local.hi state = some hi)
    (valid : ref < state.heap.nextRef) (nonempty : lo < hi) :
    randomized_partition.expectedFrom state reward =
      reward (partitionResult state.heap ref lo hi).1 (partitionResult state.heap ref lo hi).2 := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have partition_in_caller (heap : Heap) (ref : SeqRef) (lo hi : Int)
      (locals : State_randomized_partition) (valid : ref < heap.nextRef) (nonempty : lo < hi)
      (reward : Heap × Int → ℝ≥0∞) :
      callExpected nextChoice randomized_partition.outcome
        (.active heap (entry_partition (ref, lo, hi))
          [fun result => match result with
            | .fn_partition value => .fn_randomized_partition 1 {locals with t5 := value}
            | _ => .invalid]) reward = reward (partitionResult heap ref lo hi) := by
    have reuse := callExpected_with_stack nextChoice partition.outcome randomized_partition.outcome
      nextChoice_context (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      heap (entry_partition (ref, lo, hi))
      (fun result => match result with
        | .fn_partition value => .fn_randomized_partition 1 {locals with t5 := value}
        | _ => .invalid) [] reward reward
      (by
        intro final result
        cases result with
        | fn_partition value =>
            advanceRandomPartition
            rw [callExpected_return nextChoice randomized_partition.outcome _ _ rfl]
            rfl
        | fn_randomized_partition value =>
            change callExpected nextChoice randomized_partition.outcome (.active final .invalid []) reward = 0
            exact callExpected_fail _ _ _ rfl rfl _)
    apply reuse.trans
    have contract := expected_return heap ref lo hi valid nonempty (fun final value => reward (final, value))
    simpa only [partition.expectedReturn, partition.ValidInput, if_pos valid,
      partition.initial, start, entry_partition] using contract
  cases state with
  | done => cases location
  | active heap frame stack =>
      cases frame <;> try cases location
      case fn_randomized_partition pc s =>
        have counter : pc = 5 := by
          unfold randomized_partition.At.partition at location
          split at location <;> simp_all
        subst pc
        change ref < heap.nextRef at valid
        simp [randomized_partition.Local.a, randomized_partition.Local.lo,
          randomized_partition.Local.hi] at readRef readLo readHi
        simp only [randomized_partition.expectedFrom]
        advanceRandomPartition
        advanceRandomPartition
        advanceRandomPartition
        advanceRandomPartition
        have call := partition_in_caller heap ref lo hi {s with t6 := ref, t7 := lo, t8 := hi}
          valid nonempty (fun result => reward result.1 result.2)
        simp only [readRef, readLo, readHi, Config.heap, entry_partition] at call ⊢
        convert call using 1
        congr 1

/-- The actual randomized call has the joint model law for every nonnegative reward. -/
theorem randomized_expected_return (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) (reward : Heap → Int → ℝ≥0∞) :
    randomized_partition.expectedReturn heap (ref, lo, hi) reward =
      pmfExpected (randomizedPartitionLaw heap ref lo hi nonempty)
        (fun result => reward result.1 result.2) := by
  simp only [randomized_partition.expectedReturn, randomized_partition.ValidInput,
    valid, ↓reduceIte, randomized_partition.initial, start]
  advanceRandomPartition
  advanceRandomPartition
  rw [callExpected_uniform nextChoice randomized_partition.outcome _ _ _ _ rfl rfl nonempty]
  rw [randomizedPartitionLaw, pmfExpected_map, pmfExpected_uniformInt]
  apply Finset.sum_congr rfl
  intro chosen _
  congr 1
  advanceRandomPartition
  advanceRandomPartition
  advanceRandomPartition
  advanceRandomPartition
  advanceRandomPartition
  advanceRandomPartition
  have continuation := after_pivot_expected
    (.active (choosePivot heap ref chosen hi)
      (.fn_randomized_partition 5
        { v0 := ref, v1 := lo, v2 := hi, v3 := chosen, v4 := heap.read ref chosen,
          t9 := chosen, t10 := lo, t11 := hi }) [])
    ref lo hi reward True.intro rfl rfl rfl (by simpa [Config.heap, choosePivot] using valid) nonempty
  simpa [randomized_partition.expectedFrom, choosePivot, exchange, Config.heap] using continuation

/-- Reusable randomized partition law, including the correlated final heap,
returned pivot position, and operation costs. -/
theorem randomized_partition_law (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    randomized_partition.HasLaw heap (ref, lo, hi) (randomizedPartitionLaw heap ref lo hi nonempty) := by
  intro reward
  exact randomized_expected_return heap ref lo hi valid nonempty (fun final value => reward (final, value))

/-- A property of every supported joint outcome holds with return probability one. -/
theorem randomized_returns_of_support (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) (post : Heap → Int → Prop)
    (holds : ∀ result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support,
      post result.1 result.2) :
    randomized_partition.returnProbability heap (ref, lo, hi) post = 1 := by
  rw [randomized_partition.returnProbability_eq_expectedReturn heap (ref, lo, hi) valid,
    randomized_expected_return heap ref lo hi valid nonempty]
  unfold pmfExpected
  calc
    _ = ∑' result, randomizedPartitionLaw heap ref lo hi nonempty result := by
      apply tsum_congr
      intro result
      by_cases possible : result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support
      · simp [holds result possible]
      · simp [(PMF.apply_eq_zero_iff _ _).2 possible]
    _ = 1 := PMF.tsum_coe _

-- Main result: Correctness
/-- Randomized partition satisfies the partition inequalities, preserves the
input multiset and outside storage, and returns with probability one. -/
theorem randomized_correctness (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    randomized_partition.returnProbability heap (ref, lo, hi)
      (fun final boundary => Partitioned final ref lo hi boundary (final.read ref boundary) ∧
        Rearranges heap final ref lo hi ∧ final.nextRef = heap.nextRef ∧
        heap.Footprint final [ref] [] []) = 1 := by
  apply randomized_returns_of_support heap ref lo hi valid nonempty
  exact randomizedPartitionLaw_correct heap ref lo hi nonempty

-- Main result: Running time
/-- Randomized partition performs n-1 comparisons, one draw, and at most n+1 swaps
on an interval of length n, including pivot selection and final placement. -/
theorem randomized_running_time (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    randomized_partition.returnProbability heap (ref, lo, hi)
      (fun final _ => Heap.cost heap final "comparisons" = (hi - lo - 1).toNat ∧
        Heap.cost heap final "random_draws" = 1 ∧ 2 ≤ Heap.cost heap final "swaps" ∧
        Heap.cost heap final "swaps" ≤ (hi - lo).toNat + 1) = 1 := by
  apply randomized_returns_of_support heap ref lo hi valid nonempty
  exact randomizedPartitionLaw_cost heap ref lo hi nonempty

/-- Any specified distinct input key has probability 1/n of becoming the pivot. -/
theorem randomized_pivot_probability (heap : Heap) (ref : SeqRef) (lo hi position : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (member : lo ≤ position ∧ position < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_partition.returnProbability heap (ref, lo, hi)
      (fun final boundary => final.read ref boundary = heap.read ref position) =
      ((hi - lo).toNat : ℝ≥0∞)⁻¹ := by
  rw [randomized_partition.returnProbability_eq_expectedReturn heap (ref, lo, hi) valid,
    randomized_expected_return heap ref lo hi valid nonempty]
  convert pivot_probability heap ref lo hi position nonempty member distinct using 1
  congr 1
  funext result
  split_ifs <;> rfl

private theorem random_outcome_halts (state : Configuration) (output : Heap × Int)
    (observed : randomized_partition.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | done heap result => rfl
  | active heap frame stack => simp [randomized_partition.outcome] at observed

private theorem random_outcome_cost (heap : Heap) (clock : String) (state : Configuration)
    (output : Heap × Int) (observed : randomized_partition.outcome state = some output) :
    Heap.cost heap state.heap clock = Heap.cost heap output.1 clock := by
  cases state with
  | done final result =>
      cases result <;> simp [randomized_partition.outcome] at observed
      subst output
      rfl
  | active heap frame stack => simp [randomized_partition.outcome] at observed

/-- The joint call law also gives unconditional total path costs; nontermination
is not discarded or conditioned away. -/
theorem randomized_expected_cost (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) (clock : String) :
    randomized_partition.expectedCost heap (ref, lo, hi) clock =
      pmfExpected (randomizedPartitionLaw heap ref lo hi nonempty)
        (fun result => (Heap.cost heap result.1 clock : ℝ≥0∞)) := by
  have finishes := Algo2LeanProbability.HasLaw.termination
    (randomized_partition_law heap ref lo hi valid nonempty)
  simp only [randomized_partition.ValidInput, valid, ↓reduceIte] at finishes
  have bridge := expected_total_eq_callExpected nextChoice randomized_partition.outcome
    random_outcome_halts (randomized_partition.initial heap (ref, lo, hi))
    (fun state => Heap.cost heap state.heap clock) (fun output => Heap.cost heap output.1 clock)
    (fun before after allowed => Nat.sub_le_sub_right (clock_step (choice_step.mp allowed) clock) _)
    (random_outcome_cost heap clock) finishes id measurable_id
  have returned := randomized_expected_return heap ref lo hi valid nonempty
    (fun final _ => (Heap.cost heap final clock : ℝ≥0∞))
  simp only [randomized_partition.expectedReturn, randomized_partition.ValidInput,
    valid, ↓reduceIte] at returned
  unfold randomized_partition.expectedCost randomized_partition.law randomized_partition.cost
  simp only [randomized_partition.ValidInput, valid, ↓reduceIte]
  change expected (execution nextChoice (randomized_partition.initial heap (ref, lo, hi)))
    ((Observable.total (fun state => Heap.cost heap state.heap clock)).map id measurable_id) = _
  rw [bridge]
  exact returned

/-- Randomized pivot selection does not change the n-1 comparison count. -/
theorem randomized_expected_comparisons (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    randomized_partition.expectedCost heap (ref, lo, hi) "comparisons" =
      ((hi - lo - 1).toNat : ℝ≥0∞) := by
  rw [randomized_expected_cost heap ref lo hi valid nonempty]
  unfold pmfExpected
  calc
    _ = ∑' result, randomizedPartitionLaw heap ref lo hi nonempty result *
        ((hi - lo - 1).toNat : ℝ≥0∞) := by
      apply tsum_congr
      intro result
      by_cases possible : result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support
      · simp only [(randomizedPartitionLaw_cost heap ref lo hi nonempty result possible).1]
      · simp [(PMF.apply_eq_zero_iff _ _).2 possible]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- For distinct keys, any observation of the returned boundary has the
expectation of a uniform integer in the original interval. -/
theorem randomized_boundary_expected (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) (reward : Int → ℝ≥0∞) :
    randomized_partition.expectedReturn heap (ref, lo, hi) (fun _ boundary => reward boundary) =
      pmfExpected (uniformInt lo hi nonempty) reward := by
  rw [randomized_expected_return heap ref lo hi valid nonempty]
  calc
    _ = pmfExpected ((randomizedPartitionLaw heap ref lo hi nonempty).map Prod.snd) reward :=
      (pmfExpected_map _ _ _).symm
    _ = _ := by rw [randomized_boundary_law heap ref lo hi nonempty distinct]

/-- Each possible pivot rank occurs with probability exactly 1/n. This statement
uses the actual returned boundary and is directly reusable by recursive callers. -/
theorem randomized_boundary_probability (heap : Heap) (ref : SeqRef) (lo hi boundary : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_partition.returnProbability heap (ref, lo, hi) (fun _ result => result = boundary) =
      if lo ≤ boundary ∧ boundary < hi then ((hi - lo).toNat : ℝ≥0∞)⁻¹ else 0 := by
  rw [randomized_partition.returnProbability_eq_expectedReturn heap (ref, lo, hi) valid]
  have evaluate := randomized_boundary_expected heap ref lo hi valid nonempty distinct
    (fun result => if result = boundary then (1 : ℝ≥0∞) else 0)
  trans pmfExpected (uniformInt lo hi nonempty) (fun result => if result = boundary then 1 else 0)
  · convert evaluate using 1
    congr 1
    funext final result
    split_ifs <;> rfl
  · simp [pmfExpected, uniformInt_apply]

end PartitionAnalysis
