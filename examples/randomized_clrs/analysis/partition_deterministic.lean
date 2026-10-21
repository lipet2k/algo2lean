import Algo.partition.Points
import Algo.partition.Probability
import Algo.partition_model.Analysis
import Algo2LeanProbability.CallObservations

/-!
Source-facing contracts for Lomuto partition. The local loop lemma connects
the generated instructions to the mathematical scan; its statement refers only
to the named loop, source variables, and the public expectation interface.
-/

noncomputable section
namespace PartitionAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability
open Algo.partition Algo.partition.Algo2LeanGenerated
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local macro "advancePartition" : tactic =>
  `(tactic| rw [callExpected_next nextChoice partition.outcome _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; split <;> simp_all <;> rfl))])

/-- Completing the named loop realizes the remaining mathematical partition scan. -/
theorem remaining_expected (count : Nat) (state : Configuration) (ref : SeqRef)
    (pivot boundary first : Int) (reward : Heap → Int → ℝ≥0∞)
    (location : partition.At.loop state)
    (readRef : partition.Local.a state = some ref)
    (readPivot : partition.Local.pivot state = some pivot)
    (readBoundary : partition.Local.boundary state = some boundary)
    (readFirst : partition.Local.j state = some first)
    (readEnd : partition.Local.hi state = some (first + count + 1))
    (valid : ref < state.heap.nextRef) :
    partition.expectedFrom state reward =
      reward (scan state.heap ref pivot boundary first count).1
        (scan state.heap ref pivot boundary first count).2 := by
  induction count generalizing state boundary first with
  | zero =>
      cases state with
      | done => cases location
      | active heap frame stack =>
        cases frame <;> try cases location
        case fn_partition pc s =>
          have counter : pc = 8 := by
            unfold partition.At.loop at location
            split at location <;> simp_all
          subst pc
          change ref < heap.nextRef at valid
          simp [partition.Local.a, partition.Local.pivot, partition.Local.boundary,
            partition.Local.j, partition.Local.hi] at readRef readPivot readBoundary readFirst readEnd
          simp only [partition.expectedFrom]
          advancePartition
          advancePartition
          advancePartition
          advancePartition
          advancePartition
          advancePartition
          advancePartition
          advancePartition
          rw [callExpected_return nextChoice partition.outcome _ _ rfl]
          simp [scan, exchange, Config.heap]
  | succ count ih =>
      cases state with
      | done => cases location
      | active heap frame stack =>
        cases frame <;> try cases location
        case fn_partition pc s =>
          have counter : pc = 8 := by
            unfold partition.At.loop at location
            split at location <;> simp_all
          subst pc
          change ref < heap.nextRef at valid
          simp [partition.Local.a, partition.Local.pivot, partition.Local.boundary,
            partition.Local.j, partition.Local.hi] at readRef readPivot readBoundary readFirst readEnd
          have less : s.v5 < s.v2 - 1 := by omega
          simp only [partition.expectedFrom]
          advancePartition
          advancePartition
          advancePartition
          advancePartition
          by_cases accepted : heap.read ref first ≤ pivot
          · have decision : decide (heap.read ref first ≤ pivot) = true := by simp [accepted]
            simp only [decision]
            advancePartition
            advancePartition
            advancePartition
            advancePartition
            advancePartition
            advancePartition
            advancePartition
            have continuation := ih
              (.active (exchange (heap.tick "comparisons") ref boundary first)
                (.fn_partition 8 { s with
                  v0 := ref, v2 := first + (count + 1 : Nat) + 1, v3 := pivot,
                  v4 := boundary + 1, v5 := first + 1, v6 := heap.read ref boundary,
                  t8 := true, t9 := true }) [])
              (boundary + 1) (first + 1) True.intro rfl rfl rfl rfl
              (by simp [partition.Local.hi]; omega) (by simpa [Config.heap] using valid)
            simpa [partition.expectedFrom, Config.heap, scan, exchange, accepted,
              readRef, readPivot, readBoundary, readFirst, readEnd, less] using continuation
          · have decision : decide (heap.read ref first ≤ pivot) = false := by simp [accepted]
            simp only [decision]
            advancePartition
            advancePartition
            have continuation := ih
              (.active (heap.tick "comparisons")
                (.fn_partition 8 { s with
                  v0 := ref, v2 := first + (count + 1 : Nat) + 1, v3 := pivot,
                  v4 := boundary, v5 := first + 1, t8 := true, t9 := false }) [])
              boundary (first + 1) True.intro rfl rfl rfl rfl
              (by simp [partition.Local.hi]; omega) (by simpa [Config.heap] using valid)
            simpa [partition.expectedFrom, Config.heap, scan, accepted,
              readRef, readPivot, readBoundary, readFirst, readEnd, less] using continuation

/-- Every nonnegative observation of the full call equals its deterministic result. -/
theorem expected_return (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) (reward : Heap → Int → ℝ≥0∞) :
    partition.expectedReturn heap (ref, lo, hi) reward =
      reward (partitionResult heap ref lo hi).1 (partitionResult heap ref lo hi).2 := by
  simp only [partition.expectedReturn, partition.ValidInput, valid, ↓reduceIte,
    partition.initial, start]
  advancePartition
  advancePartition
  advancePartition
  have continuation := remaining_expected (hi - lo - 1).toNat
    (.active heap (.fn_partition 8
      { v0 := ref, v1 := lo, v2 := hi, v3 := heap.read ref (hi - 1), v4 := lo, v5 := lo }) [])
    ref (heap.read ref (hi - 1)) lo lo reward True.intro rfl rfl rfl rfl
    (by simp [partition.Local.hi]; omega) valid
  simpa [partition.expectedFrom, Config.heap, partitionResult] using continuation

/-- The reusable contract retains the complete final heap, output index, and clocks. -/
theorem partition_law (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    partition.HasLaw heap (ref, lo, hi) (PMF.pure (partitionResult heap ref lo hi)) := by
  intro payoff
  change partition.expectedReturn heap (ref, lo, hi) (fun h value => payoff (h, value)) = _
  rw [expected_return heap ref lo hi valid nonempty]
  simp [PMF.pure_apply]

-- Main result: Correctness
/-- Lomuto partition places the original pivot correctly, permutes its interval,
and preserves unrelated storage. Duplicate and negative keys are allowed. -/
theorem correctness (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    partition.returnProbability heap (ref, lo, hi)
      (fun final boundary => Partitioned final ref lo hi boundary (heap.read ref (hi - 1)) ∧
        Rearranges heap final ref lo hi ∧ final.nextRef = heap.nextRef ∧
        heap.Footprint final [ref] [] []) = 1 := by
  rw [partition.returnProbability_eq_expectedReturn heap (ref, lo, hi) valid,
    expected_return heap ref lo hi valid nonempty]
  simp [partitionResult_partitioned heap ref lo hi nonempty,
    partitionResult_rearranges heap ref lo hi nonempty, partitionResult_frame]

-- Main result: Running time
/-- A nonempty interval of length n uses exactly n-1 comparisons and between
one and n swaps. These are increments from the caller's initial clocks. -/
theorem running_time (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    partition.returnProbability heap (ref, lo, hi)
      (fun final _ => Heap.cost heap final "comparisons" = (hi - lo - 1).toNat ∧
        1 ≤ Heap.cost heap final "swaps" ∧ Heap.cost heap final "swaps" ≤ (hi - lo).toNat) = 1 := by
  rw [partition.returnProbability_eq_expectedReturn heap (ref, lo, hi) valid,
    expected_return heap ref lo hi valid nonempty]
  simp [partitionResult_comparisons, partitionResult_swaps heap ref lo hi nonempty]

/-- Every valid nonempty partition call returns with probability one. -/
theorem termination (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    partition.terminationProbability heap (ref, lo, hi) = 1 := by
  unfold partition.terminationProbability
  rw [partition.returnProbability_eq_expectedReturn heap (ref, lo, hi) valid,
    expected_return heap ref lo hi valid nonempty]
  simp

/-- Source transitions preserve the monotonicity of every charged clock. -/
theorem clock_step {before after : Configuration} (transition : Step before after)
    (clock : String) : before.heap.clocks clock ≤ after.heap.clocks clock := by
  have resumed (heap : Heap) (result : Result) (stack : Stack) :
      (resumeConfig heap result stack).heap = heap := by cases stack <;> rfl
  cases transition with
  | partition_pc1 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_partition locals.t7) stack).heap.clocks clock
      rw [resumed]
  | randomized_partition_pc1 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomized_partition locals.t5) stack).heap.clocks clock
      rw [resumed]
  | _ => simp [Config.heap, Heap.write, Heap.tick] <;> split_ifs <;> omega

private theorem outcome_halts (state : Configuration) (output : Heap × Int)
    (observed : partition.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | done heap result => rfl
  | active heap frame stack => simp [partition.outcome] at observed

private theorem outcome_cost (heap : Heap) (clock : String) (state : Configuration)
    (output : Heap × Int) (observed : partition.outcome state = some output) :
    Heap.cost heap state.heap clock = Heap.cost heap output.1 clock := by
  cases state with
  | done final result =>
      cases result <;> simp [partition.outcome] at observed
      subst output
      rfl
  | active heap frame stack => simp [partition.outcome] at observed

/-- Expected total path cost agrees with the deterministic final clock increment.
This expectation includes all executions and does not condition on return. -/
theorem expected_cost (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) (clock : String) :
    partition.expectedCost heap (ref, lo, hi) clock =
      (Heap.cost heap (partitionResult heap ref lo hi).1 clock : ℝ≥0∞) := by
  have finishes := Algo2LeanProbability.HasLaw.termination (partition_law heap ref lo hi valid nonempty)
  simp only [partition.ValidInput, valid, ↓reduceIte] at finishes
  have bridge := expected_total_eq_callExpected nextChoice partition.outcome
    outcome_halts (partition.initial heap (ref, lo, hi))
    (fun state => Heap.cost heap state.heap clock) (fun output => Heap.cost heap output.1 clock)
    (fun before after allowed => Nat.sub_le_sub_right (clock_step (choice_step.mp allowed) clock) _)
    (outcome_cost heap clock) finishes id measurable_id
  have returned := expected_return heap ref lo hi valid nonempty
    (fun final _ => (Heap.cost heap final clock : ℝ≥0∞))
  simp only [partition.expectedReturn, partition.ValidInput, valid, ↓reduceIte] at returned
  unfold partition.expectedCost partition.law partition.cost
  simp only [partition.ValidInput, valid, ↓reduceIte]
  change expected (execution nextChoice (partition.initial heap (ref, lo, hi)))
    ((Observable.total (fun state => Heap.cost heap state.heap clock)).map id measurable_id) = _
  rw [bridge]
  exact returned

/-- The unconditional expected comparison count is the interval length minus one. -/
theorem expected_comparisons (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi) :
    partition.expectedCost heap (ref, lo, hi) "comparisons" = ((hi - lo - 1).toNat : ℝ≥0∞) := by
  rw [expected_cost heap ref lo hi valid nonempty, partitionResult_comparisons]

end PartitionAnalysis
