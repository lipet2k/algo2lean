import Algo.selection.Points
import Algo.selection.Probability
import Algo.selection_model.Analysis
import Algo.selection_cost_model.Analysis
import Algo.partition.Analysis
import Algo2LeanProbability.CallContext

/-!
Selection's proof reuses randomized partition as a complete joint law. Local
helpers describe the named decision point and recursive tail calls; none of
them inspect partition's transition rules.
-/

noncomputable section
namespace SelectionAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis
open Algo.selection Algo.selection.Algo2LeanGenerated
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

macro "advanceSelect" : tactic =>
  `(tactic| ((try dsimp only); rw [callExpected_next nextChoice randomized_select.outcome _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; split <;> simp_all <;> rfl))]; (try dsimp only)))

/-- After partition, selection either returns the pivot or recurses only on the
side containing the requested rank. The partition's heap is passed unchanged. -/
theorem after_partition_expected (state : Configuration) (ref : SeqRef)
    (lo hi requested pivot : Int) (reward : Heap → Int → ℝ≥0∞)
    (location : randomized_select.At.choose state)
    (readRef : randomized_select.Local.a state = some ref)
    (readLo : randomized_select.Local.lo state = some lo)
    (readHi : randomized_select.Local.hi state = some hi)
    (readRank : randomized_select.Local.rank state = some requested)
    (readPivot : randomized_select.Local.pivot state = some pivot)
    (valid : ref < state.heap.nextRef) :
    randomized_select.expectedFrom state reward =
      if requested = pivot - lo then reward state.heap (state.heap.read ref pivot)
      else if requested < pivot - lo then
        randomized_select.expectedReturn state.heap (ref, lo, pivot, requested) reward
      else randomized_select.expectedReturn state.heap
        (ref, pivot + 1, hi, requested - (pivot - lo) - 1) reward := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have recursive_call (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
      (resume : Result → Frame) (valid : ref < heap.nextRef)
      (returns : ∀ final value, nextChoice (.active final (resume (.fn_randomized_select value)) []) =
        .next (.done final (.fn_randomized_select value))) (reward : Heap × Int → ℝ≥0∞) :
      callExpected nextChoice randomized_select.outcome
        (.active heap (.fn_randomized_select 29 {v0 := ref, v1 := lo, v2 := hi, v3 := requested}) [resume]) reward =
      randomized_select.expectedReturn heap (ref, lo, hi, requested)
        (fun final value => reward (final, value)) := by
    have reuse := callExpected_with_stack nextChoice randomized_select.outcome randomized_select.outcome
      nextChoice_context (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      heap (entry_randomized_select (ref, lo, hi, requested)) resume [] reward reward
      (by
        intro final result
        cases result with
        | fn_randomized_select value =>
          rw [callExpected_next nextChoice randomized_select.outcome _ _ rfl (returns final value),
            callExpected_return nextChoice randomized_select.outcome _ _ rfl]
          rfl)
    simpa only [randomized_select.expectedReturn, randomized_select.ValidInput, if_pos valid,
      randomized_select.initial, start, entry_randomized_select] using reuse
  cases state with
  | done => cases location
  | active heap frame stack =>
    cases frame <;> try cases location
    case fn_randomized_select pc s =>
      have place : pc = 19 := by
        unfold randomized_select.At.choose at location
        split at location <;> simp_all
      subst pc
      simp [randomized_select.Local.a, randomized_select.Local.lo, randomized_select.Local.hi,
        randomized_select.Local.rank, randomized_select.Local.pivot] at readRef readLo readHi readRank readPivot
      change ref < heap.nextRef at valid
      simp only [randomized_select.expectedFrom]
      advanceSelect
      advanceSelect
      by_cases found : requested = pivot - lo
      · have decision : decide (s.v3 = s.v4 - s.v1) = true := by simp [readRank, readPivot, readLo, found]
        try simp only [decision]
        advanceSelect
        advanceSelect
        advanceSelect
        rw [callExpected_return nextChoice randomized_select.outcome _ _ rfl]
        simp [Config.heap, found]
      · have decision : decide (s.v3 = s.v4 - s.v1) = false := by simp [readRank, readPivot, readLo, found]
        try simp only [decision]
        advanceSelect
        advanceSelect
        by_cases before : requested < pivot - lo
        · have decision : decide (s.v3 < s.v4 - s.v1) = true := by simp [readRank, readPivot, readLo, before]
          try simp only [decision]
          advanceSelect
          advanceSelect
          advanceSelect
          advanceSelect
          advanceSelect
          advanceSelect
          simp only [readRef, readLo, readHi, readRank, readPivot]
          rw [recursive_call heap ref lo pivot requested _ valid (by intros; rfl)]
          simp [Config.heap, found, before]
        · have decision : decide (s.v3 < s.v4 - s.v1) = false := by simp [readRank, readPivot, readLo, before]
          try simp only [decision]
          advanceSelect
          advanceSelect
          advanceSelect
          advanceSelect
          advanceSelect
          advanceSelect
          simp only [readRef, readLo, readHi, readRank, readPivot]
          rw [recursive_call heap ref (pivot + 1) hi (requested - (pivot - lo) - 1) _ valid (by intros; rfl)]
          simp [Config.heap, found, before]

/-- At the partition call, the imported law supplies the next decision state.
This contract preserves the dependence between the pivot index and mutated heap. -/
theorem partition_expected (state : Configuration) (ref : SeqRef)
    (lo hi requested : Int) (reward : Heap → Int → ℝ≥0∞)
    (location : randomized_select.At.partition state)
    (readRef : randomized_select.Local.a state = some ref)
    (readLo : randomized_select.Local.lo state = some lo)
    (readHi : randomized_select.Local.hi state = some hi)
    (readRank : randomized_select.Local.rank state = some requested)
    (valid : ref < state.heap.nextRef) (nonempty : lo < hi) :
    randomized_select.expectedFrom state reward =
      pmfExpected (randomizedPartitionLaw state.heap ref lo hi nonempty)
        (fun result => if requested = result.2 - lo then reward result.1 (result.1.read ref result.2)
          else if requested < result.2 - lo then
            randomized_select.expectedReturn result.1 (ref, lo, result.2, requested) reward
          else randomized_select.expectedReturn result.1
            (ref, result.2 + 1, hi, requested - (result.2 - lo) - 1) reward) := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have imported_partition (heap : Heap) (ref : SeqRef) (lo hi : Int)
      (locals : Int → State_randomized_select) (valid : ref < heap.nextRef)
      (nonempty : lo < hi) (reward : Heap × Int → ℝ≥0∞) :
      callExpected nextChoice randomized_select.outcome
        (.active heap (.import_0 (Algo.partition.entry_randomized_partition (ref, lo, hi)) []
          (fun result => match result with
            | .fn_randomized_partition value => .fn_randomized_select 20 (locals value)
            | _ => .invalid)) []) reward =
      pmfExpected (randomizedPartitionLaw heap ref lo hi nonempty)
        (fun result => callExpected nextChoice randomized_select.outcome
          (.active result.1 (.fn_randomized_select 20 (locals result.2)) []) reward) := by
    let insidePartition : Frame → Bool
      | .import_0 _ _ _ => true
      | _ => false
    let resume : Algo.partition.Algo2LeanGenerated.Result → Frame := fun result => match result with
      | .fn_randomized_partition value => .fn_randomized_select 20 (locals value)
      | _ => .invalid
    let continuation : Heap × Int → ℝ≥0∞ := fun result =>
      callExpected nextChoice randomized_select.outcome
        (.active result.1 (.fn_randomized_select 20 (locals result.2)) []) reward
    have reuse := callExpected_import Algo.partition.Algo2LeanGenerated.nextChoice nextChoice
      Algo.partition.randomized_partition.outcome randomized_select.outcome
      Frame.import_0 insidePartition resume []
      (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (by intros; rfl) (by intro result; cases result <;> rfl)
      heap (Algo.partition.entry_randomized_partition (ref, lo, hi)) reward continuation
      (by
        intro final result
        cases result with
        | fn_randomized_partition value => rfl
        | fn_partition value => exact callExpected_fail _ _ _ rfl rfl _)
    apply reuse.trans
    have contract := randomized_partition_law heap ref lo hi valid nonempty continuation
    simp only [Algo.partition.randomized_partition.ValidInput, if_pos valid] at contract
    change callExpected _ _ _ _ = pmfExpected _ continuation at contract
    simpa only [Algo.partition.randomized_partition.initial, start,
      Algo.partition.entry_randomized_partition] using contract
  cases state with
  | done => cases location
  | active heap frame stack =>
    cases frame <;> try cases location
    case fn_randomized_select pc s =>
      have place : pc = 24 := by
        unfold randomized_select.At.partition at location
        split at location <;> simp_all
      subst pc
      simp [randomized_select.Local.a, randomized_select.Local.lo, randomized_select.Local.hi,
        randomized_select.Local.rank] at readRef readLo readHi readRank
      change ref < heap.nextRef at valid
      simp only [randomized_select.expectedFrom, Config.heap]
      advanceSelect
      advanceSelect
      advanceSelect
      advanceSelect
      try simp only [readRef, readLo, readHi]
      let saved (value : Int) : State_randomized_select :=
        {s with v0 := ref, v1 := lo, v2 := hi, t19 := value, t20 := ref, t21 := lo, t22 := hi}
      trans pmfExpected (randomizedPartitionLaw heap ref lo hi nonempty)
        (fun result => callExpected nextChoice randomized_select.outcome
          (.active result.1 (.fn_randomized_select 20 (saved result.2)) [])
          (fun pair => reward pair.1 pair.2))
      · convert imported_partition heap ref lo hi saved valid nonempty
          (fun pair => reward pair.1 pair.2) using 1
        congr 1
      unfold pmfExpected
      apply tsum_congr
      intro result
      by_cases impossible : randomizedPartitionLaw heap ref lo hi nonempty result = 0
      · simp [impossible]
      have validFinal : ref < result.1.nextRef := by
        have same := (randomizedPartitionLaw_correct heap ref lo hi nonempty result impossible).2.2.1
        simpa [same] using valid
      congr 1
      advanceSelect
      have continuation := after_partition_expected
        (.active result.1 (.fn_randomized_select 19
          {s with v4 := result.2, t19 := result.2, t20 := ref, t21 := lo, t22 := hi}) [])
        ref lo hi requested result.2 reward True.intro
        (by simpa [randomized_select.Local.a] using readRef)
        (by simpa [randomized_select.Local.lo] using readLo)
        (by simpa [randomized_select.Local.hi] using readHi)
        (by simpa [randomized_select.Local.rank] using readRank)
        (by simp [randomized_select.Local.pivot]) validFinal
      simpa only [randomized_select.expectedFrom, Config.heap, readRef, readLo, readHi] using continuation

/-- The source execution has the finite recursive joint law whenever the fuel
covers the interval length. Each recursive branch reuses the partition contract. -/
theorem expected_return (fuel : Nat) (heap : Heap) (ref : SeqRef)
    (lo hi requested : Int) (valid : ref < heap.nextRef)
    (nonempty : lo < hi) (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (enough : (hi - lo).toNat ≤ fuel) (reward : Heap → Int → ℝ≥0∞) :
    randomized_select.expectedReturn heap (ref, lo, hi, requested) reward =
      pmfExpected (selectionLaw fuel heap ref lo hi requested)
        (fun result => reward result.1 result.2) := by
  induction fuel generalizing heap lo hi requested with
  | zero => omega
  | succ fuel ih =>
    simp only [randomized_select.expectedReturn, randomized_select.ValidInput,
      valid, ↓reduceIte, randomized_select.initial, start]
    advanceSelect
    advanceSelect
    by_cases singleton : hi - lo = 1
    · try simp only [singleton, decide_true]
      advanceSelect
      advanceSelect
      advanceSelect
      rw [callExpected_return nextChoice randomized_select.outcome _ _ rfl]
      simp [selectionLaw, singleton, pmfExpected_pure]
    · have decision : decide (hi - lo = 1) = false := by simp [singleton]
      try simp only [decision]
      advanceSelect
      change randomized_select.expectedFrom
        (.active (heap.tick "selection_calls") (.fn_randomized_select 24
          {v0 := ref, v1 := lo, v2 := hi, v3 := requested}) []) reward = _
      rw [partition_expected
        (.active (heap.tick "selection_calls") (.fn_randomized_select 24
          {v0 := ref, v1 := lo, v2 := hi, v3 := requested}) [])
        ref lo hi requested reward True.intro rfl rfl rfl rfl valid nonempty]
      rw [selectionLaw, if_neg singleton, dif_pos nonempty, pmfExpected_bind]
      simp only [Config.heap]
      unfold pmfExpected
      apply tsum_congr
      intro result
      by_cases impossible : randomizedPartitionLaw (heap.tick "selection_calls") ref lo hi nonempty result = 0
      · simp [impossible]
      obtain ⟨partitioned, _, refs, _⟩ := randomizedPartitionLaw_correct
        (heap.tick "selection_calls") ref lo hi nonempty result impossible
      have validFinal : ref < result.1.nextRef := by simpa [refs] using valid
      have lower := partitioned.1
      have upper := partitioned.2.1
      congr 1
      by_cases found : requested = result.2 - lo
      · simp [found]
      · simp only [found, ↓reduceIte]
        by_cases before : requested < result.2 - lo
        · simp only [before, ↓reduceIte]
          exact ih result.1 lo result.2 requested validFinal (by omega) (by omega) (by omega)
        · simp only [before, ↓reduceIte]
          exact ih result.1 (result.2 + 1) hi (requested - (result.2 - lo) - 1)
            validFinal (by omega) (by omega) (by omega)

/-- The reusable joint law of randomized selection. It certifies almost-sure
successful return, preserving data and costs for subsequent callers. -/
theorem selection_law (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo) :
    randomized_select.HasLaw heap (ref, lo, hi, requested)
      (selectionLaw (hi - lo).toNat heap ref lo hi requested) := by
  intro payoff
  change randomized_select.expectedReturn heap (ref, lo, hi, requested)
    (fun final value => payoff (final, value)) = pmfExpected _ payoff
  exact expected_return _ heap ref lo hi requested valid nonempty requestedValid le_rfl _

/-- The completed selection call needs at most four comparisons per input
key in expectation. Existing comparison counts are subtracted automatically. -/
theorem expected_comparisons (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (valid : ref < heap.nextRef) (nonempty : lo < hi)
    (requestedValid : 0 ≤ requested ∧ requested < hi - lo)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    randomized_select.expectedReturn heap (ref, lo, hi, requested)
      (fun final _ => (Heap.cost heap final "comparisons" : ℝ≥0∞)) ≤
      4 * ((hi - lo).toNat : ℝ≥0∞) := by
  rw [expected_return (hi - lo).toNat heap ref lo hi requested valid nonempty requestedValid le_rfl]
  simpa only [Heap.cost, Nat.sub_self, Nat.cast_zero, zero_add] using
    selectionLaw_comparisons_le (hi - lo).toNat heap ref lo hi requested nonempty requestedValid
      distinct (heap.clocks "comparisons") le_rfl

end SelectionAnalysis
