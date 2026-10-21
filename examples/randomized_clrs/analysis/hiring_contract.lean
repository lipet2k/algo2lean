import Algo.hiring.Points
import Algo.hiring.Probability
import Algo.hiring_model.Analysis
import Algo.hiring_records.Analysis
import Algo.shuffle.Analysis
import Algo2LeanProbability.CallContext

/-!
The deterministic scan is analyzed through a local remaining-scan contract.
The randomized wrapper then reuses the imported shuffle law and that scan
contract. A separate symmetry argument on uniform permutations gives the
harmonic expected number of hires for distinct candidate scores.

The named hiring line separates the two phases. Public statements describe
source variables, joint return laws, and counter increments from the caller's
actual heap. Generated transitions appear only inside the local proof helpers.
-/

noncomputable section
namespace HiringAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability
open Algo.hiring Algo.hiring.Algo2LeanGenerated
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

macro "advanceHire" : tactic =>
  `(tactic| rw [callExpected_next nextChoice hire_assistant.outcome _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; split <;> simp_all <;> rfl))])

/-- The remaining interviews return the current number of hires plus the
strict records among the unprocessed scores, with the exact two clock changes. -/
theorem remaining_expected (count : Nat) (state : Configuration) (ref : SeqRef)
    (first best hires : Int) (reward : Heap → Int → ℝ≥0∞)
    (location : hire_assistant.At.loop state)
    (readRef : hire_assistant.Local.scores state = some ref)
    (readFirst : hire_assistant.Local.i state = some first)
    (readEnd : hire_assistant.Local.n state = some (first + (count : Int)))
    (readBest : hire_assistant.Local.best state = some best)
    (readHires : hire_assistant.Local.hires state = some hires)
    (valid : ref < state.heap.nextRef) :
    hire_assistant.expectedFrom state reward =
      reward (account state.heap count (recordsAfter (state.heap.read ref) first best count))
        (hires + recordsAfter (state.heap.read ref) first best count) := by
  induction count generalizing state first best hires with
  | zero =>
      cases state with
      | done => cases location
      | active heap frame stack =>
        cases frame <;> try cases location
        case fn_hire_assistant pc s =>
          have counter : pc = 4 := by
            unfold hire_assistant.At.loop at location
            split at location <;> simp_all
          subst pc
          change ref < heap.nextRef at valid
          simp [hire_assistant.Local.scores, hire_assistant.Local.i,
            hire_assistant.Local.n, hire_assistant.Local.best,
            hire_assistant.Local.hires] at readRef readFirst readEnd readBest readHires
          simp only [hire_assistant.expectedFrom]
          advanceHire
          advanceHire
          advanceHire
          advanceHire
          rw [callExpected_return nextChoice hire_assistant.outcome _ _ rfl]
          simp [recordsAfter, Config.heap]
  | succ count ih =>
      cases state with
      | done => cases location
      | active heap frame stack =>
        cases frame <;> try cases location
        case fn_hire_assistant pc s =>
          have counter : pc = 4 := by
            unfold hire_assistant.At.loop at location
            split at location <;> simp_all
          subst pc
          change ref < heap.nextRef at valid
          simp [hire_assistant.Local.scores, hire_assistant.Local.i,
            hire_assistant.Local.n, hire_assistant.Local.best,
            hire_assistant.Local.hires] at readRef readFirst readEnd readBest readHires
          have less : s.v4 < s.v1 := by omega
          simp only [hire_assistant.expectedFrom]
          advanceHire
          advanceHire
          advanceHire
          advanceHire
          by_cases improves : best < heap.read ref first
          · have decision : decide (best < heap.read ref first) = true := by simp [improves]
            simp only [decision]
            advanceHire
            advanceHire
            advanceHire
            advanceHire
            advanceHire
            have continuation := ih
              (.active ((heap.tick "interviews").tick "hires")
                (.fn_hire_assistant 4
                  { s with
                    v0 := ref, v1 := first + (count + 1 : Nat),
                    v2 := heap.read ref first, v3 := hires + 1, v4 := first + 1,
                    t6 := true, t7 := true }) [])
              (first + 1) (heap.read ref first) (hires + 1)
              True.intro rfl rfl (by simp [hire_assistant.Local.n]; omega)
              rfl rfl (by simpa [Config.heap] using valid)
            simpa [hire_assistant.expectedFrom, Config.heap, recordsAfter, improves,
              readRef, readFirst, readEnd, readBest, readHires, less,
              account_hire_step, Int.natCast_add, Int.add_assoc, Int.add_comm,
              Int.add_left_comm, Nat.add_comm] using continuation
          · have decision : decide (best < heap.read ref first) = false := by simp [improves]
            simp only [decision]
            advanceHire
            advanceHire
            have continuation := ih
              (.active (heap.tick "interviews")
                (.fn_hire_assistant 4
                  { s with
                    v0 := ref, v1 := first + (count + 1 : Nat), v2 := best,
                    v3 := hires, v4 := first + 1, t6 := true, t7 := false }) [])
              (first + 1) best hires
              True.intro rfl rfl (by simp [hire_assistant.Local.n]; omega)
              rfl rfl (by simpa [Config.heap] using valid)
            simpa [hire_assistant.expectedFrom, Config.heap, recordsAfter, improves,
              readRef, readFirst, readEnd, readBest, readHires, less, account_step]
              using continuation

/-- The full scan's joint output and clock effect, for every nonnegative reward. -/
theorem expected_return (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (reward : Heap → Int → ℝ≥0∞) :
    hire_assistant.expectedReturn heap (ref, n) reward =
      reward (account heap n (recordCount (heap.read ref) n))
        (recordCount (heap.read ref) n) := by
  simp only [hire_assistant.expectedReturn, hire_assistant.ValidInput,
    valid, ↓reduceIte, hire_assistant.initial, start]
  cases n with
  | zero =>
      advanceHire
      advanceHire
      advanceHire
      advanceHire
      rw [callExpected_return nextChoice hire_assistant.outcome _ _ rfl]
      simp [recordCount]
  | succ count =>
      have nonnegative : ¬ (count : Int) < 0 := by omega
      advanceHire
      advanceHire
      advanceHire
      advanceHire
      advanceHire
      advanceHire
      advanceHire
      have continuation := remaining_expected count
        (.active ((heap.tick "interviews").tick "hires")
          (.fn_hire_assistant 4
            {v0 := ref, v1 := (count + 1 : Nat), v2 := heap.read ref 0,
             v3 := 1, v4 := 1, t8 := false}) [])
        ref 1 (heap.read ref 0) 1 reward True.intro rfl rfl
        (by simp [hire_assistant.Local.n]; omega) rfl rfl
        (by simpa [Config.heap] using valid)
      simpa [hire_assistant.expectedFrom, Config.heap, recordCount,
        account_hire_step, Nat.add_comm, Int.natCast_add, nonnegative] using continuation

/-- The reusable law gives the exact record count and final heap, retaining all
caller data and existing counters. -/
theorem hiring_law (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    hire_assistant.HasLaw heap (ref, n)
      (PMF.pure (account heap n (recordCount (heap.read ref) n),
        (recordCount (heap.read ref) n : Int))) := by
  intro payoff
  change hire_assistant.expectedReturn heap (ref, n) (fun h value => payoff (h, value)) = _
  rw [expected_return heap ref n valid]
  simp [PMF.pure_apply]

/-- The algorithm returns exactly the number of strict records, with probability
one; the input sequence may contain repeated or negative scores. -/
theorem scan_correctness (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    hire_assistant.returnProbability heap (ref, n)
      (fun final result => result = (recordCount (heap.read ref) n : Int) ∧
        final = account heap n (recordCount (heap.read ref) n)) = 1 := by
  rw [hire_assistant.returnProbability_eq_expectedReturn heap (ref, n) valid,
    expected_return heap ref n valid]
  simp

/-- Every scan performs exactly `n` interviews and as many hires as strict
records. These costs are increments from the caller's initial counters. -/
theorem scan_running_time (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    hire_assistant.returnProbability heap (ref, n)
      (fun final result => Heap.cost heap final "interviews" = n ∧
        Heap.cost heap final "hires" = result.toNat ∧ result.toNat ≤ n) = 1 := by
  rw [hire_assistant.returnProbability_eq_expectedReturn heap (ref, n) valid,
    expected_return heap ref n valid]
  simp [recordCount_le]

/-- At the named hiring line, the imported shuffle is complete. The deterministic
scan's proved law gives the entire remaining output and counter effect. -/
theorem after_shuffle_expected (state : Configuration) (ref : SeqRef) (n : Nat)
    (reward : Heap → Int → ℝ≥0∞)
    (location : randomized_hire_assistant.At.hire state)
    (readRef : randomized_hire_assistant.Local.scores state = some ref)
    (readEnd : randomized_hire_assistant.Local.n state = some (n : Int))
    (valid : ref < state.heap.nextRef) :
    randomized_hire_assistant.expectedFrom state reward =
      reward (account state.heap n (recordCount (state.heap.read ref) n))
        (recordCount (state.heap.read ref) n) := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have hiring_in_caller (heap : Heap) (ref : SeqRef) (n : Nat)
      (locals : State_randomized_hire_assistant) (valid : ref < heap.nextRef)
      (reward : Heap × Int → ℝ≥0∞) :
      callExpected nextChoice randomized_hire_assistant.outcome
        (.active heap (entry_hire_assistant (ref, n))
          [fun result => match result with
            | .fn_hire_assistant value => .fn_randomized_hire_assistant 1 {locals with t2 := value}
            | _ => .invalid]) reward =
        reward (account heap n (recordCount (heap.read ref) n),
          (recordCount (heap.read ref) n : Int)) := by
    let resume : Result → Frame := fun result => match result with
      | .fn_hire_assistant value => .fn_randomized_hire_assistant 1 {locals with t2 := value}
      | _ => .invalid
    have reuse := callExpected_with_stack nextChoice hire_assistant.outcome
      randomized_hire_assistant.outcome nextChoice_context
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      heap (entry_hire_assistant (ref, n)) resume [] reward reward
      (by
        intro h result
        cases result with
        | fn_hire_assistant value =>
          rw [callExpected_next nextChoice randomized_hire_assistant.outcome _ _ rfl rfl,
            callExpected_return nextChoice randomized_hire_assistant.outcome _ _ rfl]
          rfl
        | fn_randomized_hire_assistant value =>
          exact callExpected_fail _ _ _ rfl rfl _)
    change callExpected nextChoice randomized_hire_assistant.outcome _ reward = _ at reuse
    apply reuse.trans
    have hired := expected_return heap ref n valid (fun final value => reward (final, value))
    simpa only [hire_assistant.expectedReturn, hire_assistant.ValidInput, if_pos valid, hire_assistant.initial, start, entry_hire_assistant] using hired
  cases state with
  | done => cases location
  | active heap frame stack =>
    cases frame with
    | invalid => cases location
    | fn_hire_assistant => cases location
    | import_0 => cases location
    | fn_randomized_hire_assistant pc s =>
      have place : pc = 4 := by
        unfold randomized_hire_assistant.At.hire at location
        split at location <;> simp_all
      subst pc
      simp [randomized_hire_assistant.Local.scores] at readRef
      simp [randomized_hire_assistant.Local.n] at readEnd
      simp only [randomized_hire_assistant.expectedFrom]
      rw [callExpected_next nextChoice randomized_hire_assistant.outcome _ _ rfl rfl,
          callExpected_next nextChoice randomized_hire_assistant.outcome _ _ rfl rfl,
          callExpected_next nextChoice randomized_hire_assistant.outcome _ _ rfl rfl]
      have call := hiring_in_caller heap ref n {s with t3 := ref, t4 := n} valid
        (fun pair => reward pair.1 pair.2)
      simp only [readRef, readEnd, Config.heap, entry_hire_assistant] at call ⊢
      convert call using 1
      congr 1

/-- The randomized wrapper reuses the imported shuffle law and the deterministic
hiring law, preserving their joint output, heap, and clock effects. -/
theorem randomized_expected_return (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (reward : Heap → Int → ℝ≥0∞) :
    randomized_hire_assistant.expectedReturn heap (ref, n) reward =
    pmfExpected (ShuffleAnalysis.shuffleLaw heap ref 0 n)
      (fun final => reward (account final n (recordCount (final.read ref) n))
        (recordCount (final.read ref) n)) := by
  -- Transport through the saved continuation is internal to this source-level contract.
  have shuffle_in_caller (heap : Heap) (ref : SeqRef) (n : Nat)
      (locals : State_randomized_hire_assistant) (valid : ref < heap.nextRef)
      (reward : Heap × Int → ℝ≥0∞) :
      callExpected nextChoice randomized_hire_assistant.outcome
        (.active heap (.import_0 (Algo.shuffle.entry_randomize_in_place (ref, n)) []
          (fun result => match result with
            | .fn_randomize_in_place _ => .fn_randomized_hire_assistant 4 locals)) []) reward =
      pmfExpected (ShuffleAnalysis.shuffleLaw heap ref 0 n)
        (fun final => callExpected nextChoice randomized_hire_assistant.outcome
          (.active final (.fn_randomized_hire_assistant 4 locals) []) reward) := by
    let insideShuffle : Frame → Bool
      | .import_0 _ _ _ => true
      | _ => false
    let resume : Algo.shuffle.Algo2LeanGenerated.Result → Frame := fun result =>
      match result with | .fn_randomize_in_place _ => .fn_randomized_hire_assistant 4 locals
    let continuation : Heap × Unit → ℝ≥0∞ := fun result =>
      callExpected nextChoice randomized_hire_assistant.outcome
        (.active result.1 (.fn_randomized_hire_assistant 4 locals) []) reward
    have reuse := callExpected_import Algo.shuffle.Algo2LeanGenerated.nextChoice nextChoice
      Algo.shuffle.randomize_in_place.outcome randomized_hire_assistant.outcome
      Frame.import_0 insideShuffle resume []
      (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (by intros; rfl) (by intro result; cases result; rfl)
      heap (Algo.shuffle.entry_randomize_in_place (ref, n)) reward continuation
      (by intro h result; cases result; rfl)
    apply reuse.trans
    have contract := ShuffleAnalysis.shuffle_law heap ref n valid continuation
    simp only [Algo.shuffle.randomize_in_place.ValidInput, if_pos valid] at contract
    change callExpected _ _ _ _ = pmfExpected _ continuation at contract
    simpa only [pmfExpected_map, Algo.shuffle.randomize_in_place.initial,
      start, Algo.shuffle.entry_randomize_in_place] using contract
  simp only [randomized_hire_assistant.expectedReturn,
    randomized_hire_assistant.ValidInput, valid, ↓reduceIte]
  rw [callExpected_next nextChoice randomized_hire_assistant.outcome _ _ rfl rfl,
      callExpected_next nextChoice randomized_hire_assistant.outcome _ _ rfl rfl,
      callExpected_next nextChoice randomized_hire_assistant.outcome _ _ rfl rfl,
      shuffle_in_caller heap ref n {v0 := ref, v1 := n, t6 := ref, t7 := n} valid]
  unfold pmfExpected
  apply tsum_congr
  intro final
  by_cases impossible : ShuffleAnalysis.shuffleLaw heap ref 0 n final = 0
  · simp [impossible]
  have same := (ShuffleAnalysis.shuffleLaw_frame n heap ref 0 final impossible).1
  have validFinal : ref < final.nextRef := by simpa [same] using valid
  congr 1
  have continuation := after_shuffle_expected
    (.active final (.fn_randomized_hire_assistant 4
      {v0 := ref, v1 := n, t6 := ref, t7 := n}) [])
    ref n reward True.intro rfl rfl validFinal
  simpa only [randomized_hire_assistant.expectedFrom, Config.heap] using continuation

/-- Uniform shuffling makes each candidate a strict record with probability
one divided by its position, giving the harmonic expected number of hires. -/
theorem expected_hires (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef)
    (distinct : Function.Injective (fun i : Fin n => heap.read ref i.val)) :
    randomized_hire_assistant.expectedReturn heap (ref, n)
      (fun _ result => (result.toNat : ℝ≥0∞)) = HiringRecords.harmonic n := by
  rw [randomized_expected_return heap ref n valid]
  simp only [Int.toNat_natCast]
  rw [shuffled_record_count]
  exact HiringRecords.expected_records (fun i : Fin n => heap.read ref i.val) distinct

/-- Joint randomized hiring law, reusable by a caller with arbitrary counters. -/
theorem randomized_hiring_law (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomized_hire_assistant.HasLaw heap (ref, n)
      ((ShuffleAnalysis.shuffleLaw heap ref 0 n).map (fun final =>
        (account final n (recordCount (final.read ref) n),
          (recordCount (final.read ref) n : Int)))) := by
  intro payoff
  change randomized_hire_assistant.expectedReturn heap (ref, n)
    (fun h value => payoff (h, value)) = pmfExpected _ payoff
  rw [randomized_expected_return heap ref n valid, pmfExpected_map]

private theorem randomized_returns_of_support (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (post : Heap → Int → Prop)
    (holds : ∀ final, final ∈ (ShuffleAnalysis.shuffleLaw heap ref 0 n).support →
      post (account final n (recordCount (final.read ref) n))
        (recordCount (final.read ref) n)) :
    randomized_hire_assistant.returnProbability heap (ref, n) post = 1 := by
  classical
  rw [randomized_hire_assistant.returnProbability_eq_expectedReturn heap (ref, n) valid,
    randomized_expected_return heap ref n valid]
  unfold pmfExpected
  calc
    _ = ∑' final, ShuffleAnalysis.shuffleLaw heap ref 0 n final := by
      apply tsum_congr
      intro final
      by_cases possible : final ∈ (ShuffleAnalysis.shuffleLaw heap ref 0 n).support
      · simp [holds final possible]
      · have zero := (PMF.apply_eq_zero_iff _ _).2 possible
        simp [zero]
    _ = 1 := PMF.tsum_coe _

/-- The shuffled input is a permutation of the original candidates, and the
returned number is exactly the strict-record count of the shuffled order. -/
theorem randomized_correctness (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomized_hire_assistant.returnProbability heap (ref, n)
      (fun final result => ShuffleAnalysis.Rearranges heap final ref 0 n ∧
        result = (recordCount (final.read ref) n : Int)) = 1 := by
  apply randomized_returns_of_support heap ref n valid
  intro final possible
  have shuffled := ShuffleAnalysis.shuffleLaw_rearranges n heap ref 0 final possible
  obtain ⟨permutation, outside, values⟩ := shuffled
  refine ⟨⟨permutation, ?_, ?_⟩, rfl⟩
  · simpa only [zero_add] using outside
  · exact values

/-- Exact realized operation counts: n interviews, n shuffle draws, n swaps,
and at most n hires. Existing counters and unrelated storage remain usable. -/
theorem randomized_running_time (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomized_hire_assistant.returnProbability heap (ref, n)
      (fun final result => Heap.cost heap final "interviews" = n ∧
        Heap.cost heap final "hires" = result.toNat ∧ result.toNat ≤ n ∧
        Heap.cost heap final "random_draws" = n ∧ Heap.cost heap final "swaps" = n) = 1 := by
  apply randomized_returns_of_support heap ref n valid
  intro final possible
  have clocks := ShuffleAnalysis.shuffleLaw_clocks n heap ref 0 final possible
  simp [Heap.cost, account, clocks, recordCount_le]

/-- The hire clock has harmonic expected growth, measured from the initial
heap rather than requiring fresh zeroed counters. -/
theorem expected_hire_ticks (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef)
    (distinct : Function.Injective (fun i : Fin n => heap.read ref i.val)) :
    randomized_hire_assistant.expectedReturn heap (ref, n)
      (fun final _ => (Heap.cost heap final "hires" : ℝ≥0∞)) = HiringRecords.harmonic n := by
  rw [randomized_expected_return heap ref n valid]
  calc
    _ = pmfExpected (ShuffleAnalysis.shuffleLaw heap ref 0 n)
        (fun final => (recordCount (final.read ref) n : ℝ≥0∞)) := by
      unfold pmfExpected
      apply tsum_congr
      intro final
      by_cases possible : final ∈ (ShuffleAnalysis.shuffleLaw heap ref 0 n).support
      · simp [Heap.cost, account, ShuffleAnalysis.shuffleLaw_clocks n heap ref 0 final possible]
      · have zero := (PMF.apply_eq_zero_iff _ _).2 possible
        simp [zero]
    _ = HiringRecords.harmonic n := by
      rw [shuffled_record_count]
      exact HiringRecords.expected_records (fun i : Fin n => heap.read ref i.val) distinct

end HiringAnalysis
