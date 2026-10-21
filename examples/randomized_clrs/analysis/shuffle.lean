import Algo.shuffle.Points
import Algo.shuffle.Probability
import Algo.shuffle_model.Analysis
import Algo.shuffle_uniform.Analysis
import Algo2LeanProbability.CallObservations

/-!
The shuffle is analyzed by a local remaining-loop contract. Its reward may be
any nonnegative function of the final heap and returned unit value, so the same
contract supports output events and cost observations. The finite shuffle model
records the complete joint heap distribution, including the caller's clocks.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace ShuffleAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability
open Algo.shuffle Algo.shuffle.Algo2LeanGenerated
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local macro "advance" : tactic =>
  `(tactic| rw [callExpected_next nextChoice randomize_in_place.outcome _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; split <;> simp_all <;> rfl))])

/-- Starting at the loop test, the remaining `count` iterations have exactly
    the model's final-heap law. No reachability or preceding transcript is needed. -/
theorem remaining_expected (count : Nat) (state : Configuration) (ref : SeqRef)
    (first : Int) (reward : Heap → Unit → ℝ≥0∞)
    (location : randomize_in_place.At.loop state)
    (readRef : randomize_in_place.Local.a state = some ref)
    (readFirst : randomize_in_place.Local.i state = some first)
    (readEnd : randomize_in_place.Local.n state = some (first + (count : Int)))
    (valid : ref < state.heap.nextRef) :
    randomize_in_place.expectedFrom state reward =
      ∑' final, shuffleLaw state.heap ref first count final * reward final () := by
  induction count generalizing state first with
  | zero =>
      cases state with
      | done => cases location
      | active heap frame stack =>
        cases frame with
        | invalid => cases location
        | fn_randomize_in_place pc s =>
          have counter : pc = 4 := by
            unfold randomize_in_place.At.loop at location
            split at location <;> simp_all
          subst pc
          change ref < heap.nextRef at valid
          simp [randomize_in_place.Local.a, randomize_in_place.Local.i,
            randomize_in_place.Local.n] at readRef readFirst readEnd
          simp only [randomize_in_place.expectedFrom]
          advance
          advance
          advance
          advance
          rw [callExpected_return nextChoice randomize_in_place.outcome _ _ rfl]
          simp [shuffleLaw, PMF.pure_apply, Config.heap]
  | succ count ih =>
      cases state with
      | done => cases location
      | active heap frame stack =>
        cases frame with
        | invalid => cases location
        | fn_randomize_in_place pc s =>
          have counter : pc = 4 := by
            unfold randomize_in_place.At.loop at location
            split at location <;> simp_all
          subst pc
          change ref < heap.nextRef at valid
          simp [randomize_in_place.Local.a, randomize_in_place.Local.i,
            randomize_in_place.Local.n] at readRef readFirst readEnd
          have less : s.v2 < s.v1 := by omega
          simp only [randomize_in_place.expectedFrom]
          advance
          advance
          advance
          advance
          rw [callExpected_uniform nextChoice randomize_in_place.outcome _ _ _ _ rfl rfl
            (by simpa only [readFirst, readEnd] using less)]
          rw [shuffleLaw_expected_succ]
          simp only [add_sub_cancel_left]
          apply Finset.sum_congr rfl
          intro chosen member
          congr 1
          advance
          advance
          advance
          advance
          advance
          advance
          advance
          have continuation := ih
            (.active (swapStep heap ref first chosen)
              (.fn_randomize_in_place 4
                { v0 := ref, v1 := first + (count + 1 : Nat), v2 := first + 1,
                  v3 := chosen, v4 := heap.read ref first, t6 := true, t7 := chosen,
                  t8 := first, t9 := first + (count + 1 : Nat) }) [])
            (first + 1) True.intro rfl rfl
            (by simp [randomize_in_place.Local.n]; omega)
            (by simpa [Config.heap] using valid)
          simpa [randomize_in_place.expectedFrom, Config.heap, swapStep, Heap.read_tick,
            readRef, readFirst, readEnd, less] using continuation

/-- The completed-call expectation equals the finite shuffle model for every
nonnegative observation of the final heap and output. -/
theorem expected_return (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (reward : Heap → Unit → ℝ≥0∞) :
    randomize_in_place.expectedReturn heap (ref, n) reward =
      ∑' final, shuffleLaw heap ref 0 n final * reward final () := by
  simp only [randomize_in_place.expectedReturn, randomize_in_place.ValidInput,
    valid, ↓reduceIte, randomize_in_place.initial, start]
  advance
  have continuation := remaining_expected n
    (.active heap (.fn_randomize_in_place 4 { v0 := ref, v1 := n, v2 := 0 }) [])
    ref 0 reward True.intro rfl rfl
    (by simp [randomize_in_place.Local.n]) valid
  exact continuation

/-- The reusable probabilistic call contract retains the final heap, all shared
storage, and all operation counters. It applies to every nonnegative reward. -/
theorem shuffle_law (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomize_in_place.HasLaw heap (ref, n)
      ((shuffleLaw heap ref 0 n).map (fun final => (final, ()))) := by
  intro payoff
  change _ = pmfExpected ((shuffleLaw heap ref 0 n).map (fun final => (final, ()))) payoff
  rw [pmfExpected_map]
  exact expected_return heap ref n valid (fun final result => payoff (final, result))

/-- The path-level return event is determined by the same joint call law. -/
theorem return_probability (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (post : Heap → Unit → Prop) :
    randomize_in_place.returnProbability heap (ref, n) post =
      ∑' final, shuffleLaw heap ref 0 n final * (if post final () then 1 else 0) := by
  classical
  have halting : ∀ state result, randomize_in_place.outcome state = some result →
      nextChoice state = .halt := by
    intro state result observed
    cases state with
    | done heap result => rfl
    | active heap frame stack => simp [randomize_in_place.outcome] at observed
  unfold randomize_in_place.returnProbability randomize_in_place.law
  simp only [randomize_in_place.ValidInput, valid, ↓reduceIte]
  rw [← callProbability_eq_execution nextChoice randomize_in_place.outcome halting]
  have result := expected_return heap ref n valid (fun final result => if post final result then 1 else 0)
  simpa only [randomize_in_place.expectedReturn, randomize_in_place.ValidInput,
    valid, ↓reduceIte, callProbability] using result

/-- A property shared by every supported model outcome holds with probability
one in the generated algorithm. -/
theorem returns_of_support (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (post : Heap → Prop)
    (holds : ∀ final ∈ (shuffleLaw heap ref 0 n).support, post final) :
    randomize_in_place.returnProbability heap (ref, n) (fun final _ => post final) = 1 := by
  classical
  rw [return_probability heap ref n valid]
  calc
    _ = ∑' final, shuffleLaw heap ref 0 n final := by
      apply tsum_congr
      intro final
      by_cases possible : final ∈ (shuffleLaw heap ref 0 n).support
      · simp [holds final possible]
      · have zero := (PMF.apply_eq_zero_iff _ _).2 possible
        simp [zero]
    _ = 1 := PMF.tsum_coe _

/-- With probability one the shuffle returns a permutation of the original
interval, preserves unrelated storage, and allocates no sequence objects. -/
theorem correctness (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomize_in_place.returnProbability heap (ref, n)
      (fun final _ => Rearranges heap final ref 0 n ∧
        heap.Footprint final [ref] [] [] ∧ final.nextRef = heap.nextRef) = 1 := by
  apply returns_of_support heap ref n valid
  intro final possible
  obtain ⟨refs, frame⟩ := shuffleLaw_frame n heap ref 0 final possible
  exact ⟨by simpa using shuffleLaw_rearranges n heap ref 0 final possible, frame, refs⟩

/-- Successful termination has probability one for every valid shared sequence. -/
theorem termination (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomize_in_place.terminationProbability heap (ref, n) = 1 := by
  exact returns_of_support heap ref n valid (fun _ => True) (fun _ _ => True.intro)

-- Main result: Running time
/-- Exactly n random draws and n swaps occur, measured from the caller's actual
initial counters; all other counters are preserved, with probability one. -/
theorem running_time (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomize_in_place.returnProbability heap (ref, n)
      (fun final _ => ∀ clock, Heap.cost heap final clock =
        if clock = "random_draws" ∨ clock = "swaps" then n else 0) = 1 := by
  apply returns_of_support heap ref n valid
  intro final possible clock
  simp [Heap.cost, shuffleLaw_clocks n heap ref 0 final possible clock]

/-- The same joint law computes expectations of counter increments without
resetting counters or assuming independence between storage and costs. -/
theorem expected_ticks (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (clock : String) :
    randomize_in_place.expectedReturn heap (ref, n)
      (fun final _ => (Heap.cost heap final clock : ℝ≥0∞)) =
      if clock = "random_draws" ∨ clock = "swaps" then n else 0 := by
  classical
  rw [expected_return heap ref n valid]
  calc
    _ = ∑' final, shuffleLaw heap ref 0 n final *
        (if clock = "random_draws" ∨ clock = "swaps" then (n : ℝ≥0∞) else 0) := by
      apply tsum_congr
      intro final
      by_cases possible : final ∈ (shuffleLaw heap ref 0 n).support
      · simp [Heap.cost, shuffleLaw_clocks n heap ref 0 final possible clock]
      · have zero := (PMF.apply_eq_zero_iff _ _).2 possible
        simp [zero]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      split_ifs <;> simp

/-- A source transition never decreases a caller-visible clock. -/
theorem clock_step {before after : Configuration} (transition : Step before after)
    (clock : String) : before.heap.clocks clock ≤ after.heap.clocks clock := by
  have resumed (heap : Heap) (result : Result) (stack : Stack) :
      (resumeConfig heap result stack).heap = heap := by
    cases stack <;> rfl
  cases transition with
  | randomize_in_place_pc1 heap locals stack =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_randomize_in_place locals.t5) stack).heap.clocks clock
      rw [resumed]
  | _ => simp [Config.heap, Heap.write, Heap.tick] <;> split_ifs <;> omega

private theorem outcome_halts (state : Configuration) (output : Heap × Unit)
    (observed : randomize_in_place.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | done heap result => rfl
  | active heap frame stack => simp [randomize_in_place.outcome] at observed

private theorem outcome_cost (heap : Heap) (clock : String) (state : Configuration)
    (output : Heap × Unit) (observed : randomize_in_place.outcome state = some output) :
    Heap.cost heap state.heap clock = Heap.cost heap output.1 clock := by
  cases state with
  | done final result =>
      cases result
      simp [randomize_in_place.outcome] at observed
      subst output
      rfl
  | active heap frame stack => simp [randomize_in_place.outcome] at observed

/-- The final-counter reward agrees with the expected total path cost because
termination is almost sure and every source transition preserves clock order. -/
theorem expected_cost (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (clock : String) :
    randomize_in_place.expectedCost heap (ref, n) clock =
      if clock = "random_draws" ∨ clock = "swaps" then (n : ℝ≥0∞) else 0 := by
  have finishes := Algo2LeanProbability.HasLaw.termination (shuffle_law heap ref n valid)
  simp only [randomize_in_place.ValidInput, valid, ↓reduceIte] at finishes
  have bridge := expected_total_eq_callExpected nextChoice randomize_in_place.outcome
    outcome_halts (randomize_in_place.initial heap (ref, n))
    (fun state => Heap.cost heap state.heap clock) (fun output => Heap.cost heap output.1 clock)
    (fun before after allowed => Nat.sub_le_sub_right (clock_step (choice_step.mp allowed) clock) _)
    (outcome_cost heap clock) finishes id measurable_id
  have returned := expected_ticks heap ref n valid clock
  simp only [randomize_in_place.expectedReturn, randomize_in_place.ValidInput,
    valid, ↓reduceIte] at returned
  unfold randomize_in_place.expectedCost randomize_in_place.law randomize_in_place.cost
  simp only [randomize_in_place.ValidInput, valid, ↓reduceIte]
  change expected (execution nextChoice (randomize_in_place.initial heap (ref, n)))
    ((Observable.total (fun state => Heap.cost heap state.heap clock)).map id measurable_id) = _
  rw [bridge]
  convert returned using 1 <;> first | rfl | (split_ifs <;> simp)

/-- Exact tail probability for total charged cost, without conditioning on return.
For the draw and swap clocks this is one below n and zero at or above n. -/
theorem runtime_tail (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (clock : String) (threshold : ℝ≥0∞) :
    randomize_in_place.costProbability heap (ref, n) clock threshold =
      if threshold < (if clock = "random_draws" ∨ clock = "swaps" then (n : ℝ≥0∞) else 0)
      then 1 else 0 := by
  have finishes := Algo2LeanProbability.HasLaw.termination (shuffle_law heap ref n valid)
  simp only [randomize_in_place.ValidInput, valid, ↓reduceIte] at finishes
  have bridge := costProbability_eq_callProbability nextChoice randomize_in_place.outcome
    outcome_halts (randomize_in_place.initial heap (ref, n))
    (fun state => Heap.cost heap state.heap clock) (fun output => Heap.cost heap output.1 clock)
    (fun before after allowed => Nat.sub_le_sub_right (clock_step (choice_step.mp allowed) clock) _)
    (outcome_cost heap clock) finishes threshold
  unfold randomize_in_place.costProbability randomize_in_place.law randomize_in_place.cost
  simp only [randomize_in_place.ValidInput, valid, ↓reduceIte]
  change costProbability (execution nextChoice (randomize_in_place.initial heap (ref, n)))
    (fun state => Heap.cost heap state.heap clock) threshold = _
  rw [bridge]
  have contract := shuffle_law heap ref n valid
  have evaluate := contract (fun output => if threshold < (Heap.cost heap output.1 clock : ℝ≥0∞)
    then 1 else 0)
  simp only [randomize_in_place.ValidInput, valid, ↓reduceIte] at evaluate
  unfold callProbability
  rw [evaluate]
  change pmfExpected ((shuffleLaw heap ref 0 n).map (fun final => (final, ()))) _ = _
  rw [pmfExpected_map]
  unfold pmfExpected
  calc
    _ = ∑' final, shuffleLaw heap ref 0 n final *
        (if threshold < (if clock = "random_draws" ∨ clock = "swaps" then (n : ℝ≥0∞) else 0)
          then 1 else 0) := by
      apply tsum_congr
      intro final
      by_cases possible : final ∈ (shuffleLaw heap ref 0 n).support
      · simp [Heap.cost, shuffleLaw_clocks n heap ref 0 final possible clock]
      · have zero := (PMF.apply_eq_zero_iff _ _).2 possible
        simp [zero]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Every observation of the output interval has the expectation obtained by
choosing a uniform positional permutation. This permits repeated input values. -/
theorem uniform_permutation_expected (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) (reward : (Fin n → Int) → ℝ≥0∞) :
    randomize_in_place.expectedReturn heap (ref, n)
      (fun final _ => reward (prefixValues final ref 0 n)) =
      pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
        (fun permutation => reward (fun index => heap.read ref ((permutation index).val : Int))) := by
  rw [expected_return heap ref n valid]
  change pmfExpected (shuffleLaw heap ref 0 n) _ = _
  rw [shuffleLaw_uniform, permutationLaw_uniform]
  simp only [zero_add]

-- Main result: Correctness
/-- For distinct input values, each specified permutation of the output interval
has probability exactly `1 / n!`. Unrelated heap contents are unrestricted. -/
theorem uniform_permutation_probability (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef)
    (distinct : Function.Injective (fun index : Fin n => heap.read ref (index.val : Int)))
    (permutation : Equiv.Perm (Fin n)) :
    randomize_in_place.returnProbability heap (ref, n)
      (fun final _ => prefixValues final ref 0 n =
        fun index => heap.read ref ((permutation index).val : Int)) =
      (n.factorial : ℝ≥0∞)⁻¹ := by
  rw [return_probability heap ref n valid]
  change pmfExpected (shuffleLaw heap ref 0 n) _ = _
  let target : Fin n → Int := fun index => heap.read ref ((permutation index).val : Int)
  let reward : (Fin n → Int) → ℝ≥0∞ := fun values => if values = target then 1 else 0
  have uniform := shuffleLaw_uniform n heap ref 0 reward
  trans pmfExpected (shuffleLaw heap ref 0 n) (fun final => reward (prefixValues final ref 0 n))
  · apply congrArg (pmfExpected (shuffleLaw heap ref 0 n))
    funext final
    by_cases same : prefixValues final ref 0 n = target <;> simp [reward, target] at same ⊢
  rw [uniform]
  simp only [reward, target, zero_add]
  have unique (other : Equiv.Perm (Fin n)) :
      (fun index => heap.read ref ((other index).val : Int)) =
        (fun index => heap.read ref ((permutation index).val : Int)) ↔ other = permutation := by
    constructor
    · intro same
      apply Equiv.ext
      intro index
      exact distinct (congrFun same index)
    · intro same; subst other; rfl
  simp_rw [unique]
  simp [pmfExpected, permutationLaw_mass]

end ShuffleAnalysis
