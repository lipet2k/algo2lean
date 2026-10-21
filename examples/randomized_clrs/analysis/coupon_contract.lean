import Algo.coupon_collector.Points
import Algo.coupon_collector.Probability
import Algo.coupon_expectation.Analysis
import Algo2LeanProbability.CallObservations
import Algo2LeanProbability.CallRewards

/-!
Source-level coupon-collector analysis. Local loop rules connect generated
instructions with independent uniform coupon draws. The connection proves
almost-sure successful termination, exact set contents, the full-path mean
N H_N, and a geometric tail bound for the charged draw cost.
-/

noncomputable section
namespace CouponAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2LeanProbability MeasureTheory
open Algo.coupon_collector Algo.coupon_collector.Algo2LeanGenerated
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

local macro "advance" : tactic =>
  `(tactic| rw [callExpected_next nextChoice collect_coupons.outcome _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; simp_all <;> rfl))])

/-- Creating the result set preserves all caller data and starts it empty. -/
def emptyHeap (heap : Heap) : Heap := («set[Int]».create heap []).1

/-- With no coupon types to collect, the call allocates an empty set and returns
zero draws. The contract applies to every nonnegative heap/output reward. -/
theorem nonpositive_expected (heap : Heap) (n : Int) (nonpositive : n ≤ 0)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    collect_coupons.expectedReturn heap n reward = reward (emptyHeap heap) (heap.nextCollection, 0) := by
  have valid : «set[Int]».valid (emptyHeap heap) heap.nextCollection :=
    «set[Int]».valid_create heap []
  have notLess : ¬ 0 < n := by omega
  have size : «set[Int]».size (emptyHeap heap) heap.nextCollection = 0 := by
    change «set[Int]».size («set[Int]».create heap []).1 («set[Int]».create heap []).2 = 0
    simp [SetType.size, SetType.keys, OrderedElements.normalize]
  simp only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true,
    collect_coupons.initial, start]
  advance
  advance
  advance
  change callExpected nextChoice collect_coupons.outcome
    (.active (emptyHeap heap) (.fn_collect_coupons 4 _) []) _ = _
  advance
  simp only [notLess, decide_false]
  advance
  advance
  advance
  rw [callExpected_return nextChoice collect_coupons.outcome _ _ rfl]

/-- The zero-coupon law is normalized; no nontermination mass is discarded. -/
theorem nonpositive_law (heap : Heap) (n : Int) (nonpositive : n ≤ 0) :
    collect_coupons.HasLaw heap n (PMF.pure (emptyHeap heap, (heap.nextCollection, 0))) := by
  intro reward
  change _ = pmfExpected (PMF.pure _) reward
  rw [pmfExpected_pure]
  exact nonpositive_expected heap n nonpositive (fun final result => reward (final, result))

/-- The one-type result inserts coupon zero and charges exactly one draw. -/
def oneHeap (heap : Heap) : Heap :=
  («set[Int]».insert (emptyHeap heap) heap.nextCollection 0).tick "random_draws"

/-- One coupon type is collected on the first draw, with an exact joint reward
for the returned set, draw count, and caller-visible final heap. -/
theorem one_expected (heap : Heap)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    collect_coupons.expectedReturn heap 1 reward = reward (oneHeap heap) (heap.nextCollection, 1) := by
  have valid : «set[Int]».valid (emptyHeap heap) heap.nextCollection :=
    «set[Int]».valid_create heap []
  have empty : «set[Int]».entries (emptyHeap heap) heap.nextCollection = some [] := by
    change «set[Int]».entries («set[Int]».create heap []).1 («set[Int]».create heap []).2 = _
    simp [OrderedElements.normalize]
  have size : «set[Int]».size (emptyHeap heap) heap.nextCollection = 0 := by
    simp [SetType.size, SetType.keys, empty]
  have singleton : «set[Int]».entries (oneHeap heap) heap.nextCollection = some [0] := by
    change «set[Int]».entries («set[Int]».insert (emptyHeap heap) heap.nextCollection 0)
      heap.nextCollection = some [0]
    rw [SetType.entries_insert _ _ _ _ _ empty]
    rfl
  have validAfter : «set[Int]».valid (oneHeap heap) heap.nextCollection := by
    simp [SetType.valid, singleton]
  have sizeAfter : «set[Int]».size (oneHeap heap) heap.nextCollection = 1 := by
    simp [SetType.size, SetType.keys, singleton]
  simp only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true,
    collect_coupons.initial, start]
  advance
  advance
  advance
  change callExpected nextChoice collect_coupons.outcome
    (.active (emptyHeap heap) (.fn_collect_coupons 4 _) []) _ = _
  advance
  advance
  advance
  advance
  rw [callExpected_uniform nextChoice collect_coupons.outcome _ 0 1 _ rfl rfl (by norm_num)]
  norm_num [show Finset.Ico (0 : Int) 1 = {0} by decide]
  advance
  advance
  advance
  advance
  advance
  advance
  advance
  change callExpected nextChoice collect_coupons.outcome
    (.active (oneHeap heap) (.fn_collect_coupons 4 _) []) _ = _
  advance
  advance
  advance
  advance
  rw [callExpected_return nextChoice collect_coupons.outcome _ _ rfl]

/-- The reusable one-type contract keeps output, mutation, and cost together. -/
theorem one_law (heap : Heap) :
    collect_coupons.HasLaw heap 1 (PMF.pure (oneHeap heap, (heap.nextCollection, 1))) := by
  intro reward
  change _ = pmfExpected (PMF.pure _) reward
  rw [pmfExpected_pure]
  exact one_expected heap (fun final result => reward (final, result))

/-- Insert one sampled coupon into the existing set and charge its draw. -/
def drawStep (heap : Heap) (ref : CollectionRef) (coupon : Int) : Heap :=
  («set[Int]».insert heap ref coupon).tick "random_draws"

/-- Once enough types have been collected, the loop returns its current set
and draw count without further mutation or charges. -/
theorem collected_expected (state : Configuration) (ref : CollectionRef) (n draws : Int)
    (location : collect_coupons.At.collect state)
    (readSeen : collect_coupons.Local.seen state = some ref)
    (readCount : collect_coupons.Local.n state = some n)
    (readDraws : collect_coupons.Local.draws state = some draws)
    (valid : «set[Int]».valid state.heap ref)
    (complete : n ≤ («set[Int]».size state.heap ref : Int))
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    collect_coupons.expectedFrom state reward = reward state.heap (ref, draws) := by
  cases state with
  | done => cases location
  | active heap frame stack =>
      cases frame with
      | invalid => cases location
      | fn_collect_coupons pc s =>
          have counter : pc = 4 := by
            unfold collect_coupons.At.collect at location
            split at location <;> simp_all
          subst pc
          simp only [collect_coupons.Local.seen, collect_coupons.Local.n,
            collect_coupons.Local.draws, ↓reduceIte, Option.some.injEq] at readSeen readCount readDraws
          change «set[Int]».valid heap ref at valid
          change n ≤ («set[Int]».size heap ref : Int) at complete
          subst ref n draws
          have notLess : ¬ («set[Int]».size heap s.v1 : Int) < s.v0 := by omega
          simp only [collect_coupons.expectedFrom]
          advance
          simp only [notLess, decide_false]
          advance
          advance
          advance
          rw [callExpected_return nextChoice collect_coupons.outcome _ _ rfl]
          rfl

/-- A local loop iteration is one uniform average of the next loop states.
The statement uses only the named source location, local variables, and heap;
no prefix transcript or whole-program reachability is required. -/
theorem draw_iteration (state : Configuration) (ref : CollectionRef) (n draws : Int)
    (location : collect_coupons.At.collect state)
    (readSeen : collect_coupons.Local.seen state = some ref)
    (readCount : collect_coupons.Local.n state = some n)
    (readDraws : collect_coupons.Local.draws state = some draws)
    (valid : «set[Int]».valid state.heap ref)
    (incomplete : («set[Int]».size state.heap ref : Int) < n)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    ∃ following : Int → Configuration,
      (∀ coupon,
        collect_coupons.At.collect (following coupon) ∧
        collect_coupons.Local.seen (following coupon) = some ref ∧
        collect_coupons.Local.n (following coupon) = some n ∧
        collect_coupons.Local.draws (following coupon) = some (draws + 1) ∧
        (following coupon).heap = drawStep state.heap ref coupon) ∧
      collect_coupons.expectedFrom state reward =
        ∑ coupon ∈ Finset.Ico (0 : Int) n,
          collect_coupons.expectedFrom (following coupon) reward * (n.toNat : ℝ≥0∞)⁻¹ := by
  cases state with
  | done => cases location
  | active heap frame stack =>
      cases frame with
      | invalid => cases location
      | fn_collect_coupons pc s =>
          have counter : pc = 4 := by
            unfold collect_coupons.At.collect at location
            split at location <;> simp_all
          subst pc
          simp only [collect_coupons.Local.seen, collect_coupons.Local.n,
            collect_coupons.Local.draws, ↓reduceIte, Option.some.injEq] at readSeen readCount readDraws
          change «set[Int]».valid heap ref at valid
          change («set[Int]».size heap ref : Int) < n at incomplete
          subst ref n draws
          let following : Int → Configuration := fun coupon =>
            .active (drawStep heap s.v1 coupon) (.fn_collect_coupons 4
              { s with
                v2 := s.v2 + 1, v3 := coupon, t5 := true, t6 := (), t7 := s.v1,
                t8 := coupon, t9 := coupon, t10 := 0, t11 := s.v0 }) []
          refine ⟨following, ?_, ?_⟩
          · intro coupon
            exact ⟨trivial, rfl, rfl, rfl, rfl⟩
          · simp only [collect_coupons.expectedFrom]
            advance
            advance
            advance
            advance
            rw [callExpected_uniform nextChoice collect_coupons.outcome _ 0 s.v0 _ rfl rfl (by omega)]
            simp only [sub_zero]
            apply Finset.sum_congr rfl
            intro coupon member
            congr 1
            advance
            advance
            advance
            advance
            advance
            advance
            advance
            rfl

private def bounded (time : Nat) (state : Configuration)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) : ℝ≥0∞ :=
  Stopped.within (transition nextChoice) (completed collect_coupons.outcome)
    (returnReward collect_coupons.outcome (fun result => reward result.1 result.2)) time (some state)

private theorem bounded_next (time : Nat) (before after : Configuration)
    (absent : collect_coupons.outcome before = none)
    (moves : nextChoice before = .next after)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    bounded (time + 1) before reward = bounded time after reward := by
  have outside : ¬ completed collect_coupons.outcome (some before) := by
    rintro ⟨state, output, same, seen⟩
    cases same
    simp [absent] at seen
  unfold bounded
  rw [Stopped.within, if_neg outside]
  simp only [transition, moves, choiceLaw_next, PMF.toMeasure_pure]
  exact lintegral_dirac' _ Measurable.of_discrete

private theorem bounded_uniform (time : Nat) (state : Configuration)
    (lower upper : Int) (following : Int → Configuration)
    (absent : collect_coupons.outcome state = none)
    (draw : nextChoice state = .uniform lower upper following) (bounds : lower < upper)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    bounded (time + 1) state reward =
      ∑ coupon ∈ Finset.Ico lower upper,
        bounded time (following coupon) reward * ((upper - lower).toNat : ℝ≥0∞)⁻¹ := by
  have outside : ¬ completed collect_coupons.outcome (some state) := by
    rintro ⟨current, output, same, seen⟩
    cases same
    simp [absent] at seen
  unfold bounded
  rw [Stopped.within, if_neg outside]
  simp only [transition, draw, choiceLaw_uniform state lower upper following bounds]
  rw [← PMF.toMeasure_map (β := SampleState Configuration)
    (mβ := inferInstance) (fun coupon => (some (following coupon) : SampleState Configuration)) _
    Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete]
  exact uniformInt_expected lower upper bounds _

local macro "advance_bounded" : tactic =>
  `(tactic| rw [bounded_next _ _ _ rfl
    (by first | rfl | (change (if _ then _ else _) = _; simp_all <;> rfl))])

/-- The source's mutable set contains exactly the mathematical coupon types.
The insertion order is retained in the heap, while the finite-set view ignores it. -/
def Represents {n : Nat} (heap : Heap) (ref : CollectionRef) (seen : Finset (Fin (n + 1))) : Prop :=
  «set[Int]».valid heap ref ∧
    («set[Int]».keys heap ref).toFinset = seen.image (fun coupon => (coupon.val : Int))

private theorem coupon_injective (n : Nat) :
    Function.Injective (fun coupon : Fin (n + 1) => (coupon.val : Int)) := by
  intro first second equal
  apply Fin.ext
  change (first.val : Int) = second.val at equal
  exact_mod_cast equal

theorem Represents.size {n : Nat} {heap : Heap} {ref : CollectionRef}
    {seen : Finset (Fin (n + 1))} (rep : Represents heap ref seen) :
    «set[Int]».size heap ref = seen.card := by
  have count := List.toFinset_card_of_nodup («set[Int]».keys_nodup heap ref)
  rw [rep.2, Finset.card_image_of_injective _ (coupon_injective n)] at count
  exact count.symm

theorem Represents.draw {n : Nat} {heap : Heap} {ref : CollectionRef}
    {seen : Finset (Fin (n + 1))} (rep : Represents heap ref seen) (coupon : Fin (n + 1)) :
    Represents (drawStep heap ref coupon.val) ref (insert coupon seen) := by
  change «set[Int]».valid («set[Int]».insert heap ref coupon.val) ref ∧ _
  refine ⟨«set[Int]».valid_insert heap ref coupon.val rep.1, ?_⟩
  change («set[Int]».keys («set[Int]».insert heap ref coupon.val) ref).toFinset = _
  rw [SetType.keys_insert _ _ _ _ rep.1]
  by_cases present : (coupon.val : Int) ∈ «set[Int]».keys heap ref
  · have member : coupon ∈ seen := by
      have mapped : (coupon.val : Int) ∈ seen.image (fun index => (index.val : Int)) := by
        rw [← rep.2]
        simpa using present
      obtain ⟨index, member, equal⟩ := Finset.mem_image.mp mapped
      exact coupon_injective n equal ▸ member
    simp [OrderedElements.insert, present, rep.2, member]
  · simp [OrderedElements.insert, present, rep.2, Finset.image_insert]

private theorem sum_fin_interval (n : Nat) (reward : Int → ℝ≥0∞) :
    (∑ coupon ∈ Finset.Ico (0 : Int) (n + 1), reward coupon) =
      ∑ coupon : Fin (n + 1), reward coupon.val := by
  symm
  apply Finset.sum_bij (fun coupon _ => (coupon.val : Int))
  · intro coupon _
    simp only [Finset.mem_Ico]
    exact ⟨by omega, by exact_mod_cast coupon.isLt⟩
  · intro first _ second _ equal
    exact coupon_injective n equal
  · intro value member
    have bounds := Finset.mem_Ico.mp member
    refine ⟨⟨value.toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [Int.toNat_of_nonneg bounds.1]
  · intro coupon _
    rfl

private theorem bounded_zero_active (heap : Heap) (frame : Frame)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    bounded 0 (.active heap frame []) reward = 0 := by
  have outside : ¬ completed collect_coupons.outcome (some (.active heap frame [])) := by
    rintro ⟨state, output, same, seen⟩
    cases same
    cases seen
  simp only [bounded, Stopped.within, if_neg outside]

/-- Completion and incompletion partition every fixed-length coupon experiment. -/
theorem completion_partition (n time : Nat) (seen : Finset (Fin (n + 1))) :
    pmfExpected (afterDraws n seen time) (fun final => if final = Finset.univ then 1 else 0) +
      pmfExpected (afterDraws n seen time) (fun final => if final ≠ Finset.univ then 1 else 0) = 1 := by
  unfold pmfExpected
  rw [← ENNReal.tsum_add]
  convert (afterDraws n seen time).tsum_coe using 1
  apply tsum_congr
  intro final
  by_cases full : final = Finset.univ <;> simp [full]

private theorem callExpected_eq_bounded (state : Configuration)
    (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
    callExpected nextChoice collect_coupons.outcome state (fun result => reward result.1 result.2) =
      ⨆ time : Nat, bounded (12 * time + 4) state reward := by
  change (⨆ time : Nat, bounded time state reward) = _
  apply le_antisymm
  · apply iSup_le
    intro time
    exact (Stopped.within_mono_time (transition nextChoice) (completed collect_coupons.outcome)
      (returnReward collect_coupons.outcome (fun result => reward result.1 result.2))
      (show time ≤ 12 * time + 4 by omega) (some state)).trans
      (le_iSup (fun time => bounded (12 * time + 4) state reward) time)
  · exact iSup_le (fun time => le_iSup (fun time => bounded time state reward) (12 * time + 4))

/-- The four guarantees needed by coupon callers, expressed at the named loop
location with the source's set reference and draw count. -/
private structure CollectionLoop (state : Configuration) (n : Nat)
    (ref : CollectionRef) (draws : Int) (seen : Finset (Fin (n + 1))) : Prop where
  terminates : collect_coupons.expectedFrom state (fun _ _ => 1) = 1
  draws_at_most (budget : Nat) :
    collect_coupons.expectedFrom state
      (fun _ result => if result.2 ≤ draws + budget then 1 else 0) =
      pmfExpected (afterDraws n seen budget) (fun final => if final = Finset.univ then 1 else 0)
  clock_reward (initial : Heap) (nonnegative : 0 ≤ draws)
      (accounted : state.heap.clocks "random_draws" = initial.clocks "random_draws" + draws.toNat)
      (reward : ℝ≥0∞ → ℝ≥0∞) :
    collect_coupons.expectedFrom state (fun final _ => reward (Heap.cost initial final "random_draws")) =
      collect_coupons.expectedFrom state (fun _ result => reward result.2.toNat)
  agree_completed (first second : Heap → (CollectionRef × Int) → ℝ≥0∞)
      (agree : ∀ final count, Represents final ref (Finset.univ : Finset (Fin (n + 1))) →
        first final (ref, count) = second final (ref, count)) :
    collect_coupons.expectedFrom state first = collect_coupons.expectedFrom state second

/-- The mutable source loop realizes the coupon experiment from any named loop
state. The contract is independent of temporary values and the caller's stack;
finite instruction bounds are used only inside its proof. -/
private theorem collection_loop (state : Configuration) (n : Nat)
    (ref : CollectionRef) (draws : Int) (seen : Finset (Fin (n + 1)))
    (location : collect_coupons.At.collect state)
    (readCount : collect_coupons.Local.n state = some (n + 1 : Int))
    (readSet : collect_coupons.Local.seen state = some ref)
    (readDraws : collect_coupons.Local.draws state = some draws)
    (rep : Represents state.heap ref seen) : CollectionLoop state n ref draws seen := by
  have bounded_return (time : Nat) (heap : Heap) (result : CollectionRef × Int)
      (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
      bounded time (.done heap (.fn_collect_coupons result)) reward = reward heap result := by
    have done : completed collect_coupons.outcome (some (.done heap (.fn_collect_coupons result))) :=
      ⟨_, (heap, result), rfl, rfl⟩
    cases time <;> simp only [bounded, Stopped.within, if_pos done] <;> rfl

  have bounded_collected (time : Nat) (heap : Heap) (s : State_collect_coupons)
      (valid : «set[Int]».valid heap s.v1)
      (complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int))
      (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
      bounded (time + 4) (.active heap (.fn_collect_coupons 4 s) []) reward =
        reward heap (s.v1, s.v2) := by
    have notLess : ¬ («set[Int]».size heap s.v1 : Int) < s.v0 := by omega
    advance_bounded
    simp only [notLess, decide_false]
    advance_bounded
    advance_bounded
    advance_bounded
    exact bounded_return time heap (s.v1, s.v2) reward

  let nextLocals (s : State_collect_coupons) (coupon : Int) : State_collect_coupons :=
    { s with
      v2 := s.v2 + 1, v3 := coupon, t5 := true, t6 := (), t7 := s.v1,
      t8 := coupon, t9 := coupon, t10 := 0, t11 := s.v0 }

  have bounded_iteration (time : Nat) (heap : Heap) (s : State_collect_coupons)
      (valid : «set[Int]».valid heap s.v1)
      (incomplete : («set[Int]».size heap s.v1 : Int) < s.v0)
      (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
      bounded (time + 12) (.active heap (.fn_collect_coupons 4 s) []) reward =
        ∑ coupon ∈ Finset.Ico (0 : Int) s.v0,
          bounded time (.active (drawStep heap s.v1 coupon)
            (.fn_collect_coupons 4 (nextLocals s coupon)) []) reward * (s.v0.toNat : ℝ≥0∞)⁻¹ := by
    advance_bounded
    advance_bounded
    advance_bounded
    advance_bounded
    rw [bounded_uniform _ _ 0 s.v0 _ rfl rfl (by omega)]
    simp only [sub_zero]
    apply Finset.sum_congr rfl
    intro coupon _
    congr 1
    advance_bounded
    advance_bounded
    advance_bounded
    advance_bounded
    advance_bounded
    advance_bounded
    advance_bounded
    rfl

  have bounded_collected_probability (time n : Nat) (heap : Heap)
      (s : State_collect_coupons) (seen : Finset (Fin (n + 1)))
      (rep : Represents heap s.v1 seen) (count : s.v0 = n + 1) :
      bounded (12 * time + 4) (.active heap (.fn_collect_coupons 4 s) []) (fun _ _ => 1) =
        pmfExpected (afterDraws n seen time) (fun final => if final = Finset.univ then 1 else 0) := by
    induction time generalizing heap s seen with
    | zero =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [show 12 * 0 + 4 = 0 + 4 by omega, bounded_collected 0 heap s rep.1 complete]
          simp [afterDraws, full]
        · have valid := rep.1
          have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          advance_bounded
          advance_bounded
          advance_bounded
          advance_bounded
          rw [bounded_zero_active]
          simp [afterDraws, full]
    | succ time ih =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [bounded_collected (12 * (time + 1)) heap s rep.1 complete]
          simp [full]
        · have valid := rep.1
          have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          rw [show 12 * (time + 1) + 4 = (12 * time + 4) + 12 by omega,
            bounded_iteration (12 * time + 4) heap s rep.1 incomplete, count,
            sum_fin_interval]
          rw [afterDraws, pmfExpected_bind]
          have width : ((n : Int) + 1).toNat = n + 1 := by omega
          simp only [pmfExpected, tsum_fintype, PMF.uniformOfFintype_apply, Fintype.card_fin,
            width, Nat.cast_add, Nat.cast_one]
          apply Finset.sum_congr rfl
          intro coupon _
          rw [mul_comm]
          congr 1
          simpa only [pmfExpected, tsum_fintype] using
            ih (drawStep heap s.v1 coupon.val) (nextLocals s coupon.val)
              (insert coupon seen) (rep.draw coupon) count

  have loop_terminates (n : Nat) (heap : Heap) (s : State_collect_coupons)
      (seen : Finset (Fin (n + 1))) (rep : Represents heap s.v1 seen)
      (count : s.v0 = n + 1) :
      callExpected nextChoice collect_coupons.outcome
        (.active heap (.fn_collect_coupons 4 s) []) (fun _ => 1) = 1 := by
    let result := callExpected nextChoice collect_coupons.outcome
      (.active heap (.fn_collect_coupons 4 s) []) (fun _ => 1)
    have upper : result ≤ 1 := by
      apply Stopped.expected_le _ _ _ (fun _ => 1)
      · intro state atBoundary
        obtain ⟨current, output, same, outputAt⟩ := atBoundary
        subst state
        simp [returnReward, outputAt]
      · intro state _
        simp
    have lower (time : Nat) : 1 ≤ result + pmfExpected (afterDraws n seen time)
        (fun final => if final ≠ Finset.univ then 1 else 0) := by
      calc
        1 = pmfExpected (afterDraws n seen time) (fun final => if final = Finset.univ then 1 else 0) +
            pmfExpected (afterDraws n seen time) (fun final => if final ≠ Finset.univ then 1 else 0) :=
          (completion_partition n time seen).symm
        _ ≤ _ := ?_
      apply add_le_add _ le_rfl
      rw [← bounded_collected_probability time n heap s seen rep count]
      exact le_iSup (fun time => bounded time (.active heap (.fn_collect_coupons 4 s) [])
        (fun _ _ => 1)) (12 * time + 4)
    have limit := Filter.Tendsto.const_add result (incomplete_probability_tendsto_zero n seen)
    have above : 1 ≤ result := by
      simpa only [add_zero] using ge_of_tendsto' limit lower
    exact le_antisymm upper above

  have bounded_late_return (time n : Nat) (heap : Heap)
      (s : State_collect_coupons) (seen : Finset (Fin (n + 1)))
      (rep : Represents heap s.v1 seen) (count : s.v0 = n + 1)
      (threshold : Int) (late : threshold < s.v2) :
      bounded (12 * time + 4) (.active heap (.fn_collect_coupons 4 s) [])
        (fun _ result => if result.2 ≤ threshold then 1 else 0) = 0 := by
    induction time generalizing heap s seen with
    | zero =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [show 12 * 0 + 4 = 0 + 4 by omega, bounded_collected 0 heap s rep.1 complete]
          simp [show ¬s.v2 ≤ threshold by omega]
        · have valid := rep.1
          have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          advance_bounded
          advance_bounded
          advance_bounded
          advance_bounded
          exact bounded_zero_active _ _ _
    | succ time ih =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [bounded_collected (12 * (time + 1)) heap s rep.1 complete]
          simp [show ¬s.v2 ≤ threshold by omega]
        · have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          rw [show 12 * (time + 1) + 4 = (12 * time + 4) + 12 by omega,
            bounded_iteration (12 * time + 4) heap s rep.1 incomplete, count,
            sum_fin_interval]
          apply Finset.sum_eq_zero
          intro coupon _
          rw [ih (drawStep heap s.v1 coupon.val) (nextLocals s coupon.val)
            (insert coupon seen) (rep.draw coupon) count (by change threshold < s.v2 + 1; omega)]
          simp

  have bounded_draw_bound (time budget n : Nat) (heap : Heap)
      (s : State_collect_coupons) (seen : Finset (Fin (n + 1)))
      (rep : Represents heap s.v1 seen) (count : s.v0 = n + 1) :
      bounded (12 * time + 4) (.active heap (.fn_collect_coupons 4 s) [])
        (fun _ result => if result.2 ≤ s.v2 + budget then 1 else 0) =
        pmfExpected (afterDraws n seen (min time budget))
          (fun final => if final = Finset.univ then 1 else 0) := by
    induction time generalizing heap s seen budget with
    | zero =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [show 12 * 0 + 4 = 0 + 4 by omega, bounded_collected 0 heap s rep.1 complete]
          simp [full, show s.v2 ≤ s.v2 + budget by omega]
        · have valid := rep.1
          have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          advance_bounded
          advance_bounded
          advance_bounded
          advance_bounded
          rw [bounded_zero_active]
          simp [afterDraws, full]
    | succ time ih =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [bounded_collected (12 * (time + 1)) heap s rep.1 complete]
          simp [full, show s.v2 ≤ s.v2 + budget by omega]
        · have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          rw [show 12 * (time + 1) + 4 = (12 * time + 4) + 12 by omega,
            bounded_iteration (12 * time + 4) heap s rep.1 incomplete, count,
            sum_fin_interval]
          cases budget with
          | zero =>
              simp only [Nat.cast_zero, add_zero, Nat.min_zero, afterDraws, pmfExpected_pure,
                if_neg full]
              apply Finset.sum_eq_zero
              intro coupon _
              rw [bounded_late_return time n (drawStep heap s.v1 coupon.val)
                (nextLocals s coupon.val) (insert coupon seen) (rep.draw coupon) count s.v2
                (by change s.v2 < s.v2 + 1; omega)]
              simp
          | succ budget =>
              rw [show min (time + 1) (budget + 1) = min time budget + 1 by omega,
                afterDraws, pmfExpected_bind]
              have width : ((n : Int) + 1).toNat = n + 1 := by omega
              simp only [pmfExpected, tsum_fintype, PMF.uniformOfFintype_apply,
                Fintype.card_fin, width, Nat.cast_add, Nat.cast_one]
              apply Finset.sum_congr rfl
              intro coupon _
              have cutoff : s.v2 + ((budget : Int) + 1) =
                  (nextLocals s coupon.val).v2 + budget := by
                change s.v2 + ((budget : Int) + 1) = s.v2 + 1 + budget
                omega
              rw [cutoff, mul_comm]
              congr 1
              simpa only [pmfExpected, tsum_fintype] using
                ih budget (drawStep heap s.v1 coupon.val) (nextLocals s coupon.val)
                  (insert coupon seen) (rep.draw coupon) count

  have loop_draw_bound (budget n : Nat) (heap : Heap)
      (s : State_collect_coupons) (seen : Finset (Fin (n + 1)))
      (rep : Represents heap s.v1 seen) (count : s.v0 = n + 1) :
      callExpected nextChoice collect_coupons.outcome (.active heap (.fn_collect_coupons 4 s) [])
        (fun result => if result.2.2 ≤ s.v2 + budget then 1 else 0) =
        pmfExpected (afterDraws n seen budget) (fun final => if final = Finset.univ then 1 else 0) := by
    rw [callExpected_eq_bounded _ (fun _ result => if result.2 ≤ s.v2 + budget then 1 else 0)]
    simp_rw [bounded_draw_bound _ budget n heap s seen rep count]
    apply le_antisymm
    · apply iSup_le
      intro time
      rw [← bounded_collected_probability (min time budget) n heap s seen rep count,
        ← bounded_collected_probability budget n heap s seen rep count]
      exact Stopped.within_mono_time (transition nextChoice) (completed collect_coupons.outcome)
        (returnReward collect_coupons.outcome (fun _ => 1)) (by omega) _
    · simpa using le_iSup (fun time => pmfExpected (afterDraws n seen (min time budget))
        (fun final => if final = Finset.univ then 1 else 0)) budget

  have bounded_incomplete (heap : Heap) (s : State_collect_coupons)
      (valid : «set[Int]».valid heap s.v1)
      (incomplete : («set[Int]».size heap s.v1 : Int) < s.v0)
      (reward : Heap → (CollectionRef × Int) → ℝ≥0∞) :
      bounded 4 (.active heap (.fn_collect_coupons 4 s) []) reward = 0 := by
    advance_bounded
    advance_bounded
    advance_bounded
    advance_bounded
    exact bounded_zero_active _ _ _

  have bounded_clock_reward (time n : Nat) (initial heap : Heap)
      (s : State_collect_coupons) (seen : Finset (Fin (n + 1)))
      (rep : Represents heap s.v1 seen) (count : s.v0 = n + 1)
      (nonnegative : 0 ≤ s.v2)
      (accounted : heap.clocks "random_draws" = initial.clocks "random_draws" + s.v2.toNat)
      (reward : ℝ≥0∞ → ℝ≥0∞) :
      bounded (12 * time + 4) (.active heap (.fn_collect_coupons 4 s) [])
        (fun final _ => reward (Heap.cost initial final "random_draws")) =
      bounded (12 * time + 4) (.active heap (.fn_collect_coupons 4 s) [])
        (fun _ result => reward result.2.toNat) := by
    induction time generalizing heap s seen with
    | zero =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [show 12 * 0 + 4 = 0 + 4 by omega,
            bounded_collected 0 heap s rep.1 complete,
            bounded_collected 0 heap s rep.1 complete]
          simp [Heap.cost, accounted]
        · have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          rw [show 12 * 0 + 4 = 4 by omega, bounded_incomplete heap s rep.1 incomplete,
            bounded_incomplete heap s rep.1 incomplete]
    | succ time ih =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [bounded_collected (12 * (time + 1)) heap s rep.1 complete,
            bounded_collected (12 * (time + 1)) heap s rep.1 complete]
          simp [Heap.cost, accounted]
        · have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          rw [show 12 * (time + 1) + 4 = (12 * time + 4) + 12 by omega,
            bounded_iteration (12 * time + 4) heap s rep.1 incomplete,
            bounded_iteration (12 * time + 4) heap s rep.1 incomplete, count,
            sum_fin_interval, sum_fin_interval]
          apply Finset.sum_congr rfl
          intro coupon _
          congr 1
          apply ih (drawStep heap s.v1 coupon.val) (nextLocals s coupon.val)
            (insert coupon seen) (rep.draw coupon) count
          · change 0 ≤ s.v2 + 1
            omega
          · simp only [drawStep, Heap.clocks_tick_same, SetType.insert_clocks, nextLocals]
            rw [accounted]
            omega

  have bounded_agree_completed (time n : Nat) (heap : Heap)
      (s : State_collect_coupons) (seen : Finset (Fin (n + 1)))
      (rep : Represents heap s.v1 seen) (count : s.v0 = n + 1)
      (first second : Heap → (CollectionRef × Int) → ℝ≥0∞)
      (agree : ∀ final draws, Represents final s.v1 (Finset.univ : Finset (Fin (n + 1))) →
        first final (s.v1, draws) = second final (s.v1, draws)) :
      bounded (12 * time + 4) (.active heap (.fn_collect_coupons 4 s) []) first =
        bounded (12 * time + 4) (.active heap (.fn_collect_coupons 4 s) []) second := by
    induction time generalizing heap s seen with
    | zero =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [show 12 * 0 + 4 = 0 + 4 by omega,
            bounded_collected 0 heap s rep.1 complete,
            bounded_collected 0 heap s rep.1 complete]
          exact agree heap s.v2 (full ▸ rep)
        · have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          rw [show 12 * 0 + 4 = 4 by omega,
            bounded_incomplete heap s rep.1 incomplete,
            bounded_incomplete heap s rep.1 incomplete]
    | succ time ih =>
        by_cases full : seen = Finset.univ
        · have complete : s.v0 ≤ («set[Int]».size heap s.v1 : Int) := by
            rw [rep.size, count, full]
            simp
          rw [bounded_collected (12 * (time + 1)) heap s rep.1 complete,
            bounded_collected (12 * (time + 1)) heap s rep.1 complete]
          exact agree heap s.v2 (full ▸ rep)
        · have incomplete : («set[Int]».size heap s.v1 : Int) < s.v0 := by
            rw [rep.size, count]
            have small := (Finset.card_lt_iff_ne_univ seen).2 full
            simp only [Fintype.card_fin] at small
            exact_mod_cast small
          rw [show 12 * (time + 1) + 4 = (12 * time + 4) + 12 by omega,
            bounded_iteration (12 * time + 4) heap s rep.1 incomplete,
            bounded_iteration (12 * time + 4) heap s rep.1 incomplete, count,
            sum_fin_interval, sum_fin_interval]
          apply Finset.sum_congr rfl
          intro coupon _
          congr 1
          exact ih (drawStep heap s.v1 coupon.val) (nextLocals s coupon.val)
            (insert coupon seen) (rep.draw coupon) count agree
  cases state with
  | done => cases location
  | active heap frame stack =>
      cases frame <;> try cases location
      case fn_collect_coupons pc s =>
        have counter : pc = 4 := by
          unfold collect_coupons.At.collect at location
          split at location <;> simp_all
        subst pc
        simp [collect_coupons.Local.n, collect_coupons.Local.seen,
          collect_coupons.Local.draws] at readCount readSet readDraws
        change Represents heap ref seen at rep
        have represented : Represents heap s.v1 seen := by simpa only [readSet] using rep
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact loop_terminates n heap s seen represented readCount
        · intro budget
          simpa only [collect_coupons.expectedFrom, readDraws] using
            loop_draw_bound budget n heap s seen represented readCount
        · intro initial nonnegative accounted reward
          change callExpected nextChoice collect_coupons.outcome
            (.active heap (.fn_collect_coupons 4 s) [])
              (fun result => reward (Heap.cost initial result.1 "random_draws")) =
            callExpected nextChoice collect_coupons.outcome
              (.active heap (.fn_collect_coupons 4 s) []) (fun result => reward result.2.2.toNat)
          rw [callExpected_eq_bounded _ (fun final _ => reward (Heap.cost initial final "random_draws")),
            callExpected_eq_bounded _ (fun _ result => reward result.2.toNat)]
          apply iSup_congr
          intro time
          exact bounded_clock_reward time n initial heap s seen represented readCount
            (by simpa only [readDraws] using nonnegative)
            (by simpa only [Config.heap, readDraws] using accounted) reward
        · intro first second agree
          change callExpected nextChoice collect_coupons.outcome
            (.active heap (.fn_collect_coupons 4 s) []) (fun result => first result.1 result.2) =
            callExpected nextChoice collect_coupons.outcome
              (.active heap (.fn_collect_coupons 4 s) []) (fun result => second result.1 result.2)
          rw [callExpected_eq_bounded _ first, callExpected_eq_bounded _ second]
          apply iSup_congr
          intro time
          apply bounded_agree_completed time n heap s seen represented readCount first second
          simpa only [readSet] using agree

/-- The newly allocated set represents the empty coupon collection. -/
theorem represents_empty (heap : Heap) (n : Nat) :
    Represents (emptyHeap heap) heap.nextCollection (∅ : Finset (Fin (n + 1))) := by
  refine ⟨«set[Int]».valid_create heap [], ?_⟩
  change («set[Int]».keys («set[Int]».create heap []).1
    («set[Int]».create heap []).2).toFinset = _
  simp [SetType.keys, OrderedElements.normalize]

/-- For every positive number of coupon types, collection terminates with
probability one; arbitrarily long executions retain their true probability. -/
theorem positive_terminates (heap : Heap) (n : Nat) :
    collect_coupons.terminationProbability heap (n + 1) = 1 := by
  rw [collect_coupons.terminationProbability,
    collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial]
  simp only [if_true, collect_coupons.expectedReturn, collect_coupons.ValidInput,
    collect_coupons.initial, start]
  advance
  advance
  advance
  have loop := collection_loop
    (.active (emptyHeap heap) (.fn_collect_coupons 4
      {v0 := (n : Int) + 1, v1 := heap.nextCollection, t12 := heap.nextCollection}) [])
    n heap.nextCollection 0 ∅ trivial rfl rfl rfl (represents_empty heap n)
  exact loop.terminates

/-- The source program returns by its tth charged draw with exactly the
probability that t independent uniform draws contain every coupon type. -/
theorem draws_at_most (heap : Heap) (n budget : Nat) :
    collect_coupons.returnProbability heap (n + 1) (fun _ result => result.2 ≤ budget) =
      pmfExpected (afterDraws n ∅ budget) (fun final => if final = Finset.univ then 1 else 0) := by
  rw [collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial]
  simp only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true,
    collect_coupons.initial, start]
  advance
  advance
  advance
  have loop := collection_loop
    (.active (emptyHeap heap) (.fn_collect_coupons 4
      {v0 := (n : Int) + 1, v1 := heap.nextCollection, t12 := heap.nextCollection}) [])
    n heap.nextCollection 0 ∅ trivial rfl rfl rfl (represents_empty heap n)
  have bound := loop.draws_at_most budget
  simp only [collect_coupons.expectedFrom, zero_add, emptyHeap] at bound
  convert bound using 1
  congr 1
  funext result
  by_cases within : result.2.2 ≤ (budget : Int) <;> simp [within]


/-- The returned draw count and the caller-visible draw counter describe the
same work, for every nonnegative reward, including nonlinear moments. -/
theorem return_clock_reward (heap : Heap) (n : Nat) (reward : ℝ≥0∞ → ℝ≥0∞) :
    collect_coupons.expectedReturn heap (n + 1)
      (fun final _ => reward (Heap.cost heap final "random_draws")) =
    collect_coupons.expectedReturn heap (n + 1) (fun _ result => reward result.2.toNat) := by
  simp only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true,
    collect_coupons.initial, start]
  advance
  advance
  advance
  conv_rhs =>
    rw [callExpected_next nextChoice collect_coupons.outcome _ _ rfl (by rfl)]
    rw [callExpected_next nextChoice collect_coupons.outcome _ _ rfl (by rfl)]
    rw [callExpected_next nextChoice collect_coupons.outcome _ _ rfl (by rfl)]
  have loop := collection_loop
    (.active (emptyHeap heap) (.fn_collect_coupons 4
      {v0 := (n : Int) + 1, v1 := heap.nextCollection, t12 := heap.nextCollection}) [])
    n heap.nextCollection 0 ∅ trivial rfl rfl rfl (represents_empty heap n)
  exact loop.clock_reward heap (by norm_num) (by simp [Config.heap, emptyHeap]) reward


private theorem clock_step {before after : Configuration} (transition : Step before after)
    (clock : String) : before.heap.clocks clock ≤ after.heap.clocks clock := by
  have resumed (heap : Heap) (result : Result) (stack : Stack) :
      (resumeConfig heap result stack).heap = heap := by
    cases stack <;> rfl
  cases transition with
  | collect_coupons_pc1 heap locals stack defined =>
      change heap.clocks clock ≤ (resumeConfig heap (.fn_collect_coupons locals.t4) stack).heap.clocks clock
      rw [resumed]
  | _ => simp [Config.heap, Heap.tick] <;> split_ifs <;> omega

private theorem outcome_halts (state : Configuration) (output : Heap × (CollectionRef × Int))
    (observed : collect_coupons.outcome state = some output) : nextChoice state = .halt := by
  cases state with
  | done heap result => rfl
  | active heap frame stack => simp [collect_coupons.outcome] at observed

private theorem outcome_cost (heap : Heap) (clock : String) (state : Configuration)
    (output : Heap × (CollectionRef × Int)) (observed : collect_coupons.outcome state = some output) :
    Heap.cost heap state.heap clock = Heap.cost heap output.1 clock := by
  cases state with
  | done final result =>
      cases result
      simp only [collect_coupons.outcome, Option.some.injEq] at observed
      subst output
      rfl
  | active heap frame stack => simp [collect_coupons.outcome] at observed

private theorem completes (heap : Heap) (n : Nat) :
    callProbability nextChoice collect_coupons.outcome
      (collect_coupons.initial heap (n + 1)) (fun _ => True) = 1 := by
  have terminates := positive_terminates heap n
  rw [collect_coupons.terminationProbability,
    collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial] at terminates
  simpa only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true,
    callProbability] using terminates

/-- Every measurable nonnegative function of the full execution's draw cost
has the same expectation as that function of the returned number of draws. -/
theorem total_clock_reward (heap : Heap) (n : Nat)
    (reward : ℝ≥0∞ → ℝ≥0∞) (measurable : Measurable reward) :
    expected (collect_coupons.law heap (n + 1))
      ((collect_coupons.cost heap "random_draws").map reward measurable) =
    collect_coupons.expectedReturn heap (n + 1) (fun _ result => reward result.2.toNat) := by
  have bridge := expected_total_eq_callExpected nextChoice collect_coupons.outcome
    outcome_halts (collect_coupons.initial heap (n + 1))
    (fun state => Heap.cost heap state.heap "random_draws")
    (fun output => Heap.cost heap output.1 "random_draws")
    (fun before after allowed => Nat.sub_le_sub_right
      (clock_step (choice_step.mp allowed) "random_draws") _)
    (outcome_cost heap "random_draws") (completes heap n) reward measurable
  have source : expected (collect_coupons.law heap (n + 1))
      ((collect_coupons.cost heap "random_draws").map reward measurable) =
      collect_coupons.expectedReturn heap (n + 1)
        (fun final _ => reward (Heap.cost heap final "random_draws")) := by
    simpa only [collect_coupons.law, collect_coupons.cost,
      collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true] using bridge
  exact source.trans (return_clock_reward heap n reward)

/-- The full-path draw-cost event agrees with the returned draw-count event.
The equality includes all paths and is justified by almost-sure termination. -/
theorem cost_tail_return (heap : Heap) (n budget : Nat) :
    collect_coupons.costProbability heap (n + 1) "random_draws" budget =
      collect_coupons.returnProbability heap (n + 1) (fun _ result => budget < result.2.toNat) := by
  have bridge := costProbability_eq_callProbability nextChoice collect_coupons.outcome
    outcome_halts (collect_coupons.initial heap (n + 1))
    (fun state => Heap.cost heap state.heap "random_draws")
    (fun output => Heap.cost heap output.1 "random_draws")
    (fun before after allowed => Nat.sub_le_sub_right
      (clock_step (choice_step.mp allowed) "random_draws") _)
    (outcome_cost heap "random_draws") (completes heap n) (budget : ℝ≥0∞)
  have source : collect_coupons.costProbability heap (n + 1) "random_draws" budget =
      collect_coupons.expectedReturn heap (n + 1)
        (fun final _ => if (budget : ℝ≥0∞) < (Heap.cost heap final "random_draws" : ℝ≥0∞) then 1 else 0) := by
    simpa only [collect_coupons.costProbability, collect_coupons.law, collect_coupons.cost,
      Algo2LeanProbability.costProbability, collect_coupons.expectedReturn,
      collect_coupons.ValidInput, if_true, callProbability] using bridge
  rw [source, return_clock_reward heap n (fun value => if (budget : ℝ≥0∞) < value then 1 else 0),
    collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial]
  congr 1
  funext final result
  simp only [Nat.cast_lt]
  by_cases after : budget < result.2.toNat <;> simp [after]

/-- The probability of needing more than t draws is exactly the probability
that the independent t-draw sample still misses a coupon type. -/
theorem draws_more_than (heap : Heap) (n budget : Nat) :
    collect_coupons.returnProbability heap (n + 1) (fun _ result => budget < result.2.toNat) =
      pmfExpected (afterDraws n ∅ budget) (fun final => if final ≠ Finset.univ then 1 else 0) := by
  have partition : collect_coupons.returnProbability heap (n + 1) (fun _ result => result.2 ≤ budget) +
      collect_coupons.returnProbability heap (n + 1) (fun _ result => budget < result.2.toNat) = 1 := by
    rw [collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial,
      collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial]
    simp only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true]
    rw [← callExpected_add]
    have finished : callExpected nextChoice collect_coupons.outcome
        (collect_coupons.initial heap (n + 1)) (fun _ => 1) = 1 := by
      simpa only [callProbability, if_true] using completes heap n
    convert finished using 1
    congr 1
    funext result
    by_cases before : result.2.2 ≤ budget
    · have notAfter : ¬ budget < result.2.2.toNat := by omega
      simp [before, notAfter]
    · have after : budget < result.2.2.toNat := by omega
      simp [before, after]
  rw [draws_at_most heap n budget] at partition
  have finite : pmfExpected (afterDraws n ∅ budget)
      (fun final => if final = Finset.univ then 1 else 0) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ _ + collect_coupons.returnProbability heap (n + 1)
        (fun _ result => budget < result.2.toNat) := le_self_add
      _ = 1 := partition
  exact (ENNReal.add_right_inj finite).mp
    (partition.trans (completion_partition n budget ∅).symm)

/-- The exact whole-execution draw tail, including the null set of divergent
paths, is the missing-coupon probability in the finite independent model. -/
theorem cost_tail_exact (heap : Heap) (n budget : Nat) :
    collect_coupons.costProbability heap (n + 1) "random_draws" budget =
      pmfExpected (afterDraws n ∅ budget) (fun final => if final ≠ Finset.univ then 1 else 0) := by
  rw [cost_tail_return, draws_more_than]

/-- After t draws among N coupon types, the probability of further work is at
most N(1−1/N)^t. This is a whole-path runtime guarantee. -/
theorem running_time_tail_succ (heap : Heap) (n budget : Nat) :
    collect_coupons.costProbability heap (n + 1) "random_draws" budget ≤
      (n + 1 : ℝ≥0∞) * ((n : ℝ≥0∞) / (n + 1)) ^ budget := by
  rw [cost_tail_exact]
  exact incomplete_probability_le n budget

/-- The exact expected draw count is N H_N. This expectation is unconditional;
the source program's almost-sure successful termination is proved above. -/
theorem expected_return_draws (heap : Heap) (n : Nat) :
    collect_coupons.expectedReturn heap (n + 1) (fun _ result => (result.2.toNat : ℝ≥0∞)) =
      (n + 1 : ℝ≥0∞) * ∑ index ∈ Finset.range (n + 1), (index + 1 : ℝ≥0∞)⁻¹ := by
  have tailSum : collect_coupons.expectedReturn heap (n + 1)
      (fun _ result => (result.2.toNat : ℝ≥0∞)) =
      ∑' budget : Nat, collect_coupons.returnProbability heap (n + 1)
        (fun _ result => budget < result.2.toNat) := by
    simp_rw [collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial]
    simp only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true]
    convert callExpected_nat_tail_sum nextChoice collect_coupons.outcome
      (collect_coupons.initial heap (n + 1)) (fun result => result.2.2.toNat) using 1
    apply tsum_congr
    intro budget
    congr 1
    funext result
    by_cases after : budget < result.2.2.toNat <;> simp [after]
  rw [tailSum]
  simp_rw [draws_more_than]
  exact mean_empty n

/-- For N positive coupon types, the actual algorithm has expected total draw
cost N H_N, with all finite and infinite execution paths accounted for. -/
theorem running_time_succ (heap : Heap) (n : Nat) :
    collect_coupons.expectedCost heap (n + 1) "random_draws" =
      (n + 1 : ℝ≥0∞) * ∑ index ∈ Finset.range (n + 1), (index + 1 : ℝ≥0∞)⁻¹ := by
  have bridge := total_clock_reward heap n id measurable_id
  change collect_coupons.expectedCost heap (n + 1) "random_draws" = _ at bridge
  rw [bridge]
  exact expected_return_draws heap n

/-- With probability one, the source program returns its newly allocated set
containing exactly every coupon type from zero to N−1. -/
theorem correctness_succ (heap : Heap) (n : Nat) :
    collect_coupons.returnProbability heap (n + 1) (fun final result =>
      result.1 = heap.nextCollection ∧
        Represents final result.1 (Finset.univ : Finset (Fin (n + 1)))) = 1 := by
  rw [collect_coupons.returnProbability_eq_expectedReturn heap (n + 1) trivial]
  have equal : collect_coupons.expectedReturn heap (n + 1) (fun final result =>
      if result.1 = heap.nextCollection ∧
          Represents final result.1 (Finset.univ : Finset (Fin (n + 1))) then 1 else 0) =
      collect_coupons.expectedReturn heap (n + 1) (fun _ _ => 1) := by
    simp only [collect_coupons.expectedReturn, collect_coupons.ValidInput, if_true,
      collect_coupons.initial, start]
    advance
    advance
    advance
    conv_rhs =>
      rw [callExpected_next nextChoice collect_coupons.outcome _ _ rfl (by rfl)]
      rw [callExpected_next nextChoice collect_coupons.outcome _ _ rfl (by rfl)]
      rw [callExpected_next nextChoice collect_coupons.outcome _ _ rfl (by rfl)]
    have loop := collection_loop
      (.active (emptyHeap heap) (.fn_collect_coupons 4
        {v0 := (n : Int) + 1, v1 := heap.nextCollection, t12 := heap.nextCollection}) [])
      n heap.nextCollection 0 ∅ trivial rfl rfl rfl (represents_empty heap n)
    have agrees := loop.agree_completed
      (fun final result => if result.1 = heap.nextCollection ∧
        Represents final result.1 (Finset.univ : Finset (Fin (n + 1))) then 1 else 0)
      (fun _ _ => 1) (by intro final draws rep; simp only [true_and, ↓reduceIte, rep])
    exact agrees
  have finished : collect_coupons.expectedReturn heap (n + 1) (fun _ _ => 1) = 1 := by
    simpa only [collect_coupons.expectedReturn, collect_coupons.ValidInput,
      if_true, callProbability] using completes heap n
  convert equal.trans finished using 1
  congr 1
  funext final result
  by_cases full : result.1 = heap.nextCollection ∧
      Represents final result.1 (Finset.univ : Finset (Fin (n + 1))) <;> simp [full]

end CouponAnalysis
