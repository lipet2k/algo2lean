import Algo.general_binary_lower_bound.Points
import Algo.general_binary_lower_bound.Facts
import Algo2LeanLib.SequenceModel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Binary search over arbitrary integer intervals of an infinite sequence.
The proof separates interval arithmetic, preservation of discarded halves,
source-level loop steps, a decreasing-length induction, and the final contract.
-/

open Algo2LeanCore Algo2LeanGenerated
open Algo.general_binary_lower_bound Algo.general_binary_lower_bound.Algo2LeanGenerated

namespace GeneralBinaryLowerBoundAnalysis

/-- Nondecreasing contents on the half-open interval `[lo, hi)`. -/
def SortedOn (a : Seq) (lo hi : Int) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → a i ≤ a j

/-- The returned boundary separates values below the target from values at least it. -/
def PartitionAt (a : Seq) (lo hi target result : Int) : Prop :=
  lo ≤ result ∧ result ≤ hi ∧
  (∀ i, lo ≤ i → i < result → a i < target) ∧
  (∀ i, result ≤ i → i < hi → target ≤ a i)

/-- The mathematical midpoint uses Python's floor division, also at negative indices. -/
def midpoint (lo hi : Int) : Int := Int.fdiv (lo + hi) 2

theorem midpoint_bounds (lo hi : Int) (nonempty : lo < hi) :
    lo ≤ midpoint lo hi ∧ midpoint lo hi < hi := by
  unfold midpoint
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem left_half_shorter (lo hi : Int) (nonempty : lo < hi) :
    (midpoint lo hi - lo).toNat < (hi - lo).toNat := by
  have bounds := midpoint_bounds lo hi nonempty
  omega

theorem right_half_shorter (lo hi : Int) (nonempty : lo < hi) :
    (hi - (midpoint lo hi + 1)).toNat < (hi - lo).toNat := by
  have bounds := midpoint_bounds lo hi nonempty
  omega

/-- Everything outside the current search interval has already been classified. -/
def SearchInvariant (a : Seq) (start finish target lo hi : Int) : Prop :=
  start ≤ lo ∧ lo ≤ hi ∧ hi ≤ finish ∧
  (∀ i, start ≤ i → i < lo → a i < target) ∧
  (∀ i, hi ≤ i → i < finish → target ≤ a i)

theorem initial_invariant (a : Seq) (lo hi target : Int) (ordered : lo ≤ hi) :
    SearchInvariant a lo hi target lo hi := by
  refine ⟨Int.le_refl _, ordered, Int.le_refl _, ?_, ?_⟩ <;> intro i first second <;> omega

theorem discard_left_half (a : Seq) (start finish target lo hi : Int)
    (sorted : SortedOn a start finish)
    (invariant : SearchInvariant a start finish target lo hi)
    (nonempty : lo < hi) (below : a (midpoint lo hi) < target) :
    SearchInvariant a start finish target (midpoint lo hi + 1) hi := by
  obtain ⟨lower, ordered, upper, before, after⟩ := invariant
  have bounds := midpoint_bounds lo hi nonempty
  refine ⟨by omega, by omega, upper, ?_, after⟩
  intro i start_le before_middle
  by_cases old : i < lo
  · exact before i start_le old
  · have monotone := sorted i (midpoint lo hi) start_le (by omega) (by omega)
    omega

theorem discard_right_half (a : Seq) (start finish target lo hi : Int)
    (sorted : SortedOn a start finish)
    (invariant : SearchInvariant a start finish target lo hi)
    (nonempty : lo < hi) (at_least : target ≤ a (midpoint lo hi)) :
    SearchInvariant a start finish target lo (midpoint lo hi) := by
  obtain ⟨lower, ordered, upper, before, after⟩ := invariant
  have bounds := midpoint_bounds lo hi nonempty
  refine ⟨lower, by omega, by omega, before, ?_⟩
  intro i middle_le before_finish
  by_cases old : hi ≤ i
  · exact after i old before_finish
  · have monotone := sorted (midpoint lo hi) i (by omega) middle_le before_finish
    omega

theorem invariant_at_exit (a : Seq) (start finish target lo hi : Int)
    (invariant : SearchInvariant a start finish target lo hi) (finished : hi ≤ lo) :
    PartitionAt a start finish target lo := by
  obtain ⟨lower, ordered, upper, before, after⟩ := invariant
  refine ⟨lower, by omega, before, ?_⟩
  intro i at_boundary before_finish
  exact after i (by omega) before_finish

theorem partition_unique (a : Seq) (lo hi target first second : Int)
    (one : PartitionAt a lo hi target first) (two : PartitionAt a lo hi target second) :
    first = second := by
  obtain ⟨first_lo, first_hi, first_before, first_after⟩ := one
  obtain ⟨second_lo, second_hi, second_before, second_after⟩ := two
  by_cases lt : first < second
  · have below := second_before first first_lo lt
    have above := first_after first (Int.le_refl _) (by omega)
    omega
  · by_cases gt : second < first
    · have below := first_before second second_lo gt
      have above := second_after second (Int.le_refl _) (by omega)
      omega
    · omega

/-- Only named locations and source variables describe the loop's local state. -/
def AtSearch (state : Configuration) (heap : Heap) (object : SeqRef) (lo hi target : Int) : Prop :=
  lower_bound.At.search state ∧ state.heap = heap ∧
  lower_bound.Local.a state = some object ∧ lower_bound.Local.lo state = some lo ∧
  lower_bound.Local.hi state = some hi ∧ lower_bound.Local.target state = some target

/-- A false loop guard immediately returns the current lower endpoint. -/
theorem search_exit (state : Configuration) (heap : Heap) (object : SeqRef) (lo hi target : Int)
    (located : AtSearch state heap object lo hi target) (finished : hi ≤ lo) :
    lower_bound.CallFrom state heap lo := by
  obtain ⟨named, sameHeap, sameObject, sameLo, sameHi, sameTarget⟩ := located
  unfold lower_bound.At.search at named
  split at named <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [lower_bound.Local.a, lower_bound.Local.lo, lower_bound.Local.hi,
    lower_bound.Local.target] at sameObject sameLo sameHi sameTarget
  change Summary Step heap (.fn_lower_bound 4 locals) heap (.fn_lower_bound lo)
  intro caller
  refine (Reaches.single (Step.lower_bound_pc4 _ _ _)).trans ?_
  refine (Reaches.single (Step.lower_bound_pc3_false _ _ _ (by simp [sameLo, sameHi]; omega))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc2 _ _ _)).trans ?_
  simpa only [sameLo] using Reaches.single (Step.lower_bound_pc1 heap
    { locals with t6 := decide (locals.v1 < locals.v2), t5 := locals.v1 } caller)

/-- One iteration discards the left half, then reuses a summary of what remains. -/
theorem search_go_right (state : Configuration) (heap : Heap) (object : SeqRef) (lo hi target result : Int)
    (located : AtSearch state heap object lo hi target) (allocated : object < heap.nextRef)
    (nonempty : lo < hi) (comparison : heap.read object (midpoint lo hi) < target)
    (continuation : ∀ next, AtSearch next heap object (midpoint lo hi + 1) hi target →
      lower_bound.CallFrom next heap result) :
    lower_bound.CallFrom state heap result := by
  obtain ⟨named, sameHeap, sameObject, sameLo, sameHi, sameTarget⟩ := located
  unfold lower_bound.At.search at named
  split at named <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [lower_bound.Local.a, lower_bound.Local.lo, lower_bound.Local.hi,
    lower_bound.Local.target] at sameObject sameLo sameHi sameTarget
  let next : State_lower_bound := { locals with v1 := midpoint lo hi + 1, v4 := midpoint lo hi, t6 := true, t7 := true }
  have nextLocated : AtSearch (.active heap (.fn_lower_bound 4 next) []) heap object (midpoint lo hi + 1) hi target := by
    simp [AtSearch, lower_bound.At.search, Config.heap, lower_bound.Local.a,
      lower_bound.Local.lo, lower_bound.Local.hi, lower_bound.Local.target,
      next, sameObject, sameHi, sameTarget]
  have continued := continuation _ nextLocated
  simp only [midpoint] at comparison
  change Summary Step heap (.fn_lower_bound 4 locals) heap (.fn_lower_bound result)
  intro caller
  refine (Reaches.single (Step.lower_bound_pc4 _ _ _)).trans ?_
  refine (Reaches.single (Step.lower_bound_pc3_true _ _ _ (by simpa [sameLo, sameHi] using nonempty))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc9 _ _ _ (by decide))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc8 _ _ _ (by simpa [sameObject] using allocated))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc7_true _ _ _ (by simpa [sameObject, sameLo, sameHi, sameTarget, midpoint] using comparison))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc5 _ _ _)).trans ?_
  simpa [next, midpoint, sameObject, sameLo, sameHi, sameTarget, nonempty, comparison] using continued caller

/-- One iteration discards the right half, then reuses a summary of what remains. -/
theorem search_go_left (state : Configuration) (heap : Heap) (object : SeqRef) (lo hi target result : Int)
    (located : AtSearch state heap object lo hi target) (allocated : object < heap.nextRef)
    (nonempty : lo < hi) (comparison : target ≤ heap.read object (midpoint lo hi))
    (continuation : ∀ next, AtSearch next heap object lo (midpoint lo hi) target →
      lower_bound.CallFrom next heap result) :
    lower_bound.CallFrom state heap result := by
  obtain ⟨named, sameHeap, sameObject, sameLo, sameHi, sameTarget⟩ := located
  unfold lower_bound.At.search at named
  split at named <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [lower_bound.Local.a, lower_bound.Local.lo, lower_bound.Local.hi,
    lower_bound.Local.target] at sameObject sameLo sameHi sameTarget
  let next : State_lower_bound := { locals with v2 := midpoint lo hi, v4 := midpoint lo hi, t6 := true, t7 := false }
  have nextLocated : AtSearch (.active heap (.fn_lower_bound 4 next) []) heap object lo (midpoint lo hi) target := by
    simp [AtSearch, lower_bound.At.search, Config.heap, lower_bound.Local.a,
      lower_bound.Local.lo, lower_bound.Local.hi, lower_bound.Local.target,
      next, sameObject, sameLo, sameTarget]
  have continued := continuation _ nextLocated
  simp only [midpoint] at comparison
  change Summary Step heap (.fn_lower_bound 4 locals) heap (.fn_lower_bound result)
  intro caller
  refine (Reaches.single (Step.lower_bound_pc4 _ _ _)).trans ?_
  refine (Reaches.single (Step.lower_bound_pc3_true _ _ _ (by simpa [sameLo, sameHi] using nonempty))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc9 _ _ _ (by decide))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc8 _ _ _ (by simpa [sameObject] using allocated))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc7_false _ _ _ (by simpa [sameObject, sameLo, sameHi, sameTarget, midpoint] using comparison))).trans ?_
  refine (Reaches.single (Step.lower_bound_pc6 _ _ _)).trans ?_
  have notBelow : ¬ heap.read object (Int.fdiv (lo + hi) 2) < target := by omega
  simpa [next, midpoint, sameObject, sameLo, sameHi, sameTarget, nonempty, notBelow] using continued caller

/-- A decreasing interval length turns local loop rules into a completed-call
    proof. Invariant and postcondition remain arbitrary mathematical predicates. -/
theorem loop_induction (heap : Heap) (object : SeqRef) (target : Int)
    (allocated : object < heap.nextRef)
    (invariant : Int → Int → Prop) (postcondition : Int → Prop)
    (finish : ∀ lo hi, invariant lo hi → hi ≤ lo → postcondition lo)
    (discardLeft : ∀ lo hi, invariant lo hi → lo < hi →
      heap.read object (midpoint lo hi) < target → invariant (midpoint lo hi + 1) hi)
    (discardRight : ∀ lo hi, invariant lo hi → lo < hi →
      target ≤ heap.read object (midpoint lo hi) → invariant lo (midpoint lo hi))
    (lo hi : Int) (initial : invariant lo hi) :
    ∃ result, postcondition result ∧ ∀ state, AtSearch state heap object lo hi target →
      lower_bound.CallFrom state heap result := by
  have terminate : ∀ length : Nat, ∀ lo hi : Int, (hi - lo).toNat = length → invariant lo hi →
      ∃ result, postcondition result ∧ ∀ state, AtSearch state heap object lo hi target →
        lower_bound.CallFrom state heap result := by
    intro length
    induction length using Nat.strongRecOn with
    | ind length smaller =>
      intro lo hi measured preserved
      by_cases nonempty : lo < hi
      · by_cases below : heap.read object (midpoint lo hi) < target
        · have decreases : (hi - (midpoint lo hi + 1)).toNat < length := by
            simpa [measured] using right_half_shorter lo hi nonempty
          obtain ⟨result, property, continuation⟩ := smaller _ decreases _ _ rfl
            (discardLeft lo hi preserved nonempty below)
          exact ⟨result, property, fun state located =>
            search_go_right state heap object lo hi target result located allocated nonempty below continuation⟩
        · have atLeast : target ≤ heap.read object (midpoint lo hi) := by omega
          have decreases : (midpoint lo hi - lo).toNat < length := by
            simpa [measured] using left_half_shorter lo hi nonempty
          obtain ⟨result, property, continuation⟩ := smaller _ decreases _ _ rfl
            (discardRight lo hi preserved nonempty atLeast)
          exact ⟨result, property, fun state located =>
            search_go_left state heap object lo hi target result located allocated nonempty atLeast continuation⟩
      · have finished : hi ≤ lo := by omega
        exact ⟨lo, finish lo hi preserved finished, fun state located =>
          search_exit state heap object lo hi target located finished⟩
  exact terminate _ lo hi rfl initial

/-- A source-level loop summary specializes to an ordinary complete call. -/
theorem summary_of_search (heap : Heap) (object : SeqRef) (lo hi target result : Int)
    (allocated : object < heap.nextRef)
    (search : ∀ state, AtSearch state heap object lo hi target →
      lower_bound.CallFrom state heap result) :
    lower_bound.Call heap (object, lo, hi, target) heap result := by
  have located : AtSearch (lower_bound.initial heap (object, lo, hi, target))
      heap object lo hi target := by
    simp [AtSearch, lower_bound.initial, start, lower_bound.At.search, Config.heap,
      lower_bound.Local.a, lower_bound.Local.lo, lower_bound.Local.hi, lower_bound.Local.target]
  exact ⟨allocated, search _ located⟩

/-- Termination does not depend on sortedness. Reversed ranges also terminate. -/
theorem terminating_summary (heap : Heap) (object : SeqRef) (lo hi target : Int)
    (allocated : object < heap.nextRef) :
    ∃ result, lo ≤ result ∧ result ≤ max lo hi ∧
      lower_bound.Call heap (object, lo, hi, target) heap result := by
  let invariant := fun left right : Int => lo ≤ left ∧ left ≤ max lo hi ∧ right ≤ max lo hi
  obtain ⟨result, bounds, search⟩ := loop_induction heap object target allocated invariant
    (fun result => lo ≤ result ∧ result ≤ max lo hi)
    (by intro left right maintained stopped; exact ⟨maintained.1, maintained.2.1⟩)
    (by intro left right maintained nonempty below
        have middle := midpoint_bounds left right nonempty
        dsimp [invariant] at maintained ⊢
        omega)
    (by intro left right maintained nonempty atLeast
        have middle := midpoint_bounds left right nonempty
        dsimp [invariant] at maintained ⊢
        omega)
    lo hi (by dsimp [invariant]; omega)
  exact ⟨result, bounds.1, bounds.2, summary_of_search heap object lo hi target result allocated search⟩

/-- On a sorted interval, the discarded-region invariant yields the full
    partition contract, while the same proof also supplies termination. -/
theorem sorted_summary (heap : Heap) (object : SeqRef) (lo hi target : Int)
    (allocated : object < heap.nextRef) (ordered : lo ≤ hi)
    (sorted : SortedOn (heap.read object) lo hi) :
    ∃ result, PartitionAt (heap.read object) lo hi target result ∧
      lower_bound.Call heap (object, lo, hi, target) heap result := by
  obtain ⟨result, partition, search⟩ := loop_induction heap object target allocated
    (SearchInvariant (heap.read object) lo hi target)
    (PartitionAt (heap.read object) lo hi target)
    (fun left right maintained stopped => invariant_at_exit _ lo hi target left right maintained stopped)
    (fun left right maintained nonempty below => discard_left_half _ lo hi target left right sorted maintained nonempty below)
    (fun left right maintained nonempty atLeast => discard_right_half _ lo hi target left right sorted maintained nonempty atLeast)
    lo hi (initial_invariant _ lo hi target ordered)
  exact ⟨result, partition, summary_of_search heap object lo hi target result allocated search⟩

/-- This program has at most one successor at every configuration. -/
theorem transitions_deterministic : Deterministic Step :=
  Algo.general_binary_lower_bound.Algo2LeanGenerated.deterministic

/-- All completed calls agree, including the final heap. -/
theorem execution_unique (heap firstHeap secondHeap : Heap) (object : SeqRef)
    (lo hi target first second : Int)
    (one : lower_bound.Run heap (object, lo, hi, target) firstHeap first)
    (two : lower_bound.Run heap (object, lo, hi, target) secondHeap second) :
    firstHeap = secondHeap ∧ first = second := by
  have endpoints := Reaches.eq_of_terminal (step := Step) transitions_deterministic one.2 two.2
    (by intro next transition; cases transition) (by intro next transition; cases transition)
  cases endpoints
  exact ⟨rfl, rfl⟩

theorem output_unique (a : Seq) (lo hi target first second : Int)
    (one : lower_bound.Returns (a, lo, hi, target) first)
    (two : lower_bound.Returns (a, lo, hi, target) second) : first = second := by
  obtain ⟨firstHeap, one⟩ := one
  obtain ⟨secondHeap, two⟩ := two
  exact (execution_unique _ firstHeap secondHeap _ lo hi target first second one two).2

/-- Binary search returns for every sequence and interval, even without sortedness. -/
theorem terminates (a : Seq) (lo hi target : Int) :
    ∃ result, lo ≤ result ∧ result ≤ max lo hi ∧ lower_bound.Returns (a, lo, hi, target) result := by
  let heap := ({} : Heap).allocate a
  obtain ⟨result, lower, upper, summary⟩ := terminating_summary heap 0 lo hi target (by simp [heap])
  exact ⟨result, lower, upper, heap, summary.1, summary.2.root⟩

/-- A read-only search preserves the entire caller heap, not just the searched slice. -/
theorem execution_preserves_heap (heap finalHeap : Heap) (object : SeqRef) (lo hi target result : Int)
    (execution : lower_bound.Run heap (object, lo, hi, target) finalHeap result) :
    finalHeap = heap := by
  obtain ⟨expected, _, _, summary⟩ := terminating_summary heap object lo hi target execution.1
  exact (execution_unique heap finalHeap heap object lo hi target result expected execution
    ⟨summary.1, summary.2.root⟩).1

/-- Termination and the full partition specification hold together on sorted input. -/
theorem sorted_termination (a : Seq) (lo hi target : Int) (ordered : lo ≤ hi)
    (sorted : SortedOn a lo hi) :
    ∃ result, PartitionAt a lo hi target result ∧ lower_bound.Returns (a, lo, hi, target) result := by
  let heap := ({} : Heap).allocate a
  have contents : heap.read 0 = a := by funext i; simp [heap, Heap.read, Heap.allocate]
  obtain ⟨result, partition, summary⟩ := sorted_summary heap 0 lo hi target
    (by simp [heap]) ordered (by simpa [contents] using sorted)
  exact ⟨result, by simpa [contents] using partition, heap, summary.1, summary.2.root⟩

/-- The specification applies to every output, not only the constructed witness. -/
theorem every_output_correct (a : Seq) (lo hi target result : Int) (ordered : lo ≤ hi)
    (sorted : SortedOn a lo hi) (produces : lower_bound.Returns (a, lo, hi, target) result) :
    PartitionAt a lo hi target result := by
  obtain ⟨expected, partition, computation⟩ := sorted_termination a lo hi target ordered sorted
  have same := output_unique a lo hi target result expected produces computation
  simpa [same] using partition

-- Main result: Correctness
/-- Complete correctness: the output predicate is exactly the unique sorted
    partition boundary. This covers empty intervals, duplicates and negative indices. -/
theorem output_iff_partition (a : Seq) (lo hi target result : Int) (ordered : lo ≤ hi)
    (sorted : SortedOn a lo hi) :
    lower_bound.Returns (a, lo, hi, target) result ↔ PartitionAt a lo hi target result := by
  constructor
  · exact every_output_correct a lo hi target result ordered sorted
  · intro partition
    obtain ⟨expected, expectedPartition, produces⟩ := sorted_termination a lo hi target ordered sorted
    have same := partition_unique a lo hi target result expected partition expectedPartition
    simpa [same] using produces

/-- An empty or reversed range skips the loop and returns its original lower endpoint. -/
theorem empty_or_reversed (a : Seq) (lo hi target : Int) (empty : hi ≤ lo) :
    lower_bound.Returns (a, lo, hi, target) lo := by
  let heap := ({} : Heap).allocate a
  have summary := summary_of_search heap 0 lo hi target lo (by simp [heap])
    (fun state located => search_exit state heap 0 lo hi target located empty)
  exact ⟨heap, summary.1, summary.2.root⟩

theorem empty_or_reversed_iff (a : Seq) (lo hi target result : Int) (empty : hi ≤ lo) :
    lower_bound.Returns (a, lo, hi, target) result ↔ result = lo := by
  constructor
  · intro produces
    exact output_unique a lo hi target result lo produces (empty_or_reversed a lo hi target empty)
  · intro same
    simpa [same] using empty_or_reversed a lo hi target empty

/-- Sortedness on a one-element interval is automatic. -/
theorem singleton_sorted (a : Seq) (lo : Int) : SortedOn a lo (lo + 1) := by
  intro i j lower ordered upper
  have same : i = j := by omega
  simp [same]

theorem singleton_below (a : Seq) (lo target : Int) (below : a lo < target) :
    lower_bound.Returns (a, lo, lo + 1, target) (lo + 1) := by
  apply (output_iff_partition a lo (lo + 1) target (lo + 1) (by omega) (singleton_sorted a lo)).2
  refine ⟨by omega, Int.le_refl _, ?_, ?_⟩
  · intro i lower upper
    have same : i = lo := by omega
    simpa [same] using below
  · intro i lower upper
    omega

theorem singleton_at_least (a : Seq) (lo target : Int) (at_least : target ≤ a lo) :
    lower_bound.Returns (a, lo, lo + 1, target) lo := by
  apply (output_iff_partition a lo (lo + 1) target lo (by omega) (singleton_sorted a lo)).2
  refine ⟨Int.le_refl _, by omega, ?_, ?_⟩
  · intro i lower upper
    omega
  · intro i lower upper
    have same : i = lo := by omega
    simpa [same] using at_least

theorem singleton (a : Seq) (lo target : Int) :
    lower_bound.Returns (a, lo, lo + 1, target)
      (if a lo < target then lo + 1 else lo) := by
  by_cases below : a lo < target
  · simpa [below] using singleton_below a lo target below
  · simpa [below] using singleton_at_least a lo target (by omega)

/-- A heap-level summary of the original empty/reversed-range behavior. -/
theorem empty_summary (heap : Heap) (object : SeqRef) (lo hi target : Int)
    (allocated : object < heap.nextRef) (empty : hi ≤ lo) :
    lower_bound.Call heap (object, lo, hi, target) heap lo :=
  summary_of_search heap object lo hi target lo allocated
    (fun state located => search_exit state heap object lo hi target located empty)

/-- Reuse the existing binary-search theorem with the sorting library's shared
    finite-list model. Empty and reversed intervals have normalized length zero. -/
theorem normalized_summary (heap : Heap) (object : SeqRef) (lo hi target : Int)
    (allocated : object < heap.nextRef)
    (sorted : SequenceModel.Sorted (heap.store object) lo (hi - lo).toNat) :
    ∃ result, lower_bound.Call heap (object, lo, hi, target) heap result ∧
      SequenceModel.LowerBound (heap.store object) lo (hi - lo).toNat target result := by
  by_cases ordered : lo ≤ hi
  · have monotone : SortedOn (heap.read object) lo hi := by
      intro left right low order high
      exact SequenceModel.sorted_indices _ lo (hi - lo).toNat sorted left right low order (by omega)
    obtain ⟨result, partition, call⟩ := sorted_summary heap object lo hi target allocated ordered monotone
    refine ⟨result, call, ?_⟩
    have endpoint : lo + ((hi - lo).toNat : Int) = hi := by omega
    simpa only [SequenceModel.LowerBound, endpoint, Heap.read] using! partition
  · have empty : hi ≤ lo := by omega
    have call := empty_summary heap object lo hi target allocated empty
    refine ⟨lo, call, ?_⟩
    have zero : (hi - lo).toNat = 0 := by omega
    simp [SequenceModel.LowerBound, zero]
    constructor <;> intro index low high <;> omega

end GeneralBinaryLowerBoundAnalysis
