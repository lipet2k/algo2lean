import Algo.partition_random_model.Analysis
import Mathlib.Data.Finset.Card

/-!
The rank of a key is the number of strictly smaller keys in the interval.
Partition correctness identifies the returned boundary with this rank; uniform
pivot-key selection therefore gives a uniform partition boundary for distinct keys.
-/

noncomputable section
namespace PartitionAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open scoped ENNReal

/-- Number of interval cells whose keys are strictly less than the supplied value. -/
def rank (heap : Heap) (ref : SeqRef) (lo hi value : Int) : Nat :=
  ((Finset.Ico lo hi).filter (fun index => heap.read ref index < value)).card

/-- A permutation fixing every outside position maps the interval to itself. -/
theorem perm_interval (permutation : Equiv.Perm Int) (lo hi : Int)
    (outside : ∀ index, index < lo ∨ hi ≤ index → permutation index = index) (index : Int)
    (inside : lo ≤ index ∧ index < hi) : lo ≤ permutation index ∧ permutation index < hi := by
  by_contra notInside
  have fixed := outside (permutation index) (by omega)
  have same : permutation index = index := permutation.injective fixed
  omega

/-- Interval rearrangement preserves distinctness of the keys. -/
theorem rearranges_distinct {before after : Heap} {ref : SeqRef} {lo hi : Int}
    (permuted : Rearranges before after ref lo hi)
    (distinct : Set.InjOn (before.read ref) (Set.Ico lo hi)) :
    Set.InjOn (after.read ref) (Set.Ico lo hi) := by
  obtain ⟨permutation, outside, values⟩ := permuted
  intro first hf second hs same
  apply permutation.injective
  apply distinct (perm_interval permutation lo hi outside first hf)
    (perm_interval permutation lo hi outside second hs)
  simpa only [values] using same

/-- Rearranging an interval preserves the rank of every integer value. -/
theorem rearranges_rank {before after : Heap} {ref : SeqRef} {lo hi : Int}
    (permuted : Rearranges before after ref lo hi) (value : Int) :
    rank after ref lo hi value = rank before ref lo hi value := by
  classical
  obtain ⟨permutation, outside, values⟩ := permuted
  unfold rank
  apply Finset.card_bij (fun index _ => permutation index)
  · intro index member
    obtain ⟨inside, small⟩ := Finset.mem_filter.mp member
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr (perm_interval permutation lo hi outside index (Finset.mem_Ico.mp inside)),
      by simpa only [values] using small⟩
  · intro first _ second _ same
    exact permutation.injective same
  · intro index member
    obtain ⟨inside, small⟩ := Finset.mem_filter.mp member
    have inverseOutside : ∀ position, position < lo ∨ hi ≤ position → permutation.symm position = position := by
      intro position beyond
      apply permutation.injective
      simp [outside position beyond]
    refine ⟨permutation.symm index, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr (perm_interval permutation.symm lo hi inverseOutside index (Finset.mem_Ico.mp inside)),
      by simpa only [values, Equiv.apply_symm_apply] using small⟩

/-- In a distinct-key partition, exactly the positions before the boundary
contain keys smaller than the pivot. -/
theorem partitioned_rank (heap : Heap) (ref : SeqRef) (lo hi boundary pivot : Int)
    (partitioned : Partitioned heap ref lo hi boundary pivot)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    rank heap ref lo hi pivot = (boundary - lo).toNat := by
  classical
  obtain ⟨low, high, pivotCell, small, large⟩ := partitioned
  have positions : (Finset.Ico lo hi).filter (fun index => heap.read ref index < pivot) =
      Finset.Ico lo boundary := by
    ext index
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨lower, upper⟩, less⟩
      refine ⟨lower, ?_⟩
      by_contra notBefore
      rcases eq_or_lt_of_le (by omega : boundary ≤ index) with same | after
      · subst index; omega
      · have greater := large index after upper
        omega
    · rintro ⟨lower, upper⟩
      refine ⟨⟨lower, by omega⟩, ?_⟩
      apply lt_of_le_of_ne (small index lower upper)
      intro same
      have equal := distinct (by constructor <;> omega) ⟨low, high⟩ (same.trans pivotCell.symm)
      omega
  unfold rank
  rw [positions, Int.card_Ico]

/-- The boundary index is the original pivot key's rank, shifted by lo. -/
theorem boundary_eq_rank {before after : Heap} {ref : SeqRef} {lo hi boundary pivot : Int}
    (permuted : Rearranges before after ref lo hi)
    (partitioned : Partitioned after ref lo hi boundary pivot)
    (distinct : Set.InjOn (before.read ref) (Set.Ico lo hi)) :
    boundary = lo + (rank before ref lo hi pivot : Int) := by
  have finalRank := partitioned_rank after ref lo hi boundary pivot partitioned
    (rearranges_distinct permuted distinct)
  rw [rearranges_rank permuted] at finalRank
  have lower := partitioned.1
  omega

/-- Increasing the comparison key past an existing key strictly increases its rank. -/
theorem rank_strict (heap : Heap) (ref : SeqRef) (lo hi first second : Int)
    (member : lo ≤ first ∧ first < hi) (less : heap.read ref first < heap.read ref second) :
    rank heap ref lo hi (heap.read ref first) < rank heap ref lo hi (heap.read ref second) := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro index belongs
    obtain ⟨inside, smaller⟩ := Finset.mem_filter.mp belongs
    exact Finset.mem_filter.mpr ⟨inside, lt_trans smaller less⟩
  · intro same
    have belongs : first ∈ (Finset.Ico lo hi).filter (fun index => heap.read ref index < heap.read ref second) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr member, less⟩
    rw [← same] at belongs
    exact (lt_irrefl (heap.read ref first)) (Finset.mem_filter.mp belongs).2

/-- An interval key's rank is smaller than the interval's cardinality. -/
theorem rank_lt_length (heap : Heap) (ref : SeqRef) (lo hi position : Int)
    (member : lo ≤ position ∧ position < hi) :
    rank heap ref lo hi (heap.read ref position) < (hi - lo).toNat := by
  classical
  rw [← Int.card_Ico]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro same
  have belongs : position ∈ Finset.Ico lo hi := Finset.mem_Ico.mpr member
  rw [← same] at belongs
  exact (lt_irrefl (heap.read ref position)) (Finset.mem_filter.mp belongs).2

/-- Distinct input keys have distinct ranks. -/
theorem rank_injective (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    Set.InjOn (fun position => rank heap ref lo hi (heap.read ref position)) (Set.Ico lo hi) := by
  intro first hf second hs same
  change rank heap ref lo hi (heap.read ref first) = rank heap ref lo hi (heap.read ref second) at same
  apply distinct hf hs
  rcases lt_trichotomy (heap.read ref first) (heap.read ref second) with less | equal | greater
  · have unequal := rank_strict heap ref lo hi first second hf less
    omega
  · exact equal
  · have unequal := rank_strict heap ref lo hi second first hs greater
    omega

/-- The shifted ranks of distinct interval keys permute the interval's positions. -/
theorem rank_bijection (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    Set.BijOn (fun position => lo + (rank heap ref lo hi (heap.read ref position) : Int))
      (Finset.Ico lo hi) (Finset.Ico lo hi) := by
  let transform := fun position => lo + (rank heap ref lo hi (heap.read ref position) : Int)
  have maps : Set.MapsTo transform (Finset.Ico lo hi) (Finset.Ico lo hi) := by
    intro position member
    have inside := Finset.mem_Ico.mp member
    have bound := rank_lt_length heap ref lo hi position inside
    apply Finset.mem_Ico.mpr
    dsimp [transform]
    constructor <;> omega
  have injective : Set.InjOn transform (Finset.Ico lo hi) := by
    intro first hf second hs equal
    apply rank_injective heap ref lo hi distinct (Finset.mem_Ico.mp hf) (Finset.mem_Ico.mp hs)
    dsimp [transform] at equal
    change rank heap ref lo hi (heap.read ref first) = rank heap ref lo hi (heap.read ref second)
    omega
  exact ⟨maps, injective, Finset.surjOn_of_injOn_of_card_le transform maps injective le_rfl⟩

/-- Reindexing a uniform key draw by rank leaves every expectation unchanged. -/
theorem uniform_rank_expected (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) (reward : Int → ℝ≥0∞) :
    pmfExpected (uniformInt lo hi nonempty)
      (fun position => reward (lo + (rank heap ref lo hi (heap.read ref position) : Int))) =
    pmfExpected (uniformInt lo hi nonempty) reward := by
  rw [pmfExpected_uniformInt, pmfExpected_uniformInt]
  obtain ⟨maps, injective, surjective⟩ := rank_bijection heap ref lo hi distinct
  apply Finset.sum_bij (fun position _ => lo + (rank heap ref lo hi (heap.read ref position) : Int))
  · exact maps
  · exact fun first hf second hs same => injective hf hs same
  · intro position member
    obtain ⟨original, belongs, equal⟩ := surjective member
    exact ⟨original, belongs, equal⟩
  · intros; rfl

/-- A uniform interval key has a uniform shifted rank. -/
theorem uniform_rank_law (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    (uniformInt lo hi nonempty).map
      (fun position => lo + (rank heap ref lo hi (heap.read ref position) : Int)) =
    uniformInt lo hi nonempty := by
  classical
  ext value
  have result : pmfExpected ((uniformInt lo hi nonempty).map
      (fun position => lo + (rank heap ref lo hi (heap.read ref position) : Int)))
      (fun output => if output = value then 1 else 0) =
      pmfExpected (uniformInt lo hi nonempty) (fun output => if output = value then 1 else 0) := by
    rw [pmfExpected_map]
    exact uniform_rank_expected heap ref lo hi nonempty distinct
      (fun output => if output = value then (1 : ℝ≥0∞) else 0)
  simpa [pmfExpected] using result

/-- Deterministic partition places each chosen key at its original rank. -/
theorem chosen_boundary (heap : Heap) (ref : SeqRef) (lo hi position : Int)
    (nonempty : lo < hi) (member : lo ≤ position ∧ position < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    (partitionResult (choosePivot heap ref position hi) ref lo hi).2 =
      lo + (rank heap ref lo hi (heap.read ref position) : Int) := by
  have possible : partitionResult (choosePivot heap ref position hi) ref lo hi ∈
      (randomizedPartitionLaw heap ref lo hi nonempty).support :=
    (PMF.mem_support_map_iff ..).2 ⟨position, (uniformInt_support ..).2 member, rfl⟩
  obtain ⟨partitioned, permuted, _⟩ := randomizedPartitionLaw_correct heap ref lo hi nonempty _ possible
  rw [chosen_pivot heap ref lo hi position nonempty] at partitioned
  exact boundary_eq_rank permuted partitioned distinct

/-- Projecting randomized partition's joint law onto the boundary gives a uniform
integer in [lo,hi); this is the pivot-rank law used by quicksort and selection. -/
theorem randomized_boundary_law (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    (randomizedPartitionLaw heap ref lo hi nonempty).map Prod.snd = uniformInt lo hi nonempty := by
  rw [randomizedPartitionLaw, PMF.map_comp]
  trans (uniformInt lo hi nonempty).map
    (fun position => lo + (rank heap ref lo hi (heap.read ref position) : Int))
  · ext value
    simp only [PMF.map_apply]
    apply tsum_congr
    intro position
    by_cases possible : position ∈ (uniformInt lo hi nonempty).support
    · simp only [Function.comp_apply,
        chosen_boundary heap ref lo hi position nonempty ((uniformInt_support ..).1 possible) distinct]
      split_ifs <;> rfl
    · simp [(PMF.apply_eq_zero_iff _ _).2 possible]
  · exact uniform_rank_law heap ref lo hi nonempty distinct

end PartitionAnalysis
