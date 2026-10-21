import Algo.selection_model.Analysis

/-!
Selection correctness is proved from the partition contract and the recursive
joint law. The returned value belongs to the original interval and has the
requested zero-based rank. This first result assumes distinct interval keys.
The source permits equal keys; a count-based specification for ties is separate.
-/

noncomputable section
namespace SelectionAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis

/-- A value occurring in the input interval with the requested number of
strictly smaller keys. For distinct keys this specifies the order statistic. -/
def IsOrderStatistic (heap : Heap) (ref : SeqRef) (lo hi requested value : Int) : Prop :=
  (∃ position, lo ≤ position ∧ position < hi ∧ heap.read ref position = value) ∧
    (rank heap ref lo hi value : Int) = requested

private theorem statistic_before_rearrangement {before after : Heap} {ref : SeqRef}
    {lo hi requested value : Int} (permuted : Rearranges before after ref lo hi)
    (selected : IsOrderStatistic after ref lo hi requested value) :
    IsOrderStatistic before ref lo hi requested value := by
  obtain ⟨⟨position, lower, upper, equal⟩, ranked⟩ := selected
  constructor
  · obtain ⟨permutation, outside, values⟩ := permuted
    have inside := perm_interval permutation lo hi outside position ⟨lower, upper⟩
    exact ⟨permutation position, inside.1, inside.2, (values position).symm.trans equal⟩
  · simpa only [rearranges_rank permuted] using ranked

/-- A key in the left partition has the same rank in that partition and in the
whole interval: the pivot and every right key are at least that key. -/
theorem rank_in_left (heap : Heap) (ref : SeqRef) (lo hi boundary pivot position : Int)
    (partitioned : Partitioned heap ref lo hi boundary pivot)
    (lower : lo ≤ position) (upper : position < boundary) :
    rank heap ref lo hi (heap.read ref position) =
      rank heap ref lo boundary (heap.read ref position) := by
  obtain ⟨low, high, pivotCell, small, large⟩ := partitioned
  have valueSmall := small position lower upper
  unfold rank
  congr 1
  ext index
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨indexLow, indexHigh⟩, less⟩
    refine ⟨⟨indexLow, ?_⟩, less⟩
    by_contra beyond
    by_cases same : index = boundary
    · subst index; omega
    · have valueLarge := large index (by omega) indexHigh
      omega
  · rintro ⟨⟨indexLow, indexHigh⟩, less⟩
    exact ⟨⟨indexLow, by omega⟩, less⟩

/-- Every left key and the pivot precede a key in the right partition. The
whole-interval rank is therefore the right rank plus the left length and one. -/
theorem rank_in_right (heap : Heap) (ref : SeqRef) (lo hi boundary pivot position : Int)
    (partitioned : Partitioned heap ref lo hi boundary pivot)
    (lower : boundary < position) (upper : position < hi) :
    rank heap ref lo hi (heap.read ref position) =
      (boundary + 1 - lo).toNat + rank heap ref (boundary + 1) hi (heap.read ref position) := by
  classical
  obtain ⟨low, high, pivotCell, small, large⟩ := partitioned
  have valueLarge := large position lower upper
  have positions : (Finset.Ico lo hi).filter (fun index => heap.read ref index < heap.read ref position) =
      Finset.Ico lo (boundary + 1) ∪
        (Finset.Ico (boundary + 1) hi).filter (fun index => heap.read ref index < heap.read ref position) := by
    ext index
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union]
    constructor
    · rintro ⟨⟨indexLow, indexHigh⟩, less⟩
      by_cases left : index < boundary + 1
      · exact Or.inl ⟨indexLow, left⟩
      · exact Or.inr ⟨⟨by omega, indexHigh⟩, less⟩
    · rintro (⟨indexLow, indexHigh⟩ | ⟨⟨indexLow, indexHigh⟩, less⟩)
      · refine ⟨⟨indexLow, by omega⟩, ?_⟩
        by_cases same : index = boundary
        · subst index; omega
        · have valueSmall := small index indexLow (by omega)
          omega
      · exact ⟨⟨by omega, indexHigh⟩, less⟩
  have disjoint : Disjoint (Finset.Ico lo (boundary + 1))
      ((Finset.Ico (boundary + 1) hi).filter (fun index => heap.read ref index < heap.read ref position)) := by
    apply Finset.disjoint_left.mpr
    intro index first second
    have a := Finset.mem_Ico.mp first
    have b := Finset.mem_Ico.mp (Finset.mem_filter.mp second).1
    omega
  unfold rank
  rw [positions, Finset.card_union_of_disjoint disjoint, Int.card_Ico]

private theorem rearranges_enlarge {before after : Heap} {ref : SeqRef} {lo hi outerLo outerHi : Int}
    (permuted : Rearranges before after ref lo hi) (lower : outerLo ≤ lo) (upper : hi ≤ outerHi) :
    Rearranges before after ref outerLo outerHi := by
  obtain ⟨permutation, outside, values⟩ := permuted
  exact ⟨permutation, fun index beyond => outside index (by omega), values⟩

/-- Every supported recursive selection outcome returns the requested original
order statistic and preserves the interval's multiset. The fuel bound excludes
the arbitrary fallback at depth zero; callers can always use the input length. -/
theorem selectionLaw_correct (fuel : Nat) (heap : Heap) (ref : SeqRef)
    (lo hi requested : Int) (nonempty : lo < hi)
    (rankLow : 0 ≤ requested) (rankHigh : requested < hi - lo)
    (enough : (hi - lo).toNat ≤ fuel)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi))
    (result : Heap × Int) (possible : result ∈ (selectionLaw fuel heap ref lo hi requested).support) :
    IsOrderStatistic heap ref lo hi requested result.2 ∧ Rearranges heap result.1 ref lo hi := by
  induction fuel generalizing heap lo hi requested result with
  | zero => omega
  | succ fuel ih =>
    simp only [selectionLaw, dif_pos nonempty] at possible
    split_ifs at possible with singleton
    · have same : result = (heap.tick "selection_calls", heap.read ref lo) := by simpa using possible
      subst result
      have requestedZero : requested = 0 := by omega
      have positions : Finset.Ico lo hi = {lo} := by ext index; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      refine ⟨⟨⟨lo, le_rfl, nonempty, rfl⟩, ?_⟩, ⟨Equiv.refl _, fun _ _ => rfl, fun _ => rfl⟩⟩
      simp [rank, positions, requestedZero]
    · obtain ⟨partitioned, belongs, later⟩ := (PMF.mem_support_bind_iff ..).1 possible
      obtain ⟨split, permutation, _⟩ := randomizedPartitionLaw_correct
        (heap.tick "selection_calls") ref lo hi nonempty partitioned belongs
      have permuted : Rearranges heap partitioned.1 ref lo hi := by
        simpa only [Rearranges, ShuffleAnalysis.Rearranges, Heap.read_tick] using permutation
      have keyDistinct := rearranges_distinct permuted distinct
      have low := split.1
      have high := split.2.1
      split_ifs at later with found before
      · have same : result = (partitioned.1, partitioned.1.read ref partitioned.2) := by simpa using later
        subst result
        refine ⟨statistic_before_rearrangement permuted ⟨⟨partitioned.2, low, high, rfl⟩, ?_⟩, permuted⟩
        have ranked := partitioned_rank partitioned.1 ref lo hi partitioned.2
          (partitioned.1.read ref partitioned.2) split keyDistinct
        change (rank partitioned.1 ref lo hi (partitioned.1.read ref partitioned.2) : Int) = requested
        rw [ranked]
        omega
      · have subDistinct : Set.InjOn (partitioned.1.read ref) (Set.Ico lo partitioned.2) := by
          intro first hf second hs same
          exact keyDistinct ⟨hf.1, by have := hf.2; omega⟩ ⟨hs.1, by have := hs.2; omega⟩ same
        obtain ⟨selected, preserved⟩ := ih partitioned.1 lo partitioned.2 requested
          (by omega) rankLow before (by omega) subDistinct result later
        refine ⟨statistic_before_rearrangement permuted ?_,
          rearranges_trans permuted (rearranges_enlarge preserved le_rfl (by omega))⟩
        obtain ⟨⟨position, lower, upper, value⟩, ranked⟩ := selected
        refine ⟨⟨position, lower, by omega, value⟩, ?_⟩
        have whole := rank_in_left partitioned.1 ref lo hi partitioned.2
          (partitioned.1.read ref partitioned.2) position split lower upper
        rw [value] at whole
        simpa only [whole] using ranked
      · have subDistinct : Set.InjOn (partitioned.1.read ref) (Set.Ico (partitioned.2 + 1) hi) := by
          intro first hf second hs same
          exact keyDistinct ⟨by have := hf.1; omega, hf.2⟩ ⟨by have := hs.1; omega, hs.2⟩ same
        obtain ⟨selected, preserved⟩ := ih partitioned.1 (partitioned.2 + 1) hi
          (requested - (partitioned.2 - lo) - 1) (by omega) (by omega) (by omega)
          (by omega) subDistinct result later
        refine ⟨statistic_before_rearrangement permuted ?_,
          rearranges_trans permuted (rearranges_enlarge preserved (by omega) le_rfl)⟩
        obtain ⟨⟨position, lower, upper, value⟩, ranked⟩ := selected
        refine ⟨⟨position, by omega, upper, value⟩, ?_⟩
        have whole := rank_in_right partitioned.1 ref lo hi partitioned.2
          (partitioned.1.read ref partitioned.2) position split (by omega) upper
        rw [value] at whole
        omega
end SelectionAnalysis
