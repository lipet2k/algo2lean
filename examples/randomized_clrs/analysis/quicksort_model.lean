import Algo.partition_rank.Analysis

/-!
A finite-depth joint law for randomized quicksort. Each branch reuses the complete
partition law and passes its resulting heap to the recursive calls. The depth
parameter is only a structural recursion aid; an interval's length bounds it.
-/

noncomputable section
namespace QuicksortAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis
open scoped ENNReal

/-- The array is nondecreasing throughout the half-open interval. -/
def Sorted (heap : Heap) (ref : SeqRef) (lo hi : Int) : Prop :=
  ∀ first second, lo ≤ first → first < second → second < hi →
    heap.read ref first ≤ heap.read ref second

/-- Recursive joint heap law, retaining every operation counter. -/
def quicksortLaw : Nat → Heap → SeqRef → Int → Int → PMF Heap
  | 0, heap, _, _, _ => PMF.pure (heap.tick "quicksort_calls")
  | fuel + 1, heap, ref, lo, hi =>
      let charged := heap.tick "quicksort_calls"
      if large : 1 < hi - lo then
        (randomizedPartitionLaw charged ref lo hi (by omega)).bind (fun result =>
          (quicksortLaw fuel result.1 ref lo result.2).bind
            (fun left => quicksortLaw fuel left ref (result.2 + 1) hi))
      else PMF.pure charged

/-- Every recursive sort preserves allocation and storage outside the input sequence. -/
theorem quicksortLaw_frame (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (final : Heap) (possible : final ∈ (quicksortLaw fuel heap ref lo hi).support) :
    final.nextRef = heap.nextRef ∧ heap.Footprint final [ref] [] [] := by
  induction fuel generalizing heap lo hi final with
  | zero =>
      have same : final = heap.tick "quicksort_calls" := by simpa [quicksortLaw] using possible
      subst final
      exact ⟨rfl, (Heap.Footprint.refl heap [ref] [] []).tick "quicksort_calls"⟩
  | succ fuel ih =>
      simp only [quicksortLaw] at possible
      split_ifs at possible with large
      · obtain ⟨partitioned, selected, rest⟩ := (PMF.mem_support_bind_iff ..).1 possible
        obtain ⟨left, leftPossible, rightPossible⟩ := (PMF.mem_support_bind_iff ..).1 rest
        have frame := (randomizedPartitionLaw_correct (heap.tick "quicksort_calls") ref lo hi
          (by omega) partitioned selected).2.2
        have leftFrame := ih partitioned.1 lo partitioned.2 left leftPossible
        have rightFrame := ih left (partitioned.2 + 1) hi final rightPossible
        exact ⟨rightFrame.1.trans (leftFrame.1.trans frame.1),
          ((((Heap.Footprint.refl heap [ref] [] []).tick "quicksort_calls").trans frame.2).trans
            leftFrame.2).trans rightFrame.2⟩
      · have same : final = heap.tick "quicksort_calls" := by simpa using possible
        subst final
        exact ⟨rfl, (Heap.Footprint.refl heap [ref] [] []).tick "quicksort_calls"⟩

/-- An interval permutation leaves every outside cell unchanged. -/
theorem rearranges_outside {before after : Heap} {ref : SeqRef} {lo hi : Int}
    (permuted : Rearranges before after ref lo hi) (index : Int) (outside : index < lo ∨ hi ≤ index) :
    after.read ref index = before.read ref index := by
  obtain ⟨permutation, fixed, values⟩ := permuted
  rw [values, fixed index outside]

/-- A permutation within a smaller interval also preserves the containing interval. -/
theorem rearranges_expand {before after : Heap} {ref : SeqRef} {lo hi outerLo outerHi : Int}
    (permuted : Rearranges before after ref lo hi) (lower : outerLo ≤ lo) (upper : hi ≤ outerHi) :
    Rearranges before after ref outerLo outerHi := by
  obtain ⟨permutation, fixed, values⟩ := permuted
  exact ⟨permutation, fun index outside => fixed index (by omega), values⟩

/-- A pointwise property of all interval values survives an interval permutation. -/
theorem rearranges_forall {before after : Heap} {ref : SeqRef} {lo hi : Int}
    (permuted : Rearranges before after ref lo hi) (property : Int → Prop)
    (holds : ∀ index, lo ≤ index → index < hi → property (before.read ref index)) :
    ∀ index, lo ≤ index → index < hi → property (after.read ref index) := by
  obtain ⟨permutation, fixed, values⟩ := permuted
  intro index lower upper
  rw [values]
  have inside := perm_interval permutation lo hi fixed index ⟨lower, upper⟩
  exact holds _ inside.1 inside.2

/-- Sorting the two partition pieces yields a sorted complete interval. -/
theorem sorted_partition (partitioned left final : Heap) (ref : SeqRef) (lo hi boundary pivot : Int)
    (split : Partitioned partitioned ref lo hi boundary pivot)
    (leftPermutation : Rearranges partitioned left ref lo boundary)
    (leftSorted : Sorted left ref lo boundary)
    (rightPermutation : Rearranges left final ref (boundary + 1) hi)
    (rightSorted : Sorted final ref (boundary + 1) hi) : Sorted final ref lo hi := by
  obtain ⟨low, high, pivotValue, small, large⟩ := split
  have leftSmall := rearranges_forall leftPermutation (fun value => value ≤ pivot) small
  have leftPivot : left.read ref boundary = pivot := by
    rw [rearranges_outside leftPermutation boundary (Or.inr le_rfl), pivotValue]
  have finalPivot : final.read ref boundary = pivot := by
    rw [rearranges_outside rightPermutation boundary (Or.inl (by omega)), leftPivot]
  have rightLarge : ∀ index, boundary + 1 ≤ index → index < hi → pivot < final.read ref index := by
    apply rearranges_forall rightPermutation
    intro index lower upper
    rw [rearranges_outside leftPermutation index (Or.inr (by omega))]
    exact large index (by omega) upper
  have finalSmall : ∀ index, lo ≤ index → index < boundary → final.read ref index ≤ pivot := by
    intro index lower upper
    rw [rearranges_outside rightPermutation index (Or.inl (by omega))]
    exact leftSmall index lower upper
  intro first second lower ordered upper
  by_cases secondLeft : second < boundary
  · rw [rearranges_outside rightPermutation first (Or.inl (by omega)),
      rearranges_outside rightPermutation second (Or.inl (by omega))]
    exact leftSorted first second lower ordered secondLeft
  by_cases secondPivot : second = boundary
  · subst second
    rw [finalPivot]
    exact finalSmall first lower ordered
  have secondRight : boundary + 1 ≤ second := by omega
  by_cases firstLeft : first < boundary
  · exact le_trans (finalSmall first lower firstLeft) (le_of_lt (rightLarge second secondRight upper))
  by_cases firstPivot : first = boundary
  · subst first
    rw [finalPivot]
    exact le_of_lt (rightLarge second secondRight upper)
  exact rightSorted first second (by omega) ordered upper

/-- With enough recursive depth, every outcome is a sorted permutation of the
input interval. Equal keys are permitted. -/
theorem quicksortLaw_correct (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (enough : (hi - lo).toNat ≤ fuel) (final : Heap)
    (possible : final ∈ (quicksortLaw fuel heap ref lo hi).support) :
    Sorted final ref lo hi ∧ Rearranges heap final ref lo hi := by
  induction fuel generalizing heap lo hi final with
  | zero =>
      have same : final = heap.tick "quicksort_calls" := by simpa [quicksortLaw] using possible
      subst final
      exact ⟨by unfold Sorted; intros; omega, ⟨Equiv.refl _, fun _ _ => rfl, fun _ => rfl⟩⟩
  | succ fuel ih =>
      simp only [quicksortLaw] at possible
      split_ifs at possible with large
      · obtain ⟨partitioned, selected, rest⟩ := (PMF.mem_support_bind_iff ..).1 possible
        obtain ⟨left, leftPossible, rightPossible⟩ := (PMF.mem_support_bind_iff ..).1 rest
        obtain ⟨split, permutation, _⟩ := randomizedPartitionLaw_correct (heap.tick "quicksort_calls") ref lo hi
          (by omega) partitioned selected
        have bounds := split.1
        have boundHigh := split.2.1
        obtain ⟨leftSorted, leftPermutation⟩ := ih partitioned.1 lo partitioned.2
          (by omega) left leftPossible
        obtain ⟨rightSorted, rightPermutation⟩ := ih left (partitioned.2 + 1) hi
          (by omega) final rightPossible
        refine ⟨sorted_partition partitioned.1 left final ref lo hi partitioned.2
          (partitioned.1.read ref partitioned.2) split leftPermutation leftSorted rightPermutation rightSorted, ?_⟩
        have combined := rearranges_trans permutation
          (rearranges_trans (rearranges_expand leftPermutation le_rfl (by omega))
            (rearranges_expand rightPermutation (by omega) le_rfl))
        simpa only [Rearranges, ShuffleAnalysis.Rearranges, Heap.read_tick] using combined
      · have same : final = heap.tick "quicksort_calls" := by simpa using possible
        subst final
        exact ⟨by unfold Sorted; intros; omega, ⟨Equiv.refl _, fun _ _ => rfl, fun _ => rfl⟩⟩

end QuicksortAnalysis
