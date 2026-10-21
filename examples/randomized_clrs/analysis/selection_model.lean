import Algo.partition_rank.Analysis

/-!
RANDOMIZED-SELECT reuses the joint randomized partition law. The finite fuel
parameter bounds recursive depth; valid input intervals need at most their
length in fuel. Every recursive step retains the partition's returned heap.
-/

noncomputable section
namespace SelectionAnalysis
open Algo2LeanGenerated Algo2LeanProbability PartitionAnalysis
open scoped ENNReal

/-- A finite recursive model of selection, retaining the exact heap and output.
The fuel-zero branch is unreachable when fuel bounds the positive interval length. -/
def selectionLaw : Nat → Heap → SeqRef → Int → Int → Int → PMF (Heap × Int)
  | 0, heap, _, _, _, _ => PMF.pure (heap, 0)
  | fuel + 1, heap, ref, lo, hi, requested =>
      let charged := heap.tick "selection_calls"
      if hi - lo = 1 then PMF.pure (charged, heap.read ref lo)
      else if nonempty : lo < hi then
        (randomizedPartitionLaw charged ref lo hi nonempty).bind (fun result =>
          if requested = result.2 - lo then PMF.pure (result.1, result.1.read ref result.2)
          else if requested < result.2 - lo then
            selectionLaw fuel result.1 ref lo result.2 requested
          else selectionLaw fuel result.1 ref (result.2 + 1) hi (requested - (result.2 - lo) - 1))
      else PMF.pure (charged, 0)

/-- Selection preserves allocation and all storage outside the selected sequence. -/
theorem selectionLaw_frame (fuel : Nat) (heap : Heap) (ref : SeqRef) (lo hi requested : Int)
    (result : Heap × Int) (possible : result ∈ (selectionLaw fuel heap ref lo hi requested).support) :
    result.1.nextRef = heap.nextRef ∧ heap.Footprint result.1 [ref] [] [] := by
  induction fuel generalizing heap lo hi requested result with
  | zero =>
    have same : result = (heap, 0) := by simpa [selectionLaw] using possible
    subst result
    exact ⟨rfl, Heap.Footprint.refl ..⟩
  | succ fuel ih =>
    simp only [selectionLaw] at possible
    split_ifs at possible with singleton nonempty
    · have same : result = (heap.tick "selection_calls", heap.read ref lo) := by simpa using possible
      subst result
      exact ⟨rfl, (Heap.Footprint.refl heap [ref] [] []).tick "selection_calls"⟩
    · obtain ⟨partitioned, belongs, later⟩ := (PMF.mem_support_bind_iff ..).1 possible
      have frame := (randomizedPartitionLaw_correct (heap.tick "selection_calls") ref lo hi
        nonempty partitioned belongs).2.2
      split_ifs at later with found before
      · have same : result = (partitioned.1, partitioned.1.read ref partitioned.2) := by simpa using later
        subst result
        exact ⟨frame.1, ((Heap.Footprint.refl heap [ref] [] []).tick "selection_calls").trans frame.2⟩
      · obtain ⟨refs, storage⟩ := ih partitioned.1 lo partitioned.2 requested result later
        exact ⟨refs.trans frame.1,
          (((Heap.Footprint.refl heap [ref] [] []).tick "selection_calls").trans frame.2).trans storage⟩
      · obtain ⟨refs, storage⟩ := ih partitioned.1 (partitioned.2 + 1) hi
          (requested - (partitioned.2 - lo) - 1) result later
        exact ⟨refs.trans frame.1,
          (((Heap.Footprint.refl heap [ref] [] []).tick "selection_calls").trans frame.2).trans storage⟩
    · have same : result = (heap.tick "selection_calls", 0) := by simpa using possible
      subst result
      exact ⟨rfl, (Heap.Footprint.refl heap [ref] [] []).tick "selection_calls"⟩

end SelectionAnalysis
