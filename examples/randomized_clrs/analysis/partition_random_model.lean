import Algo.partition_model.Analysis

/-!
Randomized partition reuses the deterministic partition model after moving a
uniformly selected input cell to the pivot position. The joint law retains the
mutated heap, pivot index, and all clocks for subsequent recursive algorithms.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace PartitionAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open scoped ENNReal

/-- Move the chosen pivot to the final cell, charging one draw and one swap. -/
def choosePivot (heap : Heap) (ref : SeqRef) (position hi : Int) : Heap :=
  exchange (heap.tick "random_draws") ref position (hi - 1)

/-- Joint final heap and returned boundary after randomized partition. -/
def randomizedPartitionLaw (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi) :
    PMF (Heap × Int) :=
  (uniformInt lo hi nonempty).map (fun position => partitionResult (choosePivot heap ref position hi) ref lo hi)

/-- The pivot returned by the deterministic phase is the originally chosen value. -/
theorem chosen_pivot (heap : Heap) (ref : SeqRef) (lo hi position : Int) (nonempty : lo < hi) :
    let result := partitionResult (choosePivot heap ref position hi) ref lo hi
    result.1.read ref result.2 = heap.read ref position := by
  have result := (partitionResult_partitioned (choosePivot heap ref position hi) ref lo hi nonempty).2.2.1
  simpa [choosePivot, exchange_read] using result

/-- Projecting the final heap onto its pivot recovers the original uniform draw. -/
theorem pivot_value_law (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi) :
    (randomizedPartitionLaw heap ref lo hi nonempty).map (fun result => result.1.read ref result.2) =
      (uniformInt lo hi nonempty).map (heap.read ref) := by
  rw [randomizedPartitionLaw, PMF.map_comp]
  congr 1
  funext position
  exact chosen_pivot heap ref lo hi position nonempty

/-- Every supported randomized outcome satisfies the partition inequalities,
permutes the original interval, and preserves unrelated storage. -/
theorem randomizedPartitionLaw_correct (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (nonempty : lo < hi) (result : Heap × Int)
    (possible : result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support) :
    Partitioned result.1 ref lo hi result.2 (result.1.read ref result.2) ∧
    Rearranges heap result.1 ref lo hi ∧ result.1.nextRef = heap.nextRef ∧
    heap.Footprint result.1 [ref] [] [] := by
  obtain ⟨position, support, rfl⟩ := (PMF.mem_support_map_iff ..).1 possible
  have bounds := (uniformInt_support ..).1 support
  have partitioned := partitionResult_partitioned (choosePivot heap ref position hi) ref lo hi nonempty
  have frame := partitionResult_frame (choosePivot heap ref position hi) ref lo hi
  refine ⟨?_, ?_, frame.1, ?_⟩
  · rw [chosen_pivot heap ref lo hi position nonempty]
    simpa [choosePivot, exchange_read] using partitioned
  · have swapped := exchange_rearranges (heap.tick "random_draws") ref position (hi - 1) lo hi
      bounds (by constructor <;> omega)
    have later := partitionResult_rearranges (choosePivot heap ref position hi) ref lo hi nonempty
    have combined := rearranges_trans swapped later
    simpa only [Rearranges, ShuffleAnalysis.Rearranges, Heap.read_tick] using combined
  · exact ((Heap.Footprint.refl heap [ref] [] []).tick "random_draws").trans
      ((exchange_frame ..).trans frame.2)

/-- Randomized partition adds one draw and pivot-selection swap to deterministic partition. -/
theorem randomizedPartitionLaw_cost (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (nonempty : lo < hi) (result : Heap × Int)
    (possible : result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support) :
    Heap.cost heap result.1 "comparisons" = (hi - lo - 1).toNat ∧
    Heap.cost heap result.1 "random_draws" = 1 ∧
    2 ≤ Heap.cost heap result.1 "swaps" ∧
    Heap.cost heap result.1 "swaps" ≤ (hi - lo).toNat + 1 := by
  obtain ⟨position, _, rfl⟩ := (PMF.mem_support_map_iff ..).1 possible
  have comparisons := scan_comparisons (hi - lo - 1).toNat
    (choosePivot heap ref position hi) ref
    ((choosePivot heap ref position hi).read ref (hi - 1)) lo lo
  have draws := scan_other_clock (hi - lo - 1).toNat
    (choosePivot heap ref position hi) ref
    ((choosePivot heap ref position hi).read ref (hi - 1)) lo lo "random_draws" (by decide) (by decide)
  have swaps := scan_swaps (hi - lo - 1).toNat
    (choosePivot heap ref position hi) ref
    ((choosePivot heap ref position hi).read ref (hi - 1)) lo lo
  have comparisonClock : (choosePivot heap ref position hi).clocks "comparisons" =
      heap.clocks "comparisons" := by simp [choosePivot]
  have drawClock : (choosePivot heap ref position hi).clocks "random_draws" =
      heap.clocks "random_draws" + 1 := by simp [choosePivot]
  have swapClock : (choosePivot heap ref position hi).clocks "swaps" =
      heap.clocks "swaps" + 1 := by simp [choosePivot]
  rw [comparisonClock] at comparisons
  rw [drawClock] at draws
  rw [swapClock] at swaps
  unfold Heap.cost partitionResult
  omega

/-- For distinct input keys, every specified input key is the returned pivot
with probability exactly the reciprocal of the interval length. -/
theorem pivot_probability (heap : Heap) (ref : SeqRef) (lo hi position : Int)
    (nonempty : lo < hi) (member : lo ≤ position ∧ position < hi)
    (distinct : Set.InjOn (heap.read ref) (Set.Ico lo hi)) :
    pmfExpected (randomizedPartitionLaw heap ref lo hi nonempty)
      (fun result => if result.1.read ref result.2 = heap.read ref position then 1 else 0) =
      ((hi - lo).toNat : ℝ≥0∞)⁻¹ := by
  classical
  rw [randomizedPartitionLaw, pmfExpected_map]
  simp_rw [chosen_pivot heap ref lo hi _ nonempty]
  unfold pmfExpected
  calc
    _ = ∑' chosen, uniformInt lo hi nonempty chosen *
        (if chosen = position then (1 : ℝ≥0∞) else 0) := by
      apply tsum_congr
      intro chosen
      by_cases possible : lo ≤ chosen ∧ chosen < hi
      · have same : heap.read ref chosen = heap.read ref position ↔ chosen = position :=
          ⟨fun equal => distinct possible member equal, fun equal => by rw [equal]⟩
        simp only [same]
      · simp [uniformInt_apply, possible]
    _ = uniformInt lo hi nonempty position := by simp
    _ = _ := uniformInt_mass lo hi position nonempty member.1 member.2

/-- The imported partition leaves every clock except its three named clocks unchanged. -/
theorem randomizedPartitionLaw_other_clock (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (nonempty : lo < hi) (result : Heap × Int)
    (possible : result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support)
    (clock : String) (notComparisons : clock ≠ "comparisons") (notSwaps : clock ≠ "swaps")
    (notDraws : clock ≠ "random_draws") : result.1.clocks clock = heap.clocks clock := by
  obtain ⟨position, _, rfl⟩ := (PMF.mem_support_map_iff ..).1 possible
  unfold partitionResult
  rw [scan_other_clock _ _ _ _ _ _ clock notComparisons notSwaps]
  simp [choosePivot, notSwaps, Heap.tick, notDraws]

/-- Raw comparison-clock equality composes with recursive calls without natural
subtraction: every supported partition adds exactly n-1 comparisons. -/
theorem randomizedPartitionLaw_comparison_clock (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (nonempty : lo < hi) (result : Heap × Int)
    (possible : result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support) :
    result.1.clocks "comparisons" = heap.clocks "comparisons" + (hi - lo - 1).toNat := by
  obtain ⟨position, _, rfl⟩ := (PMF.mem_support_map_iff ..).1 possible
  unfold partitionResult
  rw [scan_comparisons]
  simp [choosePivot]

/-- Every supported partition outcome preserves monotonicity of all clocks. -/
theorem randomizedPartitionLaw_clock_mono (heap : Heap) (ref : SeqRef) (lo hi : Int)
    (nonempty : lo < hi) (result : Heap × Int)
    (possible : result ∈ (randomizedPartitionLaw heap ref lo hi nonempty).support)
    (clock : String) : heap.clocks clock ≤ result.1.clocks clock := by
  obtain ⟨position, _, rfl⟩ := (PMF.mem_support_map_iff ..).1 possible
  have initial : heap.clocks clock ≤ (choosePivot heap ref position hi).clocks clock := by
    simp [choosePivot, Heap.tick]
    split_ifs <;> omega
  apply initial.trans
  unfold partitionResult
  by_cases comparisons : clock = "comparisons"
  · subst clock
    rw [scan_comparisons]
    omega
  by_cases swaps : clock = "swaps"
  · subst clock
    exact le_trans (Nat.le_add_right _ 1) (scan_swaps ..).1
  · rw [scan_other_clock _ _ _ _ _ _ clock comparisons swaps]

end PartitionAnalysis
