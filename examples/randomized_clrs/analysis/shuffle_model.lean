import Algo2LeanLib.Footprint
import Algo2LeanProbability.Call
import Mathlib.Logic.Equiv.Basic

/-!
A finite mathematical model of Fisher-Yates shuffle. Each stage chooses a
uniform position in the remaining interval, exchanges two sequence cells, and
charges the two operation counters. This file establishes properties of the
model; the generated algorithm is connected to it in the shuffle analysis.
-/

noncomputable section
namespace ShuffleAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open scoped ENNReal

/-- Exchange two cells of an existing sequence and charge one draw and one swap.
All reads use the initial heap, including when both indices are equal. -/
def swapStep (heap : Heap) (ref : SeqRef) (first chosen : Int) : Heap :=
  (((heap.tick "random_draws").write ref first (heap.read ref chosen)).write
    ref chosen (heap.read ref first)).tick "swaps"

@[simp] theorem swapStep_nextRef (heap : Heap) (ref : SeqRef) (first chosen : Int) :
    (swapStep heap ref first chosen).nextRef = heap.nextRef := rfl

@[simp] theorem swapStep_clocks (heap : Heap) (ref : SeqRef) (first chosen : Int)
    (clock : String) :
    (swapStep heap ref first chosen).clocks clock = heap.clocks clock +
      (if clock = "random_draws" ∨ clock = "swaps" then 1 else 0) := by
  by_cases draws : clock = "random_draws"
  · subst clock; simp [swapStep]
  by_cases swaps : clock = "swaps"
  · subst clock; simp [swapStep]
  simp [swapStep, Heap.tick, draws, swaps]

/-- A swap preserves the caller's unrelated sequences, objects, and collections. -/
theorem swapStep_frame (heap : Heap) (ref : SeqRef) (first chosen : Int) :
    heap.Footprint (swapStep heap ref first chosen) [ref] [] [] := by
  exact (((Heap.Footprint.refl heap [ref] [] []).tick "random_draws").write
    ref first (heap.read ref chosen) (by simp)).write
    ref chosen (heap.read ref first) (by simp) |>.tick "swaps"

/-- Reading the exchanged sequence is precomposition with a transposition. -/
theorem swapStep_read (heap : Heap) (ref : SeqRef) (first chosen index : Int) :
    (swapStep heap ref first chosen).read ref index =
      heap.read ref (Equiv.swap first chosen index) := by
  by_cases atChosen : index = chosen
  · subst index; simp [swapStep]
  by_cases atFirst : index = first
  · subst index; simp [swapStep, atChosen]
  simp [swapStep, Heap.read, Heap.write, Equiv.swap_apply_def, atChosen, atFirst]

/-- Uniformly shuffle `count` successive cells, starting at `first`. -/
def shuffleLaw (heap : Heap) (ref : SeqRef) (first : Int) : Nat → PMF Heap
  | 0 => PMF.pure heap
  | count + 1 =>
      (uniformInt first (first + (count + 1 : Nat)) (by omega)).bind
        (fun chosen => shuffleLaw (swapStep heap ref first chosen) ref (first + 1) count)

/-- A final sequence is obtained by a permutation of positions that fixes every
position outside the specified interval. This also handles repeated values. -/
def Rearranges (before after : Heap) (ref : SeqRef) (lo hi : Int) : Prop :=
  ∃ permutation : Equiv.Perm Int,
    (∀ index, index < lo ∨ hi ≤ index → permutation index = index) ∧
    ∀ index, after.read ref index = before.read ref (permutation index)

/-- All heaps in the shuffle law preserve allocation and unrelated storage. -/
theorem shuffleLaw_frame (count : Nat) (heap : Heap) (ref : SeqRef) (first : Int)
    (final : Heap) (possible : final ∈ (shuffleLaw heap ref first count).support) :
    final.nextRef = heap.nextRef ∧ heap.Footprint final [ref] [] [] := by
  induction count generalizing heap first with
  | zero =>
      have same : final = heap := by simpa [shuffleLaw] using possible
      subst final
      exact ⟨rfl, Heap.Footprint.refl ..⟩
  | succ count ih =>
      obtain ⟨chosen, _, later⟩ := (PMF.mem_support_bind_iff _ _ _).1 possible
      obtain ⟨refs, frame⟩ := ih (swapStep heap ref first chosen) (first + 1) later
      exact ⟨refs, (swapStep_frame heap ref first chosen).trans frame⟩

/-- Both charged operation counts are exactly the number of remaining cells;
all other clocks are preserved, even when the caller has nonzero counters. -/
theorem shuffleLaw_clocks (count : Nat) (heap : Heap) (ref : SeqRef) (first : Int)
    (final : Heap) (possible : final ∈ (shuffleLaw heap ref first count).support)
    (clock : String) :
    final.clocks clock = heap.clocks clock +
      (if clock = "random_draws" ∨ clock = "swaps" then count else 0) := by
  induction count generalizing heap first with
  | zero =>
      have same : final = heap := by simpa [shuffleLaw] using possible
      subst final; simp
  | succ count ih =>
      obtain ⟨chosen, _, later⟩ := (PMF.mem_support_bind_iff _ _ _).1 possible
      rw [ih (swapStep heap ref first chosen) (first + 1) later, swapStep_clocks]
      split_ifs <;> omega

/-- Every supported outcome is an in-place permutation of the selected interval. -/
theorem shuffleLaw_rearranges (count : Nat) (heap : Heap) (ref : SeqRef) (first : Int)
    (final : Heap) (possible : final ∈ (shuffleLaw heap ref first count).support) :
    Rearranges heap final ref first (first + (count : Int)) := by
  induction count generalizing heap first with
  | zero =>
      have same : final = heap := by simpa [shuffleLaw] using possible
      subst final
      exact ⟨Equiv.refl _, fun _ _ => rfl, fun _ => rfl⟩
  | succ count ih =>
      obtain ⟨chosen, chosenSupport, later⟩ := (PMF.mem_support_bind_iff _ _ _).1 possible
      have bounds : first ≤ chosen ∧ chosen < first + (count + 1 : Nat) :=
        (uniformInt_support ..).1 chosenSupport
      obtain ⟨permutation, outside, values⟩ := ih (swapStep heap ref first chosen) (first + 1) later
      refine ⟨permutation.trans (Equiv.swap first chosen), ?_, ?_⟩
      · intro index beyond
        have farther : index < first + 1 ∨ first + 1 + (count : Int) ≤ index := by omega
        simp only [Equiv.trans_apply, outside index farther]
        apply Equiv.swap_apply_of_ne_of_ne <;> omega
      · intro index
        rw [values index, swapStep_read]
        rfl

/-- The model exposes the remaining-loop expectation as one finite average. -/
theorem shuffleLaw_expected_succ (heap : Heap) (ref : SeqRef) (first : Int)
    (count : Nat) (reward : Heap → ℝ≥0∞) :
    (∑' final, shuffleLaw heap ref first (count + 1) final * reward final) =
      ∑ chosen ∈ Finset.Ico first (first + (count + 1 : Nat)),
        (∑' final, shuffleLaw (swapStep heap ref first chosen) ref (first + 1) count final *
          reward final) * ((count + 1 : Nat) : ℝ≥0∞)⁻¹ := by
  change pmfExpected (shuffleLaw heap ref first (count + 1)) reward = _
  rw [shuffleLaw, pmfExpected_bind, pmfExpected_uniformInt]
  simp [pmfExpected]

end ShuffleAnalysis
