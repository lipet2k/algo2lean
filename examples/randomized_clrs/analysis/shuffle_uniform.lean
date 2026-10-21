import Algo.shuffle_model.Analysis
import Algo.shuffle_permutation.Analysis

/-!
The heap-based shuffle law induces the uniform law on positional permutations
of its finite interval. Expectations are stated for arbitrary observations of
that interval, so clients need no assumptions about distinct stored values.
-/

noncomputable section
namespace ShuffleAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open scoped ENNReal

/-- Read a finite interval without copying or changing its shared sequence. -/
def prefixValues (heap : Heap) (ref : SeqRef) (first : Int) (n : Nat) : Fin n → Int :=
  fun index => heap.read ref (first + (index.val : Int))

/-- Uniform integer sampling is uniform sampling of the finite offset. -/
theorem uniformInt_as_fin (first : Int) (n : Nat) :
    uniformInt first (first + (n + 1 : Nat)) (by omega) =
      (PMF.uniformOfFintype (Fin (n + 1))).map
        (fun index => first + (index.val : Int)) := by
  classical
  ext value
  by_cases within : first ≤ value ∧ value < first + (n + 1 : Nat)
  · let index : Fin (n + 1) := ⟨(value - first).toNat, by omega⟩
    have chosen : first + (index.val : Int) = value := by
      dsimp [index]; omega
    rw [PMF.map_apply, tsum_eq_single index]
    · rw [uniformInt_mass _ _ _ (by omega) within.1 within.2]
      simp only [chosen, ↓reduceIte, PMF.uniformOfFintype_apply, Fintype.card_fin,
        add_sub_cancel_left, Int.toNat_natCast]
    · intro other different
      have unequal : value ≠ first + (other.val : Int) := by
        intro same
        apply different
        apply Fin.ext
        dsimp [index] at *
        omega
      simp [unequal]
  · have none (index : Fin (n + 1)) : value ≠ first + (index.val : Int) := by omega
    rw [uniformInt_apply, if_neg within, PMF.map_apply]
    simp [none]

/-- Changing an observation only on zero-mass outcomes preserves expectation. -/
theorem expectation_congr_support {A : Type*} (law : PMF A) (first second : A → ℝ≥0∞)
    (same : ∀ value ∈ law.support, first value = second value) :
    pmfExpected law first = pmfExpected law second :=
  pmfExpected_congr_support law first second same

/-- Split the selected interval into its first cell and the remaining suffix. -/
theorem prefixValues_cons (heap : Heap) (ref : SeqRef) (first : Int) (n : Nat) :
    prefixValues heap ref first (n + 1) =
      Fin.cons (heap.read ref first) (prefixValues heap ref (first + 1) n) := by
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · simp [prefixValues]
  · simp [prefixValues, Nat.cast_add, add_left_comm, add_comm]

/-- The suffix shuffle leaves the already-selected first cell unchanged. -/
theorem suffix_first (heap : Heap) (ref : SeqRef) (first : Int) (n : Nat)
    (final : Heap) (possible : final ∈ (shuffleLaw heap ref (first + 1) n).support) :
    final.read ref first = heap.read ref first := by
  obtain ⟨permutation, outside, values⟩ := shuffleLaw_rearranges n heap ref (first + 1) final possible
  rw [values, outside first (Or.inl (by omega))]

/-- The first transposition followed by a tail permutation has the standard
finite-permutation decomposition. -/
theorem swap_prefix (heap : Heap) (ref : SeqRef) (first : Int) (n : Nat)
    (chosen : Fin (n + 1)) (tail : Equiv.Perm (Fin n)) :
    Fin.cons (heap.read ref (first + (chosen.val : Int)))
      (fun index => (swapStep heap ref first (first + (chosen.val : Int))).read ref
        (first + 1 + ((tail index).val : Int))) =
      (fun index => heap.read ref
        (first + ((Equiv.Perm.decomposeFin.symm (chosen, tail) index).val : Int))) := by
  have injective : Function.Injective (fun index : Fin (n + 1) => first + (index.val : Int)) := by
    intro a b same
    apply Fin.ext
    change first + (a.val : Int) = first + (b.val : Int) at same
    omega
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · simp
  · simp only [Fin.cons_succ, Equiv.Perm.decomposeFin_symm_apply_succ, swapStep_read]
    have mapped := injective.swap_apply 0 chosen (tail index).succ
    have equal : first + 1 + ((tail index).val : Int) = first + (((tail index).succ).val : Int) := by
      simp [Nat.cast_add, add_assoc, add_comm]
    rw [equal]
    simpa using congrArg (heap.read ref) mapped

/-- Every observation of the shuffled interval has its expectation under a
uniform positional permutation. Equal input values are permitted. -/
theorem shuffleLaw_uniform (n : Nat) (heap : Heap) (ref : SeqRef) (first : Int)
    (reward : (Fin n → Int) → ℝ≥0∞) :
    pmfExpected (shuffleLaw heap ref first n)
      (fun final => reward (prefixValues final ref first n)) =
      pmfExpected (permutationLaw n)
        (fun permutation => reward (fun index => heap.read ref (first + ((permutation index).val : Int)))) := by
  induction n generalizing heap first with
  | zero =>
      simp only [shuffleLaw, permutationLaw, pmfExpected_pure]
      rfl
  | succ n ih =>
      rw [shuffleLaw, permutationLaw, pmfExpected_bind, pmfExpected_bind, uniformInt_as_fin,
        pmfExpected_map]
      apply congrArg (pmfExpected (PMF.uniformOfFintype (Fin (n + 1))))
      funext chosen
      rw [pmfExpected_map]
      let swapped := swapStep heap ref first (first + (chosen.val : Int))
      have firstValue : swapped.read ref first = heap.read ref (first + (chosen.val : Int)) := by
        simp [swapped, swapStep_read]
      calc
        _ = pmfExpected (shuffleLaw swapped ref (first + 1) n)
            (fun final => reward (Fin.cons (swapped.read ref first)
              (prefixValues final ref (first + 1) n))) := by
          apply expectation_congr_support
          intro final possible
          rw [prefixValues_cons, suffix_first swapped ref first n final possible]
        _ = pmfExpected (permutationLaw n)
            (fun tail => reward (Fin.cons (swapped.read ref first)
              (fun index => swapped.read ref (first + 1 + ((tail index).val : Int))))) := by
          exact ih swapped (first + 1) (fun values => reward (Fin.cons (swapped.read ref first) values))
        _ = _ := by
          apply congrArg (pmfExpected (permutationLaw n))
          funext tail
          rw [firstValue, swap_prefix]

end ShuffleAnalysis
