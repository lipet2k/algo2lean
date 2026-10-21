import Algo2LeanProbability
import Mathlib.GroupTheory.Perm.Fin

/-!
The positional Fisher-Yates law is uniform over finite permutations. This
mathematical decomposition supplies the counting part of the shuffle proof;
it is separate from the generated algorithm's operational-semantics argument.
-/

noncomputable section
namespace ShuffleAnalysis
open Algo2LeanProbability
open scoped ENNReal

/-- Independent uniform choices form the uniform distribution on a product. -/
theorem uniform_product (A B : Type*) [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype A).bind
      (fun a => (PMF.uniformOfFintype B).map (fun b => (a, b))) =
      PMF.uniformOfFintype (A × B) := by
  classical
  ext pair
  rcases pair with ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, Prod.mk.injEq, PMF.uniformOfFintype_apply,
    Fintype.card_prod, ENNReal.mul_inv, ite_and]

/-- A bijection preserves a uniform distribution. -/
theorem uniform_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (equivalence : A ≃ B) :
    (PMF.uniformOfFintype A).map equivalence = PMF.uniformOfFintype B := by
  classical
  ext value
  rw [PMF.map_apply]
  have same (a : A) : value = equivalence a ↔ a = equivalence.symm value := by
    constructor
    · intro h; exact equivalence.injective (by simp [h])
    · intro h; simp [h]
  simp [same, PMF.uniformOfFintype_apply, Fintype.card_congr equivalence]

/-- Choose the first image uniformly, then recursively permute the other
positions. The decomposition uses exactly the transpositions of Fisher-Yates. -/
def permutationLaw : (n : Nat) → PMF (Equiv.Perm (Fin n))
  | 0 => PMF.pure (Equiv.refl _)
  | n + 1 => (PMF.uniformOfFintype (Fin (n + 1))).bind
      (fun chosen => (permutationLaw n).map
        (fun tail => Equiv.Perm.decomposeFin.symm (chosen, tail)))

/-- Every positional permutation has equal probability. -/
theorem permutationLaw_uniform (n : Nat) :
    permutationLaw n = PMF.uniformOfFintype (Equiv.Perm (Fin n)) := by
  induction n with
  | zero =>
      ext permutation
      have same : permutation = Equiv.refl _ := Subsingleton.elim _ _
      simp [permutationLaw, same, PMF.uniformOfFintype_apply]
  | succ n ih =>
      rw [permutationLaw, ih]
      have product := uniform_product (Fin (n + 1)) (Equiv.Perm (Fin n))
      have mapped := congrArg (PMF.map Equiv.Perm.decomposeFin.symm) product
      rw [PMF.map_bind] at mapped
      simp only [PMF.map_comp, Function.comp_def] at mapped
      rw [mapped, uniform_equiv]

/-- The mass of any specified labeled permutation is exactly `1 / n!`. -/
theorem permutationLaw_mass (n : Nat) (permutation : Equiv.Perm (Fin n)) :
    permutationLaw n permutation = (n.factorial : ℝ≥0∞)⁻¹ := by
  rw [permutationLaw_uniform, PMF.uniformOfFintype_apply]
  simp [Fintype.card_perm]

end ShuffleAnalysis
