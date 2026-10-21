import Algo.shuffle_permutation.Analysis
import Algo2LeanProbability.Call
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Fin

/-!
The expected number of strict records in a uniformly permuted list of distinct
scores is a harmonic number. These finite combinatorial lemmas are independent
of execution semantics; the hiring analysis connects them to the source program.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace HiringRecords
open Algo2LeanProbability
open scoped ENNReal

/-- Number of strict left-to-right records, counting the first position. -/
def records {n : Nat} (scores : Fin n → Int) : ℝ≥0∞ :=
  ∑ i : Fin n, if ∀ j : Fin n, j < i → scores j < scores i then 1 else 0

/-- The nth harmonic number; the empty sum is zero. -/
def harmonic (n : Nat) : ℝ≥0∞ := ∑ i : Fin n, ((i.val + 1 : Nat) : ℝ≥0∞)⁻¹

/-- A selected position holds the largest score among the positions in a set. -/
def maximumAt {n : Nat} (scores : Fin n → Int) (positions : Finset (Fin n))
    (permutation : Equiv.Perm (Fin n)) (selected : Fin n) : Prop :=
  ∀ position ∈ positions, scores (permutation position) ≤ scores (permutation selected)

private theorem swap_mem {n : Nat} (positions : Finset (Fin n))
    (first second : Fin n) (hf : first ∈ positions) (hs : second ∈ positions)
    (position : Fin n) : Equiv.swap first second position ∈ positions ↔ position ∈ positions := by
  classical
  by_cases h₁ : position = first
  · subst position; simp [hf, hs]
  by_cases h₂ : position = second
  · subst position; simp [hf, hs]
  simp [Equiv.swap_apply_of_ne_of_ne h₁ h₂]

/-- Exchanging two positions in the same set exchanges the maximum events. -/
theorem maximumAt_swap {n : Nat} (scores : Fin n → Int) (positions : Finset (Fin n))
    (permutation : Equiv.Perm (Fin n)) (first second : Fin n)
    (hf : first ∈ positions) (hs : second ∈ positions) :
    maximumAt scores positions ((Equiv.swap first second).trans permutation) first ↔
      maximumAt scores positions permutation second := by
  classical
  constructor
  · intro h position hp
    have result := h (Equiv.swap first second position) ((swap_mem positions first second hf hs position).2 hp)
    simpa [Equiv.trans_apply] using result
  · intro h position hp
    have result := h (Equiv.swap first second position) ((swap_mem positions first second hf hs position).2 hp)
    simpa [Equiv.trans_apply] using result

/-- Permuting the positions of a uniform permutation preserves its law. -/
theorem uniform_precompose {n : Nat} (change : Equiv.Perm (Fin n))
    (reward : Equiv.Perm (Fin n) → ℝ≥0∞) :
    pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
      (fun permutation => reward (change.trans permutation)) =
      pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n))) reward := by
  let equivalence : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
    { toFun := fun permutation => change.trans permutation
      invFun := fun permutation => change.symm.trans permutation
      left_inv := by intro permutation; ext position; simp
      right_inv := by intro permutation; ext position; simp }
  have mapped := congrArg (fun law => pmfExpected law reward) (ShuffleAnalysis.uniform_equiv equivalence)
  simpa [pmfExpected_map, equivalence] using mapped

/-- Every position in a fixed nonempty set has the same probability of its maximum. -/
theorem maximumAt_probability_equal {n : Nat} (scores : Fin n → Int)
    (positions : Finset (Fin n)) (first second : Fin n)
    (hf : first ∈ positions) (hs : second ∈ positions) :
    pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
      (fun permutation => if maximumAt scores positions permutation first then 1 else 0) =
    pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
      (fun permutation => if maximumAt scores positions permutation second then 1 else 0) := by
  classical
  rw [← uniform_precompose (Equiv.swap first second)]
  apply congrArg (pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n))))
  funext permutation
  simp only [maximumAt_swap scores positions permutation first second hf hs]

/-- Distinct scores have exactly one maximum in every nonempty finite set. -/
theorem maximumAt_sum {n : Nat} (scores : Fin n → Int)
    (distinct : Function.Injective scores) (positions : Finset (Fin n))
    (nonempty : positions.Nonempty) (permutation : Equiv.Perm (Fin n)) :
    (∑ position ∈ positions,
      if maximumAt scores positions permutation position then (1 : ℝ≥0∞) else 0) = 1 := by
  classical
  obtain ⟨best, hb, greatest⟩ := positions.exists_max_image (scores ∘ permutation) nonempty
  have unique (position : Fin n) (hp : position ∈ positions) :
      maximumAt scores positions permutation position ↔ position = best := by
    constructor
    · intro h
      apply permutation.injective
      apply distinct
      exact le_antisymm (greatest position hp) (h best hb)
    · intro h; subst position; exact greatest
  calc
    _ = ∑ position ∈ positions, if position = best then (1 : ℝ≥0∞) else 0 := by
      apply Finset.sum_congr rfl
      intro position hp
      simp [unique position hp]
    _ = 1 := by simp [hb]

/-- Expectation distributes over a finite sum of nonnegative rewards. -/
theorem expected_sum {A I : Type*} (law : PMF A) (indices : Finset I)
    (reward : I → A → ℝ≥0∞) :
    pmfExpected law (fun value => ∑ index ∈ indices, reward index value) =
      ∑ index ∈ indices, pmfExpected law (reward index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [pmfExpected]
  | @insert index rest absent ih =>
      simp only [Finset.sum_insert absent]
      simp only [pmfExpected, mul_add, ENNReal.tsum_add] at ih ⊢
      rw [ih]

/-- A constant nonnegative reward has that expectation under any probability law. -/
theorem expected_const {A : Type*} (law : PMF A) (value : ℝ≥0∞) :
    pmfExpected law (fun _ => value) = value := by
  simp [pmfExpected, ENNReal.tsum_mul_right, PMF.tsum_coe]

/-- Each position in a finite set is its maximum with probability one over its size. -/
theorem maximumAt_probability {n : Nat} (scores : Fin n → Int)
    (distinct : Function.Injective scores) (positions : Finset (Fin n))
    (selected : Fin n) (member : selected ∈ positions) :
    pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
      (fun permutation => if maximumAt scores positions permutation selected then 1 else 0) =
      (positions.card : ℝ≥0∞)⁻¹ := by
  classical
  let law := PMF.uniformOfFintype (Equiv.Perm (Fin n))
  let event := fun position permutation =>
    if maximumAt scores positions permutation position then (1 : ℝ≥0∞) else 0
  have total : (∑ position ∈ positions, pmfExpected law (event position)) = 1 := by
    rw [← expected_sum]
    trans pmfExpected law (fun _ => 1)
    · apply congrArg (pmfExpected law)
      funext permutation
      exact maximumAt_sum scores distinct positions ⟨selected, member⟩ permutation
    · exact expected_const law 1
  have same : (∑ position ∈ positions, pmfExpected law (event position)) =
      (positions.card : ℝ≥0∞) * pmfExpected law (event selected) := by
    calc
      _ = ∑ _position ∈ positions, pmfExpected law (event selected) := by
        apply Finset.sum_congr rfl
        intro position hp
        exact maximumAt_probability_equal scores positions position selected hp member
      _ = _ := by simp [nsmul_eq_mul]
  have one := same.symm.trans total
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using one)

/-- With distinct scores, a prefix maximum is exactly a strict new record. -/
theorem maximumAt_prefix {n : Nat} (scores : Fin n → Int)
    (distinct : Function.Injective scores) (permutation : Equiv.Perm (Fin n)) (index : Fin n) :
    maximumAt scores (Finset.Iic index) permutation index ↔
      ∀ earlier : Fin n, earlier < index → scores (permutation earlier) < scores (permutation index) := by
  constructor
  · intro maximum earlier before
    apply lt_of_le_of_ne (maximum earlier (Finset.mem_Iic.mpr (le_of_lt before)))
    intro same
    exact (ne_of_lt before) (permutation.injective (distinct same))
  · intro record position member
    have bound := Finset.mem_Iic.mp member
    rcases lt_or_eq_of_le bound with before | same
    · exact le_of_lt (record position before)
    · subst position; exact le_rfl

/-- The ith position is a strict record with probability 1/(i+1). -/
theorem record_probability {n : Nat} (scores : Fin n → Int)
    (distinct : Function.Injective scores) (index : Fin n) :
    pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
      (fun permutation => if ∀ earlier : Fin n, earlier < index →
        scores (permutation earlier) < scores (permutation index) then 1 else 0) =
      ((index.val + 1 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  have result := maximumAt_probability scores distinct (Finset.Iic index) index (Finset.mem_Iic.mpr le_rfl)
  simpa only [maximumAt_prefix scores distinct, Fin.card_Iic] using result

/-- Uniformly permuting distinct scores produces H_n expected strict records. -/
theorem expected_records {n : Nat} (scores : Fin n → Int)
    (distinct : Function.Injective scores) :
    pmfExpected (PMF.uniformOfFintype (Equiv.Perm (Fin n)))
      (fun permutation => records (scores ∘ permutation)) = harmonic n := by
  classical
  unfold records harmonic
  rw [expected_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact record_probability scores distinct index

end HiringRecords
