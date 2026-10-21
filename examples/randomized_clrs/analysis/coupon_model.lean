import Algo2LeanProbability.Call

/-!
The finite-draw model behind coupon collection. Each draw is independent and
uniform among `n + 1` coupon types. The absent-coupon formula and union bound
describe the probability that collection is still incomplete after a fixed
number of draws. The model is separate from the generated program bridge.
-/

noncomputable section
namespace CouponAnalysis
open Algo2LeanProbability
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- The set of observed coupons after a fixed number of independent draws. -/
def afterDraws (n : Nat) (seen : Finset (Fin (n + 1))) : Nat → PMF (Finset (Fin (n + 1)))
  | 0 => PMF.pure seen
  | time + 1 => (PMF.uniformOfFintype (Fin (n + 1))).bind
      (fun coupon => afterDraws n (insert coupon seen) time)

private theorem uniform_expected (n : Nat) (reward : Fin (n + 1) → ℝ≥0∞) :
    pmfExpected (PMF.uniformOfFintype (Fin (n + 1))) reward =
      ∑ coupon, reward coupon * (n + 1 : ℝ≥0∞)⁻¹ := by
  simp only [pmfExpected, tsum_fintype, PMF.uniformOfFintype_apply, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, mul_comm]

/-- A particular unseen coupon is missed on each draw with probability
`n / (n + 1)`. Already-seen coupons remain present. -/
theorem absent_probability (n time : Nat) (seen : Finset (Fin (n + 1)))
    (coupon : Fin (n + 1)) :
    pmfExpected (afterDraws n seen time) (fun final => if coupon ∉ final then 1 else 0) =
      if coupon ∉ seen then ((n : ℝ≥0∞) / (n + 1)) ^ time else 0 := by
  induction time generalizing seen with
  | zero => simp [afterDraws]
  | succ time ih =>
      rw [afterDraws, pmfExpected_bind, uniform_expected]
      simp_rw [ih]
      by_cases present : coupon ∈ seen
      · simp [present]
      · simp only [Finset.mem_insert, not_or, present, not_false_eq_true, and_true,
          if_true]
        rw [← Finset.sum_mul]
        have sum : (∑ drawn : Fin (n + 1),
            if coupon ≠ drawn then ((n : ℝ≥0∞) / (n + 1)) ^ time else 0) =
            (n : ℝ≥0∞) * ((n : ℝ≥0∞) / (n + 1)) ^ time := by
          have filter : Finset.univ.filter (fun drawn : Fin (n + 1) => coupon ≠ drawn) =
              Finset.univ.erase coupon := by ext drawn; simp [ne_comm]
          simp [Finset.sum_ite, filter]
        rw [sum, pow_succ]
        simp only [div_eq_mul_inv]
        ac_rfl

/-- The probability of incomplete collection after `time` draws is at most
`(n + 1) (n / (n + 1)) ^ time`. This is a union bound over missing coupons. -/
theorem incomplete_probability_le_from (n time : Nat) (seen : Finset (Fin (n + 1))) :
    pmfExpected (afterDraws n seen time)
      (fun final => if final ≠ Finset.univ then 1 else 0) ≤
      (n + 1 : ℝ≥0∞) * ((n : ℝ≥0∞) / (n + 1)) ^ time := by
  calc
    _ ≤ pmfExpected (afterDraws n seen time)
        (fun final => ∑ coupon : Fin (n + 1), if coupon ∉ final then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro final
      apply mul_le_mul' le_rfl
      by_cases full : final = Finset.univ
      · simp [full]
      · simp only [if_pos full]
        obtain ⟨coupon, absent⟩ : ∃ coupon : Fin (n + 1), coupon ∉ final := by
          by_contra missing
          apply full
          exact Finset.eq_univ_of_forall (by simpa using missing)
        have bound : (if coupon ∉ final then (1 : ℝ≥0∞) else 0) ≤
            ∑ other : Fin (n + 1), if other ∉ final then 1 else 0 :=
          Finset.single_le_sum (f := fun other : Fin (n + 1) =>
            if other ∉ final then (1 : ℝ≥0∞) else 0)
            (fun _ _ => bot_le) (Finset.mem_univ coupon)
        simpa only [if_pos absent] using bound
    _ = ∑ coupon : Fin (n + 1),
        pmfExpected (afterDraws n seen time) (fun final => if coupon ∉ final then 1 else 0) := by
      simp only [pmfExpected, tsum_fintype, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ coupon : Fin (n + 1), ((n : ℝ≥0∞) / (n + 1)) ^ time := by
      simp_rw [absent_probability]
      apply Finset.sum_le_sum
      intro coupon _
      split_ifs <;> simp
    _ = _ := by simp

/-- Starting empty gives the usual coupon-collector tail bound. -/
theorem incomplete_probability_le (n time : Nat) :
    pmfExpected (afterDraws n ∅ time)
      (fun final => if final ≠ Finset.univ then 1 else 0) ≤
      (n + 1 : ℝ≥0∞) * ((n : ℝ≥0∞) / (n + 1)) ^ time :=
  incomplete_probability_le_from n time ∅

/-- Every one of the next `time` coupons lies in a specified allowed set with
probability `(|allowed| / (n + 1)) ^ time`, provided the initial set does too. -/
theorem confined_probability (n time : Nat) (seen allowed : Finset (Fin (n + 1))) :
    pmfExpected (afterDraws n seen time) (fun final => if final ⊆ allowed then 1 else 0) =
      if seen ⊆ allowed then ((allowed.card : ℝ≥0∞) / (n + 1)) ^ time else 0 := by
  induction time generalizing seen with
  | zero => simp [afterDraws]
  | succ time ih =>
      rw [afterDraws, pmfExpected_bind, uniform_expected]
      simp_rw [ih]
      by_cases included : seen ⊆ allowed
      · simp only [Finset.insert_subset_iff, included, and_true, if_true]
        rw [← Finset.sum_mul]
        have sum : (∑ drawn : Fin (n + 1), if drawn ∈ allowed then
              ((allowed.card : ℝ≥0∞) / (n + 1)) ^ time else 0) =
            (allowed.card : ℝ≥0∞) * ((allowed.card : ℝ≥0∞) / (n + 1)) ^ time := by
          simp
        rw [sum, pow_succ]
        simp only [div_eq_mul_inv]
        ac_rfl
      · simp [Finset.insert_subset_iff, included]

/-- Tail probability for the waiting time until the next previously unseen
coupon. It includes the successful draw: at time zero this probability is one. -/
def newCouponTail (n : Nat) (seen : Finset (Fin (n + 1))) (time : Nat) : ℝ≥0∞ :=
  pmfExpected (afterDraws n seen time) (fun final => if final ⊆ seen then 1 else 0)

theorem newCouponTail_eq (n time : Nat) (seen : Finset (Fin (n + 1))) :
    newCouponTail n seen time = ((seen.card : ℝ≥0∞) / (n + 1)) ^ time := by
  simp [newCouponTail, confined_probability]

/-- Summing the waiting-time tail gives the mean number of draws to discover
one new coupon. If every type has already been seen, both sides are infinite. -/
theorem newCoupon_mean (n : Nat) (seen : Finset (Fin (n + 1))) :
    (∑' time : Nat, newCouponTail n seen time) =
      (n + 1 : ℝ≥0∞) / ((n + 1 : ℝ≥0∞) - seen.card) := by
  simp_rw [newCouponTail_eq]
  rw [ENNReal.tsum_geometric]
  have denominator : (n + 1 : ℝ≥0∞) ≠ 0 := by simp
  have finite : (n + 1 : ℝ≥0∞) ≠ ∞ := by simp
  have difference : 1 - (seen.card : ℝ≥0∞) / (n + 1) =
      ((n + 1 : ℝ≥0∞) - seen.card) / (n + 1) := by
    rw [ENNReal.sub_div (fun _ _ => denominator), ENNReal.div_self denominator finite]
  rw [difference, ENNReal.inv_div (Or.inl finite) (Or.inl denominator)]

end CouponAnalysis
