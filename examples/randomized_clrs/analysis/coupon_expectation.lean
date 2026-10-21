import Algo.coupon_model.Analysis

/-!
Expected completion time in the independent coupon-draw model. The mean is
the sum of the probabilities of still being incomplete after each draw. A
geometric union bound makes this sum finite before the recurrence is solved.
-/

noncomputable section
namespace CouponAnalysis
open Algo2LeanProbability
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Expected remaining draws, expressed by the natural-number tail-sum formula. -/
def meanRemaining (n : Nat) (seen : Finset (Fin (n + 1))) : ℝ≥0∞ :=
  ∑' time : Nat, pmfExpected (afterDraws n seen time)
    (fun final => if final ≠ Finset.univ then 1 else 0)

/-- The geometric union bound gives a finite mean from every initial set. -/
theorem meanRemaining_finite (n : Nat) (seen : Finset (Fin (n + 1))) :
    meanRemaining n seen ≠ ∞ := by
  have bound : meanRemaining n seen ≤
      (n + 1 : ℝ≥0∞) * ∑' time : Nat, ((n : ℝ≥0∞) / (n + 1)) ^ time := by
    unfold meanRemaining
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum (fun time => incomplete_probability_le_from n time seen)
  apply ne_top_of_le_ne_top _ bound
  apply ENNReal.mul_ne_top (by simp)
  apply ne_of_lt
  apply tsum_geometric_lt_top.mpr
  apply (ENNReal.div_lt_iff (by simp) (by simp)).2
  simpa only [one_mul, Nat.cast_add, Nat.cast_one] using
    (show (n : ℝ≥0∞) < ((n + 1 : Nat) : ℝ≥0∞) from by exact_mod_cast Nat.lt_succ_self n)

/-- The chance of still being incomplete tends to zero from every initial set. -/
theorem incomplete_probability_tendsto_zero (n : Nat) (seen : Finset (Fin (n + 1))) :
    Filter.Tendsto (fun time => pmfExpected (afterDraws n seen time)
      (fun final => if final ≠ Finset.univ then 1 else 0)) Filter.atTop (nhds 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top (meanRemaining_finite n seen)

/-- The finite-draw laws induce the usual one-draw equation for the mean. -/
theorem meanRemaining_equation (n : Nat) (seen : Finset (Fin (n + 1))) :
    meanRemaining n seen = (if seen ≠ Finset.univ then 1 else 0) +
      ∑ coupon : Fin (n + 1), meanRemaining n (insert coupon seen) * (n + 1 : ℝ≥0∞)⁻¹ := by
  unfold meanRemaining
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [afterDraws, pmfExpected_pure, pmfExpected_bind]
  congr 1
  simp only [pmfExpected, PMF.uniformOfFintype_apply, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one]
  rw [ENNReal.tsum_comm, tsum_fintype]
  apply Finset.sum_congr rfl
  intro coupon _
  rw [ENNReal.tsum_mul_left, mul_comm]

@[simp] theorem afterDraws_full (n time : Nat) :
    afterDraws n Finset.univ time = PMF.pure Finset.univ := by
  induction time with
  | zero => rfl
  | succ time ih => simp [afterDraws, ih]

@[simp] theorem meanRemaining_full (n : Nat) : meanRemaining n Finset.univ = 0 := by
  simp [meanRemaining]

/-- The sum of the geometric mean waiting times for the remaining stages. -/
def phaseMean (total missing : Nat) : ℝ≥0∞ :=
  ∑ index ∈ Finset.range missing, (total : ℝ≥0∞) / (index + 1)

theorem phaseMean_finite (total missing : Nat) : phaseMean total missing ≠ ∞ := by
  simp [phaseMean, ENNReal.sum_eq_top, ENNReal.div_eq_top]

@[simp] theorem phaseMean_zero (total : Nat) : phaseMean total 0 = 0 := by simp [phaseMean]

theorem phaseMean_succ (total missing : Nat) :
    phaseMean total (missing + 1) = phaseMean total missing + (total : ℝ≥0∞) / (missing + 1) :=
  Finset.sum_range_succ _ missing

/-- With k coupon types still missing among N, the model's exact mean remaining
number of draws is N times the kth harmonic sum. -/
theorem meanRemaining_eq_phaseMean (n : Nat) (seen : Finset (Fin (n + 1))) :
    meanRemaining n seen = phaseMean (n + 1) (n + 1 - seen.card) := by
  generalize remaining : n + 1 - seen.card = missing
  induction missing generalizing seen with
  | zero =>
      have full : seen = Finset.univ := by
        apply Finset.eq_univ_of_card
        have bounded := Finset.card_le_card (Finset.subset_univ seen)
        simp only [Finset.card_univ, Fintype.card_fin] at bounded ⊢
        omega
      simp [full]
  | succ missing ih =>
      have full : seen ≠ Finset.univ := by
        intro equal
        simp [equal] at remaining
      have card : seen.card + (missing + 1) = n + 1 := by
        have bounded := Finset.card_le_card (Finset.subset_univ seen)
        simp only [Finset.card_univ, Fintype.card_fin] at bounded
        omega
      have after (coupon : Fin (n + 1)) :
          meanRemaining n (insert coupon seen) =
            if coupon ∈ seen then meanRemaining n seen else phaseMean (n + 1) missing := by
        by_cases old : coupon ∈ seen
        · simp [old]
        · simp only [if_neg old]
          apply ih
          rw [Finset.card_insert_of_notMem old]
          omega
      have equation := meanRemaining_equation n seen
      simp only [if_pos full, after] at equation
      rw [← Finset.sum_mul] at equation
      have summed : (∑ coupon : Fin (n + 1), if coupon ∈ seen then meanRemaining n seen
          else phaseMean (n + 1) missing) =
          (seen.card : ℝ≥0∞) * meanRemaining n seen +
            (missing + 1 : ℝ≥0∞) * phaseMean (n + 1) missing := by
        rw [Finset.sum_ite]
        have complement : (Finset.univ.filter (fun coupon : Fin (n + 1) => coupon ∉ seen)).card =
            missing + 1 := by
          simp [← Finset.sdiff_eq_filter, Finset.card_sdiff, remaining]
        simp [complement]
      rw [summed] at equation
      apply (ENNReal.toReal_eq_toReal_iff' (meanRemaining_finite n seen)
        (phaseMean_finite (n + 1) (missing + 1))).mp
      have realEquation := congrArg ENNReal.toReal equation
      have finiteMean := meanRemaining_finite n seen
      have finitePhase := phaseMean_finite (n + 1) missing
      simp [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.add_eq_top, ENNReal.mul_eq_top, finiteMean, finitePhase] at realEquation
      rw [phaseMean_succ, ENNReal.toReal_add finitePhase (by simp [ENNReal.div_eq_top])]
      simp [ENNReal.toReal_div, ENNReal.toReal_add, Nat.cast_add]
      have realCard : (seen.card : ℝ) + (missing + 1) = n + 1 := by exact_mod_cast card
      have positive : (0 : ℝ) < missing + 1 := by positivity
      have positiveN : (0 : ℝ) < n + 1 := by positivity
      field_simp [ne_of_gt positive, ne_of_gt positiveN] at realEquation ⊢
      nlinarith [congrArg (fun total : ℝ => (meanRemaining n seen).toReal * total) realCard]

/-- Starting with no coupons, the model's exact expected draw count is N H_N,
where N = n + 1 and H_N is the sum of the first N reciprocal integers. -/
theorem mean_empty (n : Nat) :
    meanRemaining n ∅ =
      (n + 1 : ℝ≥0∞) * ∑ index ∈ Finset.range (n + 1), (index + 1 : ℝ≥0∞)⁻¹ := by
  rw [meanRemaining_eq_phaseMean]
  simp [phaseMean, Finset.mul_sum, div_eq_mul_inv]

end CouponAnalysis
