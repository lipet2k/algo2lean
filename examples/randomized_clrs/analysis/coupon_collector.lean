import Algo.coupon_contract.Analysis

/-!
The coupon collector repeatedly samples uniformly from [0, N), retaining the
seen types in a mutable set. Its expected total charged draws are N H_N, and
its draw-cost tail is bounded by N((N−1)/N)^t. Both statements concern complete
execution paths; almost-sure termination is proved from the generated program.
-/

noncomputable section
namespace CouponAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open Algo.coupon_collector Algo.coupon_collector.Algo2LeanGenerated
open scoped ENNReal

/-- A valid mutable set containing precisely the integers from zero to N−1. -/
def Complete (heap : Heap) (ref : CollectionRef) (types : Nat) : Prop :=
  «set[Int]».valid heap ref ∧ («set[Int]».keys heap ref).toFinset = Finset.Ico 0 (types : Int)

private theorem full_coupon_image (n : Nat) :
    (Finset.univ : Finset (Fin (n + 1))).image (fun coupon => (coupon.val : Int)) =
      Finset.Ico 0 ((n + 1 : Nat) : Int) := by
  ext value
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ico]
  constructor
  · rintro ⟨coupon, rfl⟩
    constructor
    · omega
    · exact_mod_cast coupon.isLt
  · intro bounds
    refine ⟨⟨value.toNat, by omega⟩, ?_⟩
    change (value.toNat : Int) = value
    exact Int.toNat_of_nonneg bounds.1

-- Main result: Correctness
/-- With probability one, collection returns its newly allocated mutable set
containing every coupon type and no other integer. -/
theorem correctness (heap : Heap) (types : Nat) (positive : 0 < types) :
    collect_coupons.returnProbability heap types (fun final result =>
      result.1 = heap.nextCollection ∧ Complete final result.1 types) = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simpa only [Complete, Represents, full_coupon_image, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_one] using correctness_succ heap n

-- Main result: Running time
/-- The unconditional expected number of charged draws is exactly N H_N. -/
theorem running_time (heap : Heap) (types : Nat) (positive : 0 < types) :
    collect_coupons.expectedCost heap types "random_draws" =
      (types : ℝ≥0∞) * ∑ index ∈ Finset.range types, (index + 1 : ℝ≥0∞)⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using running_time_succ heap n

/-- After t charged draws among N positive coupon types, further work has
probability at most N((N−1)/N)^t. -/
theorem running_time_tail (heap : Heap) (types budget : Nat) (positive : 0 < types) :
    collect_coupons.costProbability heap types "random_draws" budget ≤
      (types : ℝ≥0∞) * ((types - 1 : Nat) / (types : ℝ≥0∞)) ^ budget := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
    running_time_tail_succ heap n budget

end CouponAnalysis
