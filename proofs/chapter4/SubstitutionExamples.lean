import Substitution

/-!
A genuinely arbitrary-size example of substitution. This is a numerical cost
recurrence, not a claim that an unverified source program realizes it.

The two child sizes are floor(n/2) and n-floor(n/2), so odd sizes have unequal
children. A first quadratic candidate illustrates general substitution.
Monotonicity and exact values at powers of two then give tight logarithmic
bounds for every natural size and an eventual Theta(n log₂ n) certificate.
-/
namespace Chapter4SubstitutionExamples
open Chapter4Substitution

/-- Balanced floor/ceiling splitting, including the unequal split for odd n. -/
def balancedChildren (n : Nat) : List Nat := [n / 2, n - n / 2]

/-- Both children are positive and strictly smaller above the base range. -/
theorem balanced_split_bounds (n : Nat) (large : 2 ≤ n) :
    0 < n / 2 ∧ n / 2 < n ∧ 0 < n - n / 2 ∧ n - n / 2 < n := by
  omega

theorem balanced_children_smaller : SmallerChildren balancedChildren 2 := by
  intro n large child member
  have bounds := balanced_split_bounds n large
  simp only [balancedChildren, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> omega

/-- The square candidate closes the substitution inequality for every split,
    rather than just powers of two. -/
theorem quadratic_substitution (n : Nat) (large : 2 ≤ n) :
    n + (n/2)*(n/2) + (n-n/2)*(n-n/2) ≤ n*n := by
  obtain ⟨leftPositive, leftSmaller, rightPositive, rightSmaller⟩ := balanced_split_bounds n large
  let left := n/2
  let right := n-n/2
  have split : left + right = n := by dsimp [left, right]; omega
  have leftBound : left ≤ left*right := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left left (show 1 ≤ right by exact rightPositive)
  have rightBound : right ≤ left*right := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right right (show 1 ≤ left by exact leftPositive)
  have product : n*n = left*left + left*right + left*right + right*right := by
    rw [← split]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm right left]
    omega
  change n + left*left + right*right ≤ n*n
  omega

/-- Any cost satisfying this floor/ceiling recurrence is at most n², for all
    natural n. The proof directly instantiates the general substitution theorem. -/
theorem balanced_quadratic_upper (cost : Nat → Nat)
    (zero : cost 0 = 0) (one : cost 1 = 1)
    (recurrence : ∀ n, 2 ≤ n → cost n = cost (n/2) + cost (n-n/2) + n) :
    ∀ n, cost n ≤ n*n := by
  apply exact_upper_comparison balancedChildren (fun n => n) 2 cost (fun n => n*n)
    balanced_children_smaller
  · intro n small
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl <;> simp [zero, one]
  · intro n large
    simpa [balancedChildren, childSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using recurrence n large
  · intro n large
    simpa [balancedChildren, childSum, Nat.add_assoc]
      using quadratic_substitution n large

/-- The same recurrence is at least n; this provides a simple lower candidate
    and also checks that the framework supports both directions on unequal splits. -/
theorem balanced_linear_lower (cost : Nat → Nat)
    (zero : cost 0 = 0) (one : cost 1 = 1)
    (recurrence : ∀ n, 2 ≤ n → cost n = cost (n/2) + cost (n-n/2) + n) :
    ∀ n, n ≤ cost n := by
  apply exact_lower_comparison balancedChildren (fun n => n) 2 cost (fun n => n)
    balanced_children_smaller
  · intro n small
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl <;> simp [zero, one]
  · intro n large
    simpa [balancedChildren, childSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using recurrence n large
  · intro n large
    simp [balancedChildren, childSum]

/-- The pointwise substitution proof supplies a genuine asymptotic certificate. -/
theorem balanced_isBigO_quadratic (cost : Nat → Nat)
    (zero : cost 0 = 0) (one : cost 1 = 1)
    (recurrence : ∀ n, 2 ≤ n → cost n = cost (n/2) + cost (n-n/2) + n) :
    IsBigO cost (fun n => n*n) :=
  IsBigO.of_pointwise_le (balanced_quadratic_upper cost zero one recurrence)

/-- Uniqueness includes every natural input size and both base cases. -/
theorem balanced_unique (first second : Nat → Nat)
    (firstZero : first 0 = 0) (firstOne : first 1 = 1)
    (secondZero : second 0 = 0) (secondOne : second 1 = 1)
    (firstRecurrence : ∀ n, 2 ≤ n → first n = first (n/2) + first (n-n/2) + n)
    (secondRecurrence : ∀ n, 2 ≤ n → second n = second (n/2) + second (n-n/2) + n) :
    first = second := by
  apply exact_unique balancedChildren (fun n => n) 2 first second balanced_children_smaller
  · intro n small
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl <;> simp [firstZero, firstOne, secondZero, secondOne]
  · intro n large
    simpa [balancedChildren, childSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using firstRecurrence n large
  · intro n large
    simpa [balancedChildren, childSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using secondRecurrence n large



/-- A concrete total recurrence, defined by well-founded recursion on size.
    Its finite base range includes zero and one. -/
def balancedCost (n : Nat) : Nat :=
  if _small : n < 2 then n
  else balancedCost (n/2) + balancedCost (n-n/2) + n
termination_by n
decreasing_by
  all_goals
    have bounds := balanced_split_bounds n (by omega)
    omega

@[simp] theorem balancedCost_zero : balancedCost 0 = 0 := by
  rw [balancedCost]
  rfl

@[simp] theorem balancedCost_one : balancedCost 1 = 1 := by
  rw [balancedCost]
  rfl

theorem balancedCost_recurrence (n : Nat) (large : 2 ≤ n) :
    balancedCost n = balancedCost (n/2) + balancedCost (n-n/2) + n := by
  rw [balancedCost, dif_neg (by omega)]

/-- A concrete certificate covering all natural sizes, including odd sizes. -/
theorem balancedCost_bounds (n : Nat) : n ≤ balancedCost n ∧ balancedCost n ≤ n*n :=
  ⟨balanced_linear_lower balancedCost balancedCost_zero balancedCost_one balancedCost_recurrence n,
    balanced_quadratic_upper balancedCost balancedCost_zero balancedCost_one balancedCost_recurrence n⟩

theorem balancedCost_isBigO_quadratic : IsBigO balancedCost (fun n => n*n) :=
  balanced_isBigO_quadratic balancedCost balancedCost_zero balancedCost_one balancedCost_recurrence

-- Kernel-checked boundary and unequal-split instances complement the general theorem.
example : balancedCost 0 = 0 := balancedCost_zero
example : balancedCost 1 = 1 := balancedCost_one
example : balancedCost 3 = 8 := by simp [balancedCost]
example : balancedCost 10 = 44 := by simp [balancedCost]



/-- Increasing the problem size cannot decrease this recurrence's cost. -/
theorem balancedCost_monotone {a b : Nat} (ordered : a ≤ b) :
    balancedCost a ≤ balancedCost b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases small : a < 2
    · have cases : a = 0 ∨ a = 1 := by omega
      rcases cases with rfl | rfl
      · simp
      · have lower := (balancedCost_bounds b).1
        simp only [balancedCost_one]
        omega
    · have aLarge : 2 ≤ a := by omega
      have bLarge : 2 ≤ b := by omega
      have splits := balanced_split_bounds b bLarge
      have left := ih (b/2) splits.2.1 (show a/2 ≤ b/2 by omega)
      have right := ih (b-b/2) splits.2.2.2 (show a-a/2 ≤ b-b/2 by omega)
      rw [balancedCost_recurrence a aLarge, balancedCost_recurrence b bLarge]
      exact Nat.add_le_add (Nat.add_le_add left right) ordered

/-- At powers of two every recursion level has the same total size. -/
theorem balancedCost_power_two (k : Nat) :
    balancedCost (2^k) = (k+1)*2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have positive : 0 < (2^k : Nat) := Nat.pow_pos (by decide)
    have large : 2 ≤ (2^k : Nat)*2 := by omega
    have half : (2^k*2:Nat)/2 = 2^k := by omega
    rw [Nat.pow_succ, balancedCost_recurrence _ large, half, ih]
    rw [show (2^k*2:Nat)-2^k = 2^k by omega, ih]
    simp only [Nat.succ_mul, Nat.mul_two, Nat.mul_add]
    omega

/-- Bracketing an arbitrary size between adjacent powers of two gives a
    logarithmic upper bound without assuming an exact power-of-two input. -/
theorem balancedCost_logarithmic_upper (n : Nat) :
    balancedCost n ≤ 4*n*(Nat.log2 n+1) := by
  by_cases zero : n = 0
  · subst n; simp
  · obtain ⟨below, above⟩ := (Nat.log2_eq_iff zero).mp rfl
    have runBound := balancedCost_monotone (Nat.le_of_lt above)
    rw [balancedCost_power_two] at runBound
    have exponentBound : Nat.log2 n + 1 + 1 ≤ 2*(Nat.log2 n+1) := by omega
    have nextPower : 2^(Nat.log2 n+1) ≤ 2*n := by
      rw [Nat.pow_succ]
      simpa only [Nat.mul_comm 2 n] using Nat.mul_le_mul_right 2 below
    have productBound := Nat.mul_le_mul exponentBound nextPower
    have rearrange : (2*(Nat.log2 n+1))*(2*n) = 4*n*(Nat.log2 n+1) := by
      change (2*(Nat.log2 n+1))*(2*n) = (2*2)*n*(Nat.log2 n+1)
      ac_rfl
    rw [rearrange] at productBound
    exact Nat.le_trans runBound productBound

/-- The lower adjacent power gives a matching lower bound within factor two. -/
theorem balancedCost_logarithmic_lower (n : Nat) :
    n*(Nat.log2 n+1) ≤ 2*balancedCost n := by
  by_cases zero : n = 0
  · subst n; simp
  · obtain ⟨below, above⟩ := (Nat.log2_eq_iff zero).mp rfl
    have runBound := balancedCost_monotone below
    rw [balancedCost_power_two] at runBound
    have upperSize : n ≤ 2*(2^Nat.log2 n) := by
      rw [Nat.pow_succ] at above
      omega
    have sizeBound := Nat.mul_le_mul_right (Nat.log2 n+1) upperSize
    have costBound := Nat.mul_le_mul_left 2 runBound
    have rearrange : (2*(2^Nat.log2 n))*(Nat.log2 n+1) =
        2*((Nat.log2 n+1)*2^Nat.log2 n) := by ac_rfl
    rw [rearrange] at sizeBound
    exact Nat.le_trans sizeBound costBound

/-- The rounded recurrence has the tight natural-valued Theta(n(log₂ n+1))
    bound; adding one covers the positive base case, and n=0 is also included. -/
theorem balancedCost_isTheta_logarithmic :
    IsTheta balancedCost (fun n => n*(Nat.log2 n+1)) := by
  apply IsTheta.of_pointwise_bounds 4 2 (by decide) (by decide)
  · intro n
    simpa only [Nat.mul_assoc] using balancedCost_logarithmic_upper n
  · exact balancedCost_logarithmic_lower



/-- The canonical Theta(n log₂ n) statement starts at n=2. This threshold
    matters because log₂ 1=0 while the base cost at one is positive. -/
theorem balancedCost_isTheta_nlogn :
    IsTheta balancedCost (fun n => n*Nat.log2 n) := by
  apply IsTheta.of_eventual_bounds 8 2 2 (by decide) (by decide)
  · intro n large
    have logPositive : 1 ≤ Nat.log2 n :=
      (Nat.le_log2 (show n ≠ 0 by omega)).mpr (by simpa using large)
    have logarithmBound : Nat.log2 n+1 ≤ 2*Nat.log2 n := by omega
    have scaled := Nat.mul_le_mul_left (4*n) logarithmBound
    have rearrange : (4*n)*(2*Nat.log2 n) = 8*(n*Nat.log2 n) := by
      change (4*n)*(2*Nat.log2 n) = (4*2)*(n*Nat.log2 n)
      ac_rfl
    rw [rearrange] at scaled
    exact Nat.le_trans (balancedCost_logarithmic_upper n) scaled
  · intro n _
    have smallerLog := Nat.mul_le_mul_left n (show Nat.log2 n ≤ Nat.log2 n+1 by omega)
    exact Nat.le_trans smallerLog (balancedCost_logarithmic_lower n)

/-- The tight asymptotic conclusion applies to any solution of the rounded
    recurrence, by the general exact-solution uniqueness theorem. -/
theorem balanced_isTheta_nlogn (cost : Nat → Nat)
    (zero : cost 0 = 0) (one : cost 1 = 1)
    (recurrence : ∀ n, 2 ≤ n → cost n = cost (n/2) + cost (n-n/2) + n) :
    IsTheta cost (fun n => n*Nat.log2 n) := by
  have equal := balanced_unique cost balancedCost zero one
    balancedCost_zero balancedCost_one recurrence balancedCost_recurrence
  rw [equal]
  exact balancedCost_isTheta_nlogn

end Chapter4SubstitutionExamples
