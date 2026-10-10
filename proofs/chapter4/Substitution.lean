import Std

/-!
CLRS §4.3: substitution as comparison with a proposed upper or lower bound.

Subproblem sizes are natural numbers; costs and tolls are natural-valued.
Every non-base problem has a finite list of strictly smaller children. The
number of children and their sizes may vary with the parent, and children need
not have equal sizes. Thus floor/ceiling splits, unequal splits, missing
branches, and repeated subproblems fit the same interface.

These theorems establish facts about numerical recurrences. Applying them to a
program additionally requires a proof connecting that program's charged cost
to the corresponding recurrence, as in the source-linked algorithm analyses.
-/
namespace Chapter4Substitution

/-- Sum the costs of a finite list of subproblems, preserving multiplicity. -/
def childSum (sizes : List Nat) (cost : Nat → Nat) : Nat :=
  (sizes.map cost).sum

@[simp] theorem childSum_nil (cost : Nat → Nat) : childSum [] cost = 0 := rfl

@[simp] theorem childSum_cons (size : Nat) (sizes : List Nat) (cost : Nat → Nat) :
    childSum (size :: sizes) cost = cost size + childSum sizes cost := by
  simp [childSum]

/-- Only comparisons at sizes actually occurring in the list are needed. -/
theorem childSum_mono (sizes : List Nat) (lower upper : Nat → Nat)
    (bound : ∀ size ∈ sizes, lower size ≤ upper size) :
    childSum sizes lower ≤ childSum sizes upper := by
  induction sizes with
  | nil => exact Nat.le_refl 0
  | cons size sizes ih =>
    simp only [childSum_cons]
    exact Nat.add_le_add (bound size (by simp))
      (ih (fun child member => bound child (by simp [member])))

theorem childSum_congr (sizes : List Nat) (first second : Nat → Nat)
    (same : ∀ size ∈ sizes, first size = second size) :
    childSum sizes first = childSum sizes second := by
  apply Nat.le_antisymm
  · exact childSum_mono sizes first second (fun size member => Nat.le_of_eq (same size member))
  · exact childSum_mono sizes second first (fun size member => Nat.le_of_eq (same size member).symm)

/-- Every child of a non-base problem has a strictly smaller size. -/
def SmallerChildren (children : Nat → List Nat) (cutoff : Nat) : Prop :=
  ∀ n, cutoff ≤ n → ∀ child ∈ children n, child < n

/-- An upper recurrence inequality for the cost being analyzed. -/
def UpperRecurrence (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → cost n ≤ toll n + childSum (children n) cost

/-- A lower recurrence inequality for the cost being analyzed. -/
def LowerRecurrence (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → toll n + childSum (children n) cost ≤ cost n

/-- An exact recurrence above the base-case cutoff. -/
def ExactRecurrence (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → cost n = toll n + childSum (children n) cost

/-- Substituting a candidate upper bound makes the recurrence no larger
    than that candidate. This is often called a supersolution. -/
def UpperCandidate (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (candidate : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → toll n + childSum (children n) candidate ≤ candidate n

/-- Substituting a candidate lower bound makes the recurrence no smaller
    than that candidate. This is often called a subsolution. -/
def LowerCandidate (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (candidate : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → candidate n ≤ toll n + childSum (children n) candidate

/-- General upper-bound substitution: check every base case, substitute the
    induction hypothesis at each child, and verify the proposed bound closes. -/
theorem upper_comparison (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost candidate : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → cost n ≤ candidate n)
    (recurrence : UpperRecurrence children toll cutoff cost)
    (substitution : UpperCandidate children toll cutoff candidate) :
    ∀ n, cost n ≤ candidate n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n < cutoff
    · exact base n small
    · have large : cutoff ≤ n := by omega
      have childrenBound : childSum (children n) cost ≤ childSum (children n) candidate :=
        childSum_mono (children n) cost candidate
          (fun child member => ih child (smaller n large child member))
      exact Nat.le_trans (recurrence n large)
        (Nat.le_trans (Nat.add_le_add_left childrenBound (toll n)) (substitution n large))

/-- General lower-bound substitution uses the same well-founded induction,
    with the recurrence and candidate inequalities in the opposite directions. -/
theorem lower_comparison (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost candidate : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → candidate n ≤ cost n)
    (recurrence : LowerRecurrence children toll cutoff cost)
    (substitution : LowerCandidate children toll cutoff candidate) :
    ∀ n, candidate n ≤ cost n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n < cutoff
    · exact base n small
    · have large : cutoff ≤ n := by omega
      have childrenBound : childSum (children n) candidate ≤ childSum (children n) cost :=
        childSum_mono (children n) candidate cost
          (fun child member => ih child (smaller n large child member))
      exact Nat.le_trans (substitution n large)
        (Nat.le_trans (Nat.add_le_add_left childrenBound (toll n)) (recurrence n large))

/-- An exact recurrence supplies the upper inequality required for substitution. -/
theorem exact_upper_comparison (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost candidate : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → cost n ≤ candidate n)
    (recurrence : ExactRecurrence children toll cutoff cost)
    (substitution : UpperCandidate children toll cutoff candidate) :
    ∀ n, cost n ≤ candidate n :=
  upper_comparison children toll cutoff cost candidate smaller base
    (fun n large => Nat.le_of_eq (recurrence n large)) substitution

/-- An exact recurrence also supplies the lower inequality. -/
theorem exact_lower_comparison (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost candidate : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → candidate n ≤ cost n)
    (recurrence : ExactRecurrence children toll cutoff cost)
    (substitution : LowerCandidate children toll cutoff candidate) :
    ∀ n, candidate n ≤ cost n :=
  lower_comparison children toll cutoff cost candidate smaller base
    (fun n large => Nat.le_of_eq (recurrence n large).symm) substitution

/-- Two exact solutions agreeing throughout the base range agree everywhere. -/
theorem exact_unique (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (first second : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → first n = second n)
    (firstRecurrence : ExactRecurrence children toll cutoff first)
    (secondRecurrence : ExactRecurrence children toll cutoff second) :
    first = second := by
  funext n
  apply Nat.le_antisymm
  · exact exact_upper_comparison children toll cutoff first second smaller
      (fun n small => Nat.le_of_eq (base n small)) firstRecurrence
      (fun n large => Nat.le_of_eq (secondRecurrence n large).symm) n
  · exact exact_lower_comparison children toll cutoff first second smaller
      (fun n small => Nat.le_of_eq (base n small).symm) firstRecurrence
      (fun n large => Nat.le_of_eq (secondRecurrence n large)) n

/-- Simultaneously establish lower and upper bounds for an exact recurrence. -/
theorem exact_sandwich (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost lower upper : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (baseLower : ∀ n, n < cutoff → lower n ≤ cost n)
    (baseUpper : ∀ n, n < cutoff → cost n ≤ upper n)
    (recurrence : ExactRecurrence children toll cutoff cost)
    (subLower : LowerCandidate children toll cutoff lower)
    (subUpper : UpperCandidate children toll cutoff upper) :
    ∀ n, lower n ≤ cost n ∧ cost n ≤ upper n := by
  intro n
  exact ⟨exact_lower_comparison children toll cutoff cost lower smaller baseLower recurrence subLower n,
    exact_upper_comparison children toll cutoff cost upper smaller baseUpper recurrence subUpper n⟩



/-- Equal-sized children contribute their multiplicity times one child cost. -/
@[simp] theorem childSum_replicate (count size : Nat) (cost : Nat → Nat) :
    childSum (List.replicate count size) cost = count * cost size := by
  simp [childSum]

/-- A depth-k problem with a children of depth k-1 is an instance of the
    general finite-child framework; the base depth is zero. -/
theorem depth_children_smaller (branching : Nat) :
    SmallerChildren (fun n => List.replicate branching (n-1)) 1 := by
  intro n large child member
  have equal := (List.mem_replicate.mp member).2
  omega

/-- Convenient depth form of upper substitution, derived from the general
    theorem rather than requiring a separate recurrence-solving principle. -/
theorem depth_upper (cost candidate : Nat → Nat) (branching : Nat) (toll : Nat → Nat)
    (base : cost 0 ≤ candidate 0)
    (stepCost : ∀ k, cost (k+1) ≤ branching * cost k + toll k)
    (stepCandidate : ∀ k, branching * candidate k + toll k ≤ candidate (k+1)) :
    ∀ k, cost k ≤ candidate k := by
  apply upper_comparison (fun n => List.replicate branching (n-1))
    (fun n => toll (n-1)) 1 cost candidate (depth_children_smaller branching)
  · intro n small
    have equal : n = 0 := by omega
    simpa [equal] using base
  · intro n large
    cases n with
    | zero => omega
    | succ k => simpa [Nat.add_comm] using stepCost k
  · intro n large
    cases n with
    | zero => omega
    | succ k => simpa [Nat.add_comm] using stepCandidate k

/-- The corresponding balanced-depth lower substitution theorem. -/
theorem depth_lower (cost candidate : Nat → Nat) (branching : Nat) (toll : Nat → Nat)
    (base : candidate 0 ≤ cost 0)
    (stepCost : ∀ k, branching * cost k + toll k ≤ cost (k+1))
    (stepCandidate : ∀ k, candidate (k+1) ≤ branching * candidate k + toll k) :
    ∀ k, candidate k ≤ cost k := by
  apply lower_comparison (fun n => List.replicate branching (n-1))
    (fun n => toll (n-1)) 1 cost candidate (depth_children_smaller branching)
  · intro n small
    have equal : n = 0 := by omega
    simpa [equal] using base
  · intro n large
    cases n with
    | zero => omega
    | succ k => simpa [Nat.add_comm] using stepCost k
  · intro n large
    cases n with
    | zero => omega
    | succ k => simpa [Nat.add_comm] using stepCandidate k



/-! Natural-valued asymptotic bounds. Constants and thresholds are natural
numbers; constants must be positive, and finitely many sizes below the threshold
are unrestricted. This API does not define real powers or assert a Master theorem. -/

/-- Eventually, f is bounded above by one positive constant multiple of g. -/
def IsBigO (f g : Nat → Nat) : Prop :=
  ∃ C N : Nat, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n

/-- Eventually, f is bounded below up to a positive constant factor. -/
def IsBigOmega (f g : Nat → Nat) : Prop := IsBigO g f

/-- Matching eventual upper and lower bounds for natural-valued costs. -/
def IsTheta (f g : Nat → Nat) : Prop := IsBigO f g ∧ IsBigO g f

/-- A supplied eventual constant-factor bound is a Big-O certificate. -/
theorem IsBigO.of_eventual_bound {f g : Nat → Nat} (C N : Nat)
    (positive : 0 < C) (bound : ∀ n, N ≤ n → f n ≤ C * g n) : IsBigO f g :=
  ⟨C, N, positive, bound⟩

/-- An eventual comparison uses multiplicative constant one. -/
theorem IsBigO.of_eventual_le {f g : Nat → Nat} (N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ g n) : IsBigO f g :=
  ⟨1, N, by decide, fun n large => by simpa using bound n large⟩

/-- Every pointwise comparison is in particular an asymptotic upper bound. -/
theorem IsBigO.of_pointwise_le {f g : Nat → Nat}
    (bound : ∀ n, f n ≤ g n) : IsBigO f g :=
  IsBigO.of_eventual_le 0 (fun n _ => bound n)

theorem IsBigO.refl (f : Nat → Nat) : IsBigO f f :=
  IsBigO.of_pointwise_le (fun n => Nat.le_refl (f n))

/-- Composition keeps both eventual thresholds and multiplies the constants. -/
theorem IsBigO.trans {f g h : Nat → Nat} (first : IsBigO f g) (second : IsBigO g h) :
    IsBigO f h := by
  obtain ⟨C, N, positiveC, boundC⟩ := first
  obtain ⟨D, M, positiveD, boundD⟩ := second
  refine ⟨C*D, max N M, Nat.mul_pos positiveC positiveD, ?_⟩
  intro n large
  have hn : N ≤ n := Nat.le_trans (Nat.le_max_left N M) large
  have hm : M ≤ n := Nat.le_trans (Nat.le_max_right N M) large
  have scaled := Nat.mul_le_mul_left C (boundD n hm)
  simpa only [Nat.mul_assoc] using Nat.le_trans (boundC n hn) scaled

/-- Transfer an existing asymptotic bound through an eventual comparison.
    The two premises may start at different thresholds. -/
theorem IsBigO.of_eventual_comparison {f g h : Nat → Nat} (N : Nat)
    (comparison : ∀ n, N ≤ n → f n ≤ g n) (bound : IsBigO g h) : IsBigO f h :=
  (IsBigO.of_eventual_le N comparison).trans bound

/-- Directly transfer the pointwise result of a substitution proof to Big-O. -/
theorem IsBigO.of_comparison {f g h : Nat → Nat}
    (comparison : ∀ n, f n ≤ g n) (bound : IsBigO g h) : IsBigO f h :=
  (IsBigO.of_pointwise_le comparison).trans bound

/-- Positive constant-factor bounds, beyond a common threshold, give Theta. -/
theorem IsTheta.of_eventual_bounds {f g : Nat → Nat} (upperC lowerC N : Nat)
    (positiveUpper : 0 < upperC) (positiveLower : 0 < lowerC)
    (upper : ∀ n, N ≤ n → f n ≤ upperC * g n)
    (lower : ∀ n, N ≤ n → g n ≤ lowerC * f n) : IsTheta f g :=
  ⟨IsBigO.of_eventual_bound upperC N positiveUpper upper,
    IsBigO.of_eventual_bound lowerC N positiveLower lower⟩

/-- Pointwise constant-factor bounds can use threshold zero. -/
theorem IsTheta.of_pointwise_bounds {f g : Nat → Nat} (upperC lowerC : Nat)
    (positiveUpper : 0 < upperC) (positiveLower : 0 < lowerC)
    (upper : ∀ n, f n ≤ upperC * g n) (lower : ∀ n, g n ≤ lowerC * f n) : IsTheta f g :=
  IsTheta.of_eventual_bounds upperC lowerC 0 positiveUpper positiveLower
    (fun n _ => upper n) (fun n _ => lower n)

theorem IsTheta.refl (f : Nat → Nat) : IsTheta f f := ⟨IsBigO.refl f, IsBigO.refl f⟩

theorem IsTheta.symm {f g : Nat → Nat} (bound : IsTheta f g) : IsTheta g f :=
  ⟨bound.2, bound.1⟩

theorem IsTheta.trans {f g h : Nat → Nat} (first : IsTheta f g) (second : IsTheta g h) :
    IsTheta f h := ⟨first.1.trans second.1, second.2.trans first.2⟩

end Chapter4Substitution
