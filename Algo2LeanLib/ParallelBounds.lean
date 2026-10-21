import Algo2LeanLib.Parallel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Reusable mathematics for balanced fork–join algorithms.

`nodes` counts calls in a recursion tree that splits an interval into floor and
ceiling halves. `height` counts calls on its longest root-to-leaf path. These
definitions include the empty input and do not assume a power-of-two length.
Actual generated executions must separately establish their cost recurrences.
-/

namespace Algo2Lean.ParallelBounds

open Algo2LeanParallel

/-- Read-only access to a finite interval of one existing sequence. -/
def readInterval (ref : Nat) (lo : Int) (n : Nat) : Access where
  reads location := ∃ i : Int, location = .seq ref i ∧ lo ≤ i ∧ i < lo + ↑n
  writes _ := False
  allocates := false

theorem readInterval_mono (ref : Nat) (lo lo' : Int) (n n' : Nat)
    (lower : lo ≤ lo') (upper : lo' + ↑n' ≤ lo + ↑n) :
    Access.Within (readInterval ref lo' n') (readInterval ref lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro location ⟨i, identity, first, last⟩
    exact ⟨i, identity, by omega, by omega⟩
  · simp [readInterval]
  · simp [readInterval]

theorem readInterval_compatible (ref ref' : Nat) (lo lo' : Int) (n n' : Nat) :
    Access.Compatible (readInterval ref lo n) (readInterval ref' lo' n') := by
  apply Access.reads_compatible <;> simp [readInterval]

theorem readSeq_within (ref : Nat) (lo : Int) (n : Nat) (i : Int)
    (lower : lo ≤ i) (upper : i < lo + ↑n) :
    Access.Within (Access.readSeq ref i) (readInterval ref lo n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro location same
    exact ⟨i, same, lower, upper⟩
  · simp [Access.readSeq, Access.read]
  · simp [Access.readSeq, Access.read]

/-- Number of calls, including the root and singleton or empty leaves. -/
def nodes (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else nodes (n / 2) + nodes (n - n / 2) + 1
termination_by n
decreasing_by all_goals omega

/-- Number of calls on a longest dependency chain. -/
def height (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else max (height (n / 2)) (height (n - n / 2)) + 1
termination_by n
decreasing_by all_goals omega

theorem nodes_base (n : Nat) (small : n ≤ 1) : nodes n = 1 := by
  rw [nodes]; simp [small]

theorem nodes_step (n : Nat) (large : 1 < n) :
    nodes n = nodes (n / 2) + nodes (n - n / 2) + 1 := by
  rw [nodes]; simp [show ¬ n ≤ 1 by omega]

theorem height_base (n : Nat) (small : n ≤ 1) : height n = 1 := by
  rw [height]; simp [small]

theorem height_step (n : Nat) (large : 1 < n) :
    height n = max (height (n / 2)) (height (n - n / 2)) + 1 := by
  rw [height]; simp [show ¬ n ≤ 1 by omega]

@[simp] theorem nodes_zero : nodes 0 = 1 := nodes_base 0 (by decide)
@[simp] theorem nodes_one : nodes 1 = 1 := nodes_base 1 (by decide)
@[simp] theorem height_zero : height 0 = 1 := height_base 0 (by decide)
@[simp] theorem height_one : height 1 = 1 := height_base 1 (by decide)

/-- Every nonempty balanced binary tree has `n` leaves and `n-1` forks. -/
theorem nodes_exact (n : Nat) (positive : 0 < n) : nodes n + 1 = 2 * n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n ≤ 1
    · have : n = 1 := by omega
      subst n
      simp
    · have left := ih (n / 2) (by omega) (by omega)
      have right := ih (n - n / 2) (by omega) (by omega)
      rw [nodes_step n (by omega)]
      omega

theorem nodes_le_linear (n : Nat) : nodes n ≤ 2 * n + 1 := by
  by_cases zero : n = 0
  · subst n; simp
  · have := nodes_exact n (by omega)
    omega

/-- An interval fitting in `2^k` leaves has at most `k+1` levels. -/
theorem height_le_of_le_pow (n k : Nat) (size : n ≤ 2 ^ k) :
    height n ≤ k + 1 := by
  induction k generalizing n with
  | zero =>
    have small : n ≤ 1 := by simpa using size
    rw [height_base n small]
    omega
  | succ k ih =>
    by_cases small : n ≤ 1
    · rw [height_base n small]; omega
    · have powerBound : n ≤ 2 ^ k * 2 := by simpa [Nat.pow_succ] using size
      have left := ih (n / 2) (by omega)
      have right := ih (n - n / 2) (by omega)
      rw [height_step n (by omega)]
      omega

/-- Uniform logarithmic depth, including zero and non-power-of-two sizes. -/
theorem height_le_logarithmic (n : Nat) : height n ≤ Nat.log2 n + 2 := by
  have := height_le_of_le_pow n (Nat.log2 n + 1) (Nat.le_of_lt Nat.lt_log2_self)
  omega

/-- Charge at most `c` at each leaf and fork of a balanced recursion. -/
theorem work_le_nodes (work : Nat → Nat) (c : Nat)
    (base : ∀ n, n ≤ 1 → work n ≤ c)
    (step : ∀ n, 1 < n → work n ≤ work (n / 2) + work (n - n / 2) + c)
    (n : Nat) : work n ≤ c * nodes n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n ≤ 1
    · simpa [nodes_base n small] using base n small
    · have left := ih (n / 2) (by omega)
      have right := ih (n - n / 2) (by omega)
      calc
        work n ≤ work (n / 2) + work (n - n / 2) + c := step n (by omega)
        _ ≤ c * nodes (n / 2) + c * nodes (n - n / 2) + c := by omega
        _ = c * nodes n := by rw [nodes_step n (by omega), Nat.mul_add, Nat.mul_add, Nat.mul_one]

/-- Charge at most `c` on each level of a balanced dependency chain. -/
theorem span_le_height (span : Nat → Nat) (c : Nat)
    (base : ∀ n, n ≤ 1 → span n ≤ c)
    (step : ∀ n, 1 < n → span n ≤ max (span (n / 2)) (span (n - n / 2)) + c)
    (n : Nat) : span n ≤ c * height n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n ≤ 1
    · simpa [height_base n small] using base n small
    · have left := ih (n / 2) (by omega)
      have right := ih (n - n / 2) (by omega)
      have left' := Nat.mul_le_mul_left c (Nat.le_max_left (height (n / 2)) (height (n - n / 2)))
      have right' := Nat.mul_le_mul_left c (Nat.le_max_right (height (n / 2)) (height (n - n / 2)))
      calc
        span n ≤ max (span (n / 2)) (span (n - n / 2)) + c := step n (by omega)
        _ ≤ c * max (height (n / 2)) (height (n - n / 2)) + c := by omega
        _ = c * height n := by rw [height_step n (by omega), Nat.mul_add, Nat.mul_one]

/-- The abstract work recurrence yields a concrete linear bound. -/
theorem work_le_linear (work : Nat → Nat) (c : Nat)
    (base : ∀ n, n ≤ 1 → work n ≤ c)
    (step : ∀ n, 1 < n → work n ≤ work (n / 2) + work (n - n / 2) + c)
    (n : Nat) : work n ≤ c * (2 * n + 1) :=
  Nat.le_trans (work_le_nodes work c base step n) (Nat.mul_le_mul_left c (nodes_le_linear n))

/-- The abstract span recurrence yields a concrete logarithmic bound. -/
theorem span_le_logarithmic (span : Nat → Nat) (c : Nat)
    (base : ∀ n, n ≤ 1 → span n ≤ c)
    (step : ∀ n, 1 < n → span n ≤ max (span (n / 2)) (span (n - n / 2)) + c)
    (n : Nat) : span n ≤ c * (Nat.log2 n + 2) :=
  Nat.le_trans (span_le_height span c base step n) (Nat.mul_le_mul_left c (height_le_logarithmic n))

/-- Sum of a finite interval of a total integer sequence. -/
def intervalSum (a : Int → Int) (lo : Int) : Nat → Int
  | 0 => 0
  | n + 1 => intervalSum a lo n + a (lo + n)

@[simp] theorem intervalSum_zero (a : Int → Int) (lo : Int) : intervalSum a lo 0 = 0 := rfl

@[simp] theorem intervalSum_one (a : Int → Int) (lo : Int) : intervalSum a lo 1 = a lo := by
  simp [intervalSum]

/-- Concatenating adjacent intervals adds their sums. -/
theorem intervalSum_add (a : Int → Int) (lo : Int) (m n : Nat) :
    intervalSum a lo (m + n) = intervalSum a lo m + intervalSum a (lo + m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change intervalSum a lo (m + n) + a (lo + ↑(m + n)) =
      intervalSum a lo m + (intervalSum a (lo + ↑m) n + a ((lo + ↑m) + ↑n))
    rw [ih]
    have index : lo + ↑(m + n) = (lo + ↑m) + ↑n := by omega
    rw [index]
    omega

/-- Splitting at any boundary preserves the mathematical sum. -/
theorem intervalSum_split (a : Int → Int) (lo : Int) (n m : Nat) (bound : m ≤ n) :
    intervalSum a lo n = intervalSum a lo m + intervalSum a (lo + m) (n - m) := by
  have := intervalSum_add a lo m (n - m)
  simpa [Nat.add_sub_of_le bound] using this

/-- Only values inside the requested interval affect its sum. -/
theorem intervalSum_congr (a b : Int → Int) (lo : Int) (n : Nat)
    (same : ∀ i : Nat, i < n → a (lo + i) = b (lo + i)) :
    intervalSum a lo n = intervalSum b lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [intervalSum]
    rw [ih (fun i hi => same i (by omega)), same n (by omega)]

/-- Inclusive prefix sums at every valid output index. -/
def IsPrefixSum (a b : Int → Int) (lo : Int) (n : Nat) : Prop :=
  ∀ i : Nat, i < n → b (lo + i) = intervalSum a lo (i + 1)

/-- Exclusive prefix sums with the accumulated total preceding this interval. -/
def IsExclusivePrefixSum (a b : Int → Int) (lo : Int) (n : Nat)
    (offset : Int := 0) : Prop :=
  ∀ i : Nat, i < n → b (lo + i) = offset + intervalSum a lo i

/-- Two adjacent exclusive scans combine after the right offset is shifted by
the total of the left interval. -/
theorem exclusivePrefixSum_append (a b : Int → Int) (lo : Int) (m n : Nat)
    (offset : Int)
    (left : IsExclusivePrefixSum a b lo m offset)
    (right : IsExclusivePrefixSum a b (lo + m) n (offset + intervalSum a lo m)) :
    IsExclusivePrefixSum a b lo (m + n) offset := by
  intro i hi
  by_cases before : i < m
  · exact left i before
  · have bound : i - m < n := by omega
    have shifted := right (i - m) bound
    have index : lo + ↑m + ↑(i - m) = lo + ↑i := by omega
    rw [index] at shifted
    have sum := intervalSum_split a lo i m (by omega)
    rw [sum]
    omega

/-- Scratch values needed by the down-sweep. Each internal node retains its
left subtree's total. A parent's final write may overwrite its right child's
root total; that total is deliberately not required by this invariant. -/
def PrefixTree (a sums : Int → Int) (lo : Int) (n : Nat) : Prop :=
  if n ≤ 1 then True
  else
    sums (lo + ↑(n / 2) - 1) = intervalSum a lo (n / 2) ∧
    PrefixTree a sums lo (n / 2) ∧
    PrefixTree a sums (lo + ↑(n / 2)) (n - n / 2)
termination_by n
decreasing_by all_goals omega

theorem prefixTree_base (a sums : Int → Int) (lo : Int) (n : Nat)
    (small : n ≤ 1) : PrefixTree a sums lo n := by
  rw [PrefixTree]; simp [small]

theorem prefixTree_step (a sums : Int → Int) (lo : Int) (n : Nat)
    (large : 1 < n) : PrefixTree a sums lo n ↔
      sums (lo + ↑(n / 2) - 1) = intervalSum a lo (n / 2) ∧
      PrefixTree a sums lo (n / 2) ∧
      PrefixTree a sums (lo + ↑(n / 2)) (n - n / 2) := by
  rw [PrefixTree]; simp [show ¬ n ≤ 1 by omega]

/-- The down-sweep reads scratch cells strictly before the final interval
index. Changing any other scratch cells preserves its representation. -/
theorem prefixTree_congr (a sums sums' : Int → Int) (lo : Int) (n : Nat)
    (same : ∀ i : Int, lo ≤ i → i < lo + ↑n - 1 → sums i = sums' i)
    (tree : PrefixTree a sums lo n) : PrefixTree a sums' lo n := by
  induction n using Nat.strongRecOn generalizing lo with
  | ind n ih =>
    by_cases small : n ≤ 1
    · exact prefixTree_base a sums' lo n small
    · have large : 1 < n := by omega
      rw [prefixTree_step a sums lo n large] at tree
      rw [prefixTree_step a sums' lo n large]
      refine ⟨?_, ?_, ?_⟩
      · rw [← same (lo + ↑(n / 2) - 1) (by omega) (by omega)]
        exact tree.1
      · apply ih (n / 2) (by omega) lo _ tree.2.1
        intro i lower upper
        exact same i lower (by omega)
      · apply ih (n - n / 2) (by omega) (lo + ↑(n / 2)) _ tree.2.2
        intro i lower upper
        exact same i (by omega) (by omega)

/-- Saving the whole subtree's total at its last cell leaves all required
left-subtree totals available for the down-sweep. -/
theorem prefixTree_write_last (a sums : Int → Int) (lo : Int) (n : Nat) (value : Int)
    (tree : PrefixTree a sums lo n) :
    PrefixTree a (fun i => if i = lo + ↑n - 1 then value else sums i) lo n := by
  apply prefixTree_congr a sums _ lo n _ tree
  intro i _ before
  simp [show i ≠ lo + ↑n - 1 by omega]

end Algo2Lean.ParallelBounds
