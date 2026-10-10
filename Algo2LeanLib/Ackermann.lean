import Std

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The Ackermann hierarchy used in the union-find amortized analysis.
`ack 0 r = r + 1` and `ack (k + 1) r` applies `ack k` exactly `r + 1`
times to `r`. The inverse `alpha n` is the least positive hierarchy index
whose value at one exceeds `n`. All arithmetic facts are independent of
program execution and of the union-find representation.
-/

namespace Algo2Lean.Ackermann

/-- Apply a natural-number function a fixed number of times. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, value => value
  | count + 1, value => f (iterate f count value)

@[simp] theorem iterate_zero (f : Nat → Nat) (value : Nat) :
    iterate f 0 value = value := rfl

@[simp] theorem iterate_succ (f : Nat → Nat) (count value : Nat) :
    iterate f (count + 1) value = f (iterate f count value) := rfl

theorem iterate_add (f : Nat → Nat) (first second value : Nat) :
    iterate f (first + second) value = iterate f first (iterate f second value) := by
  induction first with
  | zero => simp
  | succ first ih => simp [Nat.succ_add, ih]

theorem iterate_succ_first (f : Nat → Nat) (count value : Nat) :
    iterate f (count + 1) value = iterate f count (f value) := by
  simpa using iterate_add f count 1 value

theorem iterate_mono_start {f : Nat → Nat}
    (mono : ∀ {a b}, a ≤ b → f a ≤ f b) (count : Nat) {a b : Nat} (ordered : a ≤ b) :
    iterate f count a ≤ iterate f count b := by
  induction count with
  | zero => exact ordered
  | succ count ih => exact mono ih

theorem iterate_strict_start {f : Nat → Nat}
    (strict : ∀ {a b}, a < b → f a < f b) (count : Nat) {a b : Nat} (ordered : a < b) :
    iterate f count a < iterate f count b := by
  induction count with
  | zero => exact ordered
  | succ count ih => exact strict ih

theorem iterate_mono_count {f : Nat → Nat}
    (grow : ∀ value, value ≤ f value) {first second : Nat} (ordered : first ≤ second)
    (value : Nat) : iterate f first value ≤ iterate f second value := by
  induction second generalizing first with
  | zero =>
    have zero : first = 0 := by omega
    simp [zero]
  | succ second ih =>
    by_cases same : first = second + 1
    · subst first; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (grow _)

theorem iterate_strict_count {f : Nat → Nat}
    (grow : ∀ value, value < f value) {first second : Nat} (ordered : first < second)
    (value : Nat) : iterate f first value < iterate f second value := by
  have step := grow (iterate f first value)
  have rest := iterate_mono_count (fun x => Nat.le_of_lt (grow x)) ordered value
  exact Nat.lt_of_lt_of_le step rest

theorem iterate_ge_start {f : Nat → Nat} (grow : ∀ value, value ≤ f value)
    (count value : Nat) : value ≤ iterate f count value :=
  iterate_mono_count grow (Nat.zero_le count) value

/-- The increasing hierarchy obtained by repeated iteration. -/
def ack : Nat → Nat → Nat
  | 0, value => value + 1
  | level + 1, value => iterate (ack level) (value + 1) value

@[simp] theorem ack_zero (value : Nat) : ack 0 value = value + 1 := rfl

theorem ack_succ (level value : Nat) :
    ack (level + 1) value = iterate (ack level) (value + 1) value := rfl

theorem ack_gt (level value : Nat) : value < ack level value := by
  induction level generalizing value with
  | zero => simp
  | succ level ih =>
    have start := ih value
    have rest := iterate_mono_count (fun x => Nat.le_of_lt (ih x))
      (Nat.succ_le_succ (Nat.zero_le value)) value
    exact Nat.lt_of_lt_of_le start rest

theorem ack_strict_right (level : Nat) {a b : Nat} (ordered : a < b) :
    ack level a < ack level b := by
  induction level generalizing a b with
  | zero => simpa using ordered
  | succ level ih =>
    have start := iterate_strict_start ih (a + 1) ordered
    have rest := iterate_mono_count (fun x => Nat.le_of_lt (ack_gt level x))
      (Nat.succ_le_succ (Nat.le_of_lt ordered)) b
    exact Nat.lt_of_lt_of_le start rest

theorem ack_mono_right (level : Nat) {a b : Nat} (ordered : a ≤ b) :
    ack level a ≤ ack level b := by
  rcases Nat.eq_or_lt_of_le ordered with same | smaller
  · simp [same]
  · exact Nat.le_of_lt (ack_strict_right level smaller)

theorem ack_le_succ (level value : Nat) : ack level value ≤ ack (level + 1) value := by
  exact iterate_mono_count (fun x => Nat.le_of_lt (ack_gt level x))
    (Nat.succ_le_succ (Nat.zero_le value)) value

theorem ack_mono_left {first second : Nat} (ordered : first ≤ second) (value : Nat) :
    ack first value ≤ ack second value := by
  induction second generalizing first with
  | zero =>
    have zero : first = 0 := by omega
    simp [zero]
  | succ second ih =>
    by_cases same : first = second + 1
    · subst first; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (ack_le_succ second value)

theorem ack_lt_succ (level : Nat) {value : Nat} (positive : 0 < value) :
    ack level value < ack (level + 1) value := by
  exact iterate_strict_count (ack_gt level) (by omega : 1 < value + 1) value

theorem index_bound (level : Nat) : level + 2 ≤ ack level 1 := by
  induction level with
  | zero => simp
  | succ level ih =>
    have growing := ack_lt_succ level (by decide : 0 < 1)
    omega

/-- Every inhabited natural-number predicate has a least witness. -/
private theorem least_exists (property : Nat → Prop) (inhabited : ∃ value, property value) :
    ∃ value, property value ∧ ∀ other, other < value → ¬ property other := by
  classical
  obtain ⟨bound, holds⟩ := inhabited
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    by_cases earlier : ∃ other, other < bound ∧ property other
    · obtain ⟨other, smaller, valid⟩ := earlier
      exact ih other smaller valid
    · exact ⟨bound, holds, fun other smaller valid => earlier ⟨other, smaller, valid⟩⟩

private theorem inverse_exists (n : Nat) :
    ∃ level, (0 < level ∧ n < ack level 1) ∧
      ∀ other, other < level → ¬ (0 < other ∧ n < ack other 1) := by
  apply least_exists
  refine ⟨n + 1, by omega, ?_⟩
  have := index_bound (n + 1)
  omega

/-- Least positive level whose Ackermann value at one exceeds the input. -/
noncomputable def alpha (n : Nat) : Nat := Classical.choose (inverse_exists n)

theorem alpha_pos (n : Nat) : 0 < alpha n :=
  (Classical.choose_spec (inverse_exists n)).1.1

theorem ack_alpha_gt (n : Nat) : n < ack (alpha n) 1 :=
  (Classical.choose_spec (inverse_exists n)).1.2

theorem alpha_min {n level : Nat} (positive : 0 < level) (smaller : level < alpha n) :
    ack level 1 ≤ n := by
  have minimal := (Classical.choose_spec (inverse_exists n)).2 level smaller
  omega

theorem alpha_le {n level : Nat} (positive : 0 < level) (large : n < ack level 1) :
    alpha n ≤ level := by
  by_cases ordered : alpha n ≤ level
  · exact ordered
  · have := alpha_min positive (by omega : level < alpha n)
    omega

theorem alpha_mono {first second : Nat} (ordered : first ≤ second) :
    alpha first ≤ alpha second :=
  alpha_le (alpha_pos second) (Nat.lt_of_le_of_lt ordered (ack_alpha_gt second))

/-- A positive hierarchy index bounds the inverse exactly when its threshold
    exceeds the input. This avoids evaluating the noncomputable least witness. -/
theorem alpha_le_iff {n level : Nat} (positive : 0 < level) :
    alpha n ≤ level ↔ n < ack level 1 := by
  constructor
  · intro bound
    exact Nat.lt_of_lt_of_le (ack_alpha_gt n) (ack_mono_left bound 1)
  · exact alpha_le positive

set_option maxRecDepth 10000 in
/-- The first three thresholds make the convention for the inverse explicit. -/
theorem thresholds : ack 1 1 = 3 ∧ ack 2 1 = 7 ∧ ack 3 1 = 2047 := by
  decide

theorem alpha_le_one_iff (n : Nat) : alpha n ≤ 1 ↔ n < 3 := by
  simpa only [thresholds.1] using (alpha_le_iff (n := n) (by decide : 0 < 1))

theorem alpha_le_two_iff (n : Nat) : alpha n ≤ 2 ↔ n < 7 := by
  simpa only [thresholds.2.1] using (alpha_le_iff (n := n) (by decide : 0 < 2))

theorem alpha_le_three_iff (n : Nat) : alpha n ≤ 3 ↔ n < 2047 := by
  simpa only [thresholds.2.2] using (alpha_le_iff (n := n) (by decide : 0 < 3))

end Algo2Lean.Ackermann
