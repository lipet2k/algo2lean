import Algo2Lean

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock contracts describe increments from the caller's actual initial heap.
Weighted and amortized bounds compose on the same finite call witness used
for correctness; no counter is reset and no second execution is selected.
-/

namespace Algo2LeanGenerated

/-- Every named counter is nondecreasing between the supplied heap snapshots. -/
def Heap.ClocksMonotone (before after : Heap) : Prop :=
  ∀ name, before.clocks name ≤ after.clocks name

theorem Heap.ClocksMonotone.refl (heap : Heap) : heap.ClocksMonotone heap :=
  fun _ => Nat.le_refl _

theorem Heap.ClocksMonotone.trans {before middle after : Heap}
    (first : before.ClocksMonotone middle) (second : middle.ClocksMonotone after) :
    before.ClocksMonotone after := fun name => Nat.le_trans (first name) (second name)

/-- An exact clock effect permits arbitrary program-data changes and arbitrary
    initial counter values. -/
def Heap.Increments (before after : Heap) (costs : Clocks) : Prop :=
  ∀ name, after.clocks name = before.clocks name + costs name

theorem Heap.Increments.refl (heap : Heap) : heap.Increments heap (fun _ => 0) := by
  intro name
  simp

theorem Heap.Increments.charge (heap : Heap) (costs : Clocks) :
    heap.Increments (heap.charge costs) costs := fun _ => rfl

theorem Heap.Increments.trans {before middle after : Heap} {first second : Clocks}
    (one : before.Increments middle first) (two : middle.Increments after second) :
    before.Increments after (Clocks.add first second) := by
  intro name
  rw [two name, one name]
  simp [Clocks.add, Nat.add_assoc]

theorem Heap.Increments.monotone {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) : before.ClocksMonotone after := by
  intro name
  rw [effect name]
  exact Nat.le_add_right _ _

theorem Heap.Increments.cost {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) : Heap.cost before after = costs := by
  funext name
  simp [Heap.cost, effect name]

theorem Heap.ClocksMonotone.increments {before after : Heap}
    (monotone : before.ClocksMonotone after) :
    before.Increments after (Heap.cost before after) := by
  intro name
  have ordered := monotone name
  simp only [Heap.cost]
  omega

/-- A finite metric combines named counters with natural weights. Repeated
    names deliberately add their weights, so overlapping metrics compose. -/
def Clocks.weighted (metric : List (String × Nat)) (costs : Clocks) : Nat :=
  (metric.map fun (name, weight) => weight * costs name).sum

@[simp] theorem Clocks.weighted_zero (metric : List (String × Nat)) :
    weighted metric (fun _ => 0) = 0 := by
  induction metric with
  | nil => rfl
  | cons entry rest ih =>
    simpa only [weighted, List.map_cons, List.sum_cons, Nat.mul_zero, Nat.zero_add] using ih

theorem Clocks.weighted_add (metric : List (String × Nat)) (first second : Clocks) :
    weighted metric (add first second) = weighted metric first + weighted metric second := by
  induction metric with
  | nil => rfl
  | cons entry rest ih =>
    simp only [weighted, List.map_cons, List.sum_cons] at *
    rw [ih]
    simp [add, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm]

theorem Clocks.weighted_le (metric : List (String × Nat)) {first second : Clocks}
    (bound : ∀ name, first name ≤ second name) : weighted metric first ≤ weighted metric second := by
  induction metric with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
    exact Nat.add_le_add (Nat.mul_le_mul_left entry.2 (bound entry.1)) ih

/-- The selected metric measures the actual change in the shared heap. -/
def Heap.weightedCost (metric : List (String × Nat)) (before after : Heap) : Nat :=
  Clocks.weighted metric (Heap.cost before after)

@[simp] theorem Heap.weightedCost_self (metric : List (String × Nat)) (heap : Heap) :
    weightedCost metric heap heap = 0 := by
  have zero : Heap.cost heap heap = fun _ => 0 := by
    funext name
    exact Heap.cost_self heap name
  simp [weightedCost, zero]

theorem Heap.weightedCost_add (metric : List (String × Nat)) {before middle after : Heap}
    (first : before.ClocksMonotone middle) (second : middle.ClocksMonotone after) :
    weightedCost metric before after =
      weightedCost metric before middle + weightedCost metric middle after := by
  have costs : Heap.cost before after =
      Clocks.add (Heap.cost before middle) (Heap.cost middle after) := by
    funext name
    exact Heap.cost_add before middle after name (first name) (second name)
  simp only [weightedCost, costs, Clocks.weighted_add]

namespace CallCost

universe u
variable {State : Type u}

/-- Add one budget for each adjacent pair in a supplied finite call transcript. -/
def total (budget : State → State → Nat) : List State → Nat
  | [] => 0
  | [_] => 0
  | before :: after :: rest => budget before after + total budget (after :: rest)

theorem total_cons (budget : State → State → Nat)
    (run : Algo2LeanCore.Valid call middle states after) (before : State) :
    total budget (before :: states) = budget before middle + total budget states := by
  cases run <;> rfl

/-- Counter monotonicity lifts through exactly the supplied finite calls. -/
theorem monotone (heap : State → Heap)
    (run : Algo2LeanCore.Valid call before states after)
    (localMonotone : ∀ a b, call a b → (heap a).ClocksMonotone (heap b)) :
    (heap before).ClocksMonotone (heap after) := by
  induction run with
  | single => exact Heap.ClocksMonotone.refl _
  | cons transition _ ih => exact (localMonotone _ _ transition).trans ih

/-- Local potential charges telescope along one supplied call transcript.
    `call` may include execution, representation, and correctness facts together;
    the bound therefore applies to those same call outcomes and heap witnesses. -/
theorem amortized (metric : List (String × Nat)) (heap : State → Heap)
    (potential : State → Nat) (budget : State → State → Nat)
    (run : Algo2LeanCore.Valid call before states after)
    (localMonotone : ∀ a b, call a b → (heap a).ClocksMonotone (heap b))
    (localBound : ∀ a b, call a b →
      Heap.weightedCost metric (heap a) (heap b) + potential b ≤ potential a + budget a b) :
    Heap.weightedCost metric (heap before) (heap after) + potential after ≤
      potential before + total budget states := by
  induction run with
  | single => simp [total]
  | @cons before middle states after transition tail ih =>
    have first := localMonotone _ _ transition
    have rest := monotone heap tail localMonotone
    have bound := localBound _ _ transition
    rw [Heap.weightedCost_add metric first rest, total_cons budget tail before]
    omega

/-- Dropping the nonnegative final potential gives the usual total-work bound. -/
theorem bound (metric : List (String × Nat)) (heap : State → Heap)
    (potential : State → Nat) (budget : State → State → Nat)
    (run : Algo2LeanCore.Valid call before states after)
    (localMonotone : ∀ a b, call a b → (heap a).ClocksMonotone (heap b))
    (localBound : ∀ a b, call a b →
      Heap.weightedCost metric (heap a) (heap b) + potential b ≤ potential a + budget a b) :
    Heap.weightedCost metric (heap before) (heap after) ≤ potential before + total budget states := by
  have telescoped := amortized metric heap potential budget run localMonotone localBound
  omega

end CallCost
end Algo2LeanGenerated
