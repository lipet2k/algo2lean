import RangeSumGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `output`: Range sum output exists.
- `stepped_summary`: Reusable signed-step range contract.
- `stepped_output`: Signed-step range sum output.
- `zero_step_no_output`: Zero step has no output.
- `empty_range_output`: Empty range preserves loop binding.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace RangeSumAnalysis

/-- Sum `count` terms of an arithmetic progression. -/
def progressionSum (first step : Int) : Nat → Int
  | 0 => 0
  | count + 1 => first + progressionSum (first + step) step count

/-- A reached, named range-body state finishes by summing its remaining terms.
    The entry reachability premise justifies the bounds captured by `range`;
    getters alone intentionally do not expose that private implementation data. -/
theorem remaining_summary (count : Nat) (state : Configuration) (heap : Heap)
    (n first total : Int)
    (reachable : Reaches Step (range_sum.initial heap n) state)
    (location : range_sum.At.iteration state)
    (readFirst : range_sum.Local.i state = some first)
    (readTotal : range_sum.Local.total state = some total)
    (bound : n = first + (count : Int) + 1) :
    range_sum.CallFrom state state.heap
      (total + progressionSum first 1 (count + 1)) := by
  induction count generalizing state first total with
  | zero =>
    cases state with
    | done => cases location
    | active currentHeap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_stepped_sum => cases location
      | fn_empty_range_preserves_binding => cases location
      | fn_range_sum pc s =>
        have counter : pc = 5 := by
          unfold range_sum.At.iteration at location
          split at location <;> simp_all
        subst pc
        simp [range_sum.Local.i, range_sum.Local.total] at readFirst readTotal
        have captured := reachable.invariant
          (fun cfg => match cfg with
            | .active _ (.fn_range_sum pc s) stack =>
                stack = [] ∧ s.v0 = n ∧ (pc ≤ 9 → s.t5 = n) ∧
                (pc ≤ 7 → s.t6 = 1) ∧ (pc = 5 → s.v2 = s.t4)
            | .done _ (.fn_range_sum _) => True
            | _ => False)
          (by simp [range_sum.initial, start])
          (by intro before after transition hypothesis
              cases transition <;> simp_all [resumeConfig])
        simp at captured
        intro stack
        apply Reaches.trans (Reaches.single (Step.range_sum_pc5 ..))
        apply Reaches.trans (Reaches.single (Step.range_sum_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.range_sum_pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega)))
        apply Reaches.trans (Reaches.single (Step.range_sum_pc2 ..))
        simpa [progressionSum, readFirst, readTotal, Config.heap] using
          Reaches.single (Step.range_sum_pc1 currentHeap _ stack)
  | succ count inductionHypothesis =>
    cases state with
    | done => cases location
    | active currentHeap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_stepped_sum => cases location
      | fn_empty_range_preserves_binding => cases location
      | fn_range_sum pc s =>
        have counter : pc = 5 := by
          unfold range_sum.At.iteration at location
          split at location <;> simp_all
        subst pc
        simp [range_sum.Local.i, range_sum.Local.total] at readFirst readTotal
        have captured := reachable.invariant
          (fun cfg => match cfg with
            | .active _ (.fn_range_sum pc s) stack =>
                stack = [] ∧ s.v0 = n ∧ (pc ≤ 9 → s.t5 = n) ∧
                (pc ≤ 7 → s.t6 = 1) ∧ (pc = 5 → s.v2 = s.t4)
            | .done _ (.fn_range_sum _) => True
            | _ => False)
          (by simp [range_sum.initial, start])
          (by intro before after transition hypothesis
              cases transition <;> simp_all [resumeConfig])
        simp at captured
        have condition : decide ((s.t6 > 0 ∧ s.t4 + s.t6 < s.t5) ∨
            (s.t6 < 0 ∧ s.t4 + s.t6 > s.t5)) = true := by
          simp only [decide_eq_true_eq]; omega
        have progress := (Reaches.single (Step.range_sum_pc5 currentHeap s originalStack)).trans
          ((Reaches.single (Step.range_sum_pc4 ..)).trans
            ((Reaches.single (Step.range_sum_pc3_true _ _ _ condition)).trans
              (Reaches.single (Step.range_sum_pc6 ..))))
        have next := inductionHypothesis _ (first + 1) (total + first)
          (reachable.trans progress) True.intro
          (by simp [range_sum.Local.i]; omega)
          (by simp [range_sum.Local.total]; omega)
          (by omega)
        intro stack
        apply Reaches.trans (Reaches.single (Step.range_sum_pc5 ..))
        apply Reaches.trans (Reaches.single (Step.range_sum_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.range_sum_pc3_true _ _ _ condition))
        apply Reaches.trans (Reaches.single (Step.range_sum_pc6 ..))
        simpa [progressionSum, Int.add_assoc, Config.heap] using next stack

/-- `range(n)` returns the sum of 0, ..., n-1 for a natural input. -/
theorem natural_summary (heap : Heap) (n : Nat) :
    range_sum.Call heap (n : Int) heap (progressionSum 0 1 n) := by
  cases n with
  | zero =>
    refine ⟨True.intro, ?_⟩
    intro stack
    apply Reaches.trans (Reaches.single (Step.range_sum_pc11 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc10 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc9 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc8 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc7 _ _ _ (by decide)))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc3_false _ _ _ (by decide)))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc2 ..))
    exact Reaches.single (Step.range_sum_pc1 ..)
  | succ n =>
    have initialSegment := (Reaches.single (Step.range_sum_pc11 heap { v0 := (n+1 : Nat) } [])).trans
      ((Reaches.single (Step.range_sum_pc10 ..)).trans
        ((Reaches.single (Step.range_sum_pc9 ..)).trans
          ((Reaches.single (Step.range_sum_pc8 ..)).trans
            ((Reaches.single (Step.range_sum_pc7 _ _ _ (by simp))).trans
              ((Reaches.single (Step.range_sum_pc3_true _ _ _ (by simp))).trans
                (Reaches.single (Step.range_sum_pc6 ..)))))))
    have rest := remaining_summary n _ heap (n+1 : Nat) 0 0 initialSegment True.intro
      rfl rfl (by omega)
    refine ⟨True.intro, ?_⟩
    intro stack
    apply Reaches.trans (Reaches.single (Step.range_sum_pc11 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc10 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc9 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc8 ..))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc7 _ _ _ (by simp)))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc3_true _ _ _ (by simp)))
    apply Reaches.trans (Reaches.single (Step.range_sum_pc6 ..))
    simpa using! rest stack

/-- A nonpositive stop makes `range(n)` empty. -/
theorem nonpositive_summary (heap : Heap) (n : Int) (nonpositive : n ≤ 0) :
    range_sum.Call heap n heap 0 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.range_sum_pc11 ..))
  apply Reaches.trans (Reaches.single (Step.range_sum_pc10 ..))
  apply Reaches.trans (Reaches.single (Step.range_sum_pc9 ..))
  apply Reaches.trans (Reaches.single (Step.range_sum_pc8 ..))
  apply Reaches.trans (Reaches.single (Step.range_sum_pc7 _ _ _ (by simp)))
  apply Reaches.trans (Reaches.single (Step.range_sum_pc3_false _ _ _
    (by simp only [decide_eq_false_iff_not]; omega)))
  apply Reaches.trans (Reaches.single (Step.range_sum_pc2 ..))
  exact Reaches.single (Step.range_sum_pc1 ..)

/-- Every integer input has a reusable call contract. The entire caller heap,
    including existing storage and clocks, remains unchanged. -/
theorem summary (heap : Heap) (n : Int) :
    range_sum.Call heap n heap (progressionSum 0 1 n.toNat) := by
  by_cases nonpositive : n ≤ 0
  · simpa [Int.toNat_eq_zero.mpr nonpositive, progressionSum] using
      nonpositive_summary heap n nonpositive
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ n)] using natural_summary heap n.toNat

/-- Every integer input has the specified finite sum as an output.
    The theorem asserts existence, not uniqueness. -/
theorem output (n : Int) : range_sum.Returns n (progressionSum 0 1 n.toNat) :=
  ⟨{}, (summary {} n).run⟩

/-- Resume a reached, named stepped-range body. The public reachability premise
    supplies the once-evaluated range bounds; no private iterator appears in the
    helper's statement. -/
theorem stepped_remaining_summary (count : Nat) (state : Configuration) (heap : Heap)
    (start stop step first total : Int) (nonzero : step ≠ 0)
    (reachable : Reaches Step (stepped_sum.initial heap (start, stop, step)) state)
    (location : stepped_sum.At.iteration state)
    (readFirst : stepped_sum.Local.i state = some first)
    (readTotal : stepped_sum.Local.total state = some total)
    (bound : stop = first + ((count + 1 : Nat) : Int) * step) :
    stepped_sum.CallFrom state state.heap
      (total + progressionSum first step (count + 1)) := by
  induction count generalizing state first total with
  | zero =>
    cases state with
    | done => cases location
    | active currentHeap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_range_sum => cases location
      | fn_empty_range_preserves_binding => cases location
      | fn_stepped_sum pc s =>
        have counter : pc = 5 := by
          unfold stepped_sum.At.iteration at location
          split at location <;> simp_all
        subst pc
        simp [stepped_sum.Local.i, stepped_sum.Local.total] at readFirst readTotal
        have captured := reachable.invariant
          (fun cfg => match cfg with
            | .active _ (.fn_stepped_sum pc s) stack =>
                stack = [] ∧ s.v1 = stop ∧ s.v2 = step ∧
                (pc ≤ 8 → s.t7 = stop) ∧ (pc ≤ 7 → s.t8 = step) ∧
                (pc = 5 → s.v4 = s.t6)
            | .done _ (.fn_stepped_sum _) => True
            | _ => False)
          (by simp [stepped_sum.initial, Algo2LeanCore.start])
          (by intro before after transition hypothesis
              cases transition <;> simp_all [resumeConfig])
        simp at captured bound
        intro stack
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc5 ..))
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega)))
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc2 ..))
        simpa [progressionSum, readFirst, readTotal, Config.heap] using
          Reaches.single (Step.stepped_sum_pc1 currentHeap _ stack)
  | succ count inductionHypothesis =>
    cases state with
    | done => cases location
    | active currentHeap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_range_sum => cases location
      | fn_empty_range_preserves_binding => cases location
      | fn_stepped_sum pc s =>
        have counter : pc = 5 := by
          unfold stepped_sum.At.iteration at location
          split at location <;> simp_all
        subst pc
        simp [stepped_sum.Local.i, stepped_sum.Local.total] at readFirst readTotal
        have captured := reachable.invariant
          (fun cfg => match cfg with
            | .active _ (.fn_stepped_sum pc s) stack =>
                stack = [] ∧ s.v1 = stop ∧ s.v2 = step ∧
                (pc ≤ 8 → s.t7 = stop) ∧ (pc ≤ 7 → s.t8 = step) ∧
                (pc = 5 → s.v4 = s.t6)
            | .done _ (.fn_stepped_sum _) => True
            | _ => False)
          (by simp [stepped_sum.initial, Algo2LeanCore.start])
          (by intro before after transition hypothesis
              cases transition <;> simp_all [resumeConfig])
        simp at captured
        have nextBound : stop = first + step + ((count + 1 : Nat) : Int) * step := by
          simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul] at bound ⊢
          omega
        have positiveCount : 0 < ((count + 1 : Nat) : Int) := by omega
        have condition : decide ((s.t8 > 0 ∧ s.t6 + s.t8 < s.t7) ∨
            (s.t8 < 0 ∧ s.t6 + s.t8 > s.t7)) = true := by
          simp only [decide_eq_true_eq]
          by_cases positiveStep : 0 < step
          · have increase := Int.mul_pos positiveCount positiveStep
            left; constructor <;> omega
          · have decrease := Int.mul_neg_of_pos_of_neg positiveCount (by omega : step < 0)
            right; constructor <;> omega
        have progress := (Reaches.single (Step.stepped_sum_pc5 currentHeap s originalStack)).trans
          ((Reaches.single (Step.stepped_sum_pc4 ..)).trans
            ((Reaches.single (Step.stepped_sum_pc3_true _ _ _ condition)).trans
              (Reaches.single (Step.stepped_sum_pc6 ..))))
        have next := inductionHypothesis _ (first + step) (total + first)
          (reachable.trans progress) True.intro
          (by simp [stepped_sum.Local.i]; omega)
          (by simp [stepped_sum.Local.total]; omega) nextBound
        intro stack
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc5 ..))
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc4 ..))
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc3_true _ _ _ condition))
        apply Reaches.trans (Reaches.single (Step.stepped_sum_pc6 ..))
        simpa [progressionSum, Int.add_assoc, Config.heap] using next stack

/-- Both positive and negative steps traverse an arithmetic progression. The
    exclusive stop here is exactly `count` steps away from the start. -/
theorem stepped_summary (heap : Heap) (first step : Int) (count : Nat)
    (nonzero : step ≠ 0) :
    stepped_sum.Call heap (first, first + (count : Int) * step, step)
      heap (progressionSum first step count) := by
  cases count with
  | zero =>
    refine ⟨True.intro, ?_⟩
    intro stack
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc11 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc10 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc9 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc8 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc7 _ _ _ nonzero))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc3_false _ _ _ (by simp)))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc2 ..))
    exact Reaches.single (Step.stepped_sum_pc1 ..)
  | succ count =>
    have positiveCount : 0 < ((count + 1 : Nat) : Int) := by omega
    have condition : decide ((step > 0 ∧ first < first + ((count + 1 : Nat) : Int) * step) ∨
        (step < 0 ∧ first > first + ((count + 1 : Nat) : Int) * step)) = true := by
      simp only [decide_eq_true_eq]
      by_cases positiveStep : 0 < step
      · have increase := Int.mul_pos positiveCount positiveStep
        left; constructor <;> omega
      · have decrease := Int.mul_neg_of_pos_of_neg positiveCount (by omega : step < 0)
        right; constructor <;> omega
    have initialSegment := (Reaches.single (Step.stepped_sum_pc11 heap
        { v0 := first, v1 := first + ((count + 1 : Nat) : Int) * step, v2 := step } [])).trans
      ((Reaches.single (Step.stepped_sum_pc10 ..)).trans
        ((Reaches.single (Step.stepped_sum_pc9 ..)).trans
          ((Reaches.single (Step.stepped_sum_pc8 ..)).trans
            ((Reaches.single (Step.stepped_sum_pc7 _ _ _ nonzero)).trans
              ((Reaches.single (Step.stepped_sum_pc3_true _ _ _ condition)).trans
                (Reaches.single (Step.stepped_sum_pc6 ..)))))))
    have rest := stepped_remaining_summary count _ heap first
      (first + ((count + 1 : Nat) : Int) * step) step first 0 nonzero
      initialSegment True.intro rfl rfl rfl
    refine ⟨True.intro, ?_⟩
    intro stack
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc11 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc10 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc9 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc8 ..))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc7 _ _ _ nonzero))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc3_true _ _ _ condition))
    apply Reaches.trans (Reaches.single (Step.stepped_sum_pc6 ..))
    simpa using! rest stack

-- Main result: Correctness
/-- Ordinary-value consequence of the reusable stepped-range summary. -/
theorem stepped_output (first step : Int) (count : Nat) (nonzero : step ≠ 0) :
    stepped_sum.Returns (first, first + (count : Int) * step, step)
      (progressionSum first step count) := by
  have specification := stepped_summary {} first step count nonzero
  exact ⟨{}, specification.1, specification.2.root⟩

/-- A zero range step cannot complete, even when its bounds would be empty. -/
theorem zero_step_no_execution (heap final : Heap) (first stop output : Int) :
    ¬ stepped_sum.Run heap (first, stop, 0) final output := by
  rintro ⟨_, run⟩
  let invariant : Configuration → Prop
    | .active _ (.fn_stepped_sum pc s) _ =>
        ((pc = 11 ∨ pc = 10 ∨ pc = 9 ∨ pc = 8) ∧ s.v2 = 0) ∨
        (pc = 7 ∧ s.t8 = 0)
    | _ => False
  apply run.invariant invariant
  · simp [stepped_sum.initial, start, invariant]
  · intro before after transition hypothesis
    cases transition <;> simp_all [invariant]

/-- The invalid-step behavior is reusable in any calling context. -/
theorem zero_step_no_call (heap final : Heap) (first stop output : Int) :
    ¬ stepped_sum.Call heap (first, stop, 0) final output :=
  fun call => zero_step_no_execution heap final first stop output call.run

/-- The ordinary value view cannot produce an output for a zero step. -/
theorem zero_step_no_output (first stop output : Int) :
    ¬ stepped_sum.Returns (first, stop, 0) output := by
  rintro ⟨finalHeap, run⟩
  exact zero_step_no_execution _ finalHeap first stop output run

/-- Skipping an empty range preserves a previously bound loop variable. -/
theorem empty_range_summary (heap : Heap) :
    empty_range_preserves_binding.Call heap () heap 9 := by
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.trans (Reaches.single (Step.empty_range_preserves_binding_pc11 ..))
  apply Reaches.trans (Reaches.single (Step.empty_range_preserves_binding_pc10 ..))
  apply Reaches.trans (Reaches.single (Step.empty_range_preserves_binding_pc9 ..))
  apply Reaches.trans (Reaches.single (Step.empty_range_preserves_binding_pc8 ..))
  apply Reaches.trans (Reaches.single (Step.empty_range_preserves_binding_pc7 _ _ _ (by decide)))
  apply Reaches.trans (Reaches.single (Step.empty_range_preserves_binding_pc3_false _ _ _ (by decide)))
  apply Reaches.trans (Reaches.single (Step.empty_range_preserves_binding_pc2 ..))
  exact Reaches.single (Step.empty_range_preserves_binding_pc1 ..)

/-- The ordinary output view also sees the preserved binding. -/
theorem empty_range_output : empty_range_preserves_binding.Returns () 9 := by
  have specification := empty_range_summary {}
  exact ⟨{}, specification.1, specification.2.root⟩

end RangeSumAnalysis
