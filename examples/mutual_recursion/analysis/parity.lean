import Algo.even.Generated
import Algo.odd.Generated
import Algo.even.Facts
import Algo.odd.Facts

open Algo2LeanCore _root_.Algo2LeanGenerated Algo.even Algo.odd

namespace ParityAnalysis

/-- Evenness alternates at each successor, starting with zero. -/
def evenValue : Nat → Bool
  | 0 => true
  | n + 1 => !(evenValue n)

/-- Either zero case charges two units and returns its own parity constant. -/
theorem base_calls (heap : Heap) :
    is_even.Call heap 0 (heap.tick "work" 2) true ∧
    is_odd.Call heap 0 (heap.tick "work" 2) false := by
  open Algo._a2l_groups.G8f88a4c57ddb2cd9.Algo2LeanGenerated in
    constructor
    · refine ⟨trivial, ?_⟩
      intro stack
      apply Reaches.prepend (Step._a2l_group_0_is_even_pc8 ..)
      apply Reaches.prepend (Step._a2l_group_0_is_even_pc7 ..)
      apply Reaches.prepend (Step._a2l_group_0_is_even_pc6_true _ _ _ (by simp))
      apply Reaches.prepend (Step._a2l_group_0_is_even_pc5 ..)
      exact Reaches.single (Step._a2l_group_0_is_even_pc4 ..)
    · refine ⟨trivial, ?_⟩
      intro stack
      apply Reaches.prepend (Step._a2l_group_1_is_odd_pc8 ..)
      apply Reaches.prepend (Step._a2l_group_1_is_odd_pc7 ..)
      apply Reaches.prepend (Step._a2l_group_1_is_odd_pc6_true _ _ _ (by simp))
      apply Reaches.prepend (Step._a2l_group_1_is_odd_pc5 ..)
      exact Reaches.single (Step._a2l_group_1_is_odd_pc4 ..)

/-- A positive evenness call delegates to the oddness contract at one less. -/
theorem even_successor (heap final : Heap) (n : Nat) (value : Bool)
    (recursive : is_odd.Call (heap.tick "work" 2) (n : Int) final value) :
    is_even.Call heap ((n + 1 : Nat) : Int) final value := by
  open Algo._a2l_groups.G8f88a4c57ddb2cd9.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro stack
    apply Reaches.prepend (Step._a2l_group_0_is_even_pc8 ..)
    apply Reaches.prepend (Step._a2l_group_0_is_even_pc7 ..)
    apply Reaches.prepend (Step._a2l_group_0_is_even_pc6_false _ _ _ (by simp))
    apply Reaches.prepend (Step._a2l_group_0_is_even_pc3 ..)
    apply Reaches.prepend (Step._a2l_group_0_is_even_pc2 ..)
    have previous : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
    simp only [previous]
    apply (recursive.2 _).trans
    exact Reaches.single (Step._a2l_group_0_is_even_pc1 ..)

/-- A positive oddness call delegates to the evenness contract at one less. -/
theorem odd_successor (heap final : Heap) (n : Nat) (value : Bool)
    (recursive : is_even.Call (heap.tick "work" 2) (n : Int) final value) :
    is_odd.Call heap ((n + 1 : Nat) : Int) final value := by
  open Algo._a2l_groups.G8f88a4c57ddb2cd9.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro stack
    apply Reaches.prepend (Step._a2l_group_1_is_odd_pc8 ..)
    apply Reaches.prepend (Step._a2l_group_1_is_odd_pc7 ..)
    apply Reaches.prepend (Step._a2l_group_1_is_odd_pc6_false _ _ _ (by simp))
    apply Reaches.prepend (Step._a2l_group_1_is_odd_pc3 ..)
    apply Reaches.prepend (Step._a2l_group_1_is_odd_pc2 ..)
    have previous : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
    simp only [previous]
    apply (recursive.2 _).trans
    exact Reaches.single (Step._a2l_group_1_is_odd_pc1 ..)

/-- Simultaneous induction establishes reusable value and exact cost contracts
    on an arbitrary initial heap, including existing objects and counters. -/
theorem calls (heap : Heap) (n : Nat) :
    is_even.Call heap (n : Int) (heap.tick "work" (2 * (n + 1))) (evenValue n) ∧
    is_odd.Call heap (n : Int) (heap.tick "work" (2 * (n + 1))) (!(evenValue n)) := by
  induction n generalizing heap with
  | zero => exact base_calls heap
  | succ n previous =>
    obtain ⟨evenCall, oddCall⟩ := previous (heap.tick "work" 2)
    have charge : 2 + 2 * (n + 1) = 2 * (n + 1 + 1) := by omega
    constructor
    · simpa only [Heap.tick_add, charge, evenValue] using even_successor heap _ n _ oddCall
    · simpa only [Heap.tick_add, charge, evenValue, Bool.not_not] using
        odd_successor heap _ n _ evenCall

-- Main result: Correctness
/-- Every completed evenness run returns the parity value and has the exact
    heap effect established by the reusable call theorem. -/
theorem correct (heap final : Heap) (n : Nat) (output : Bool)
    (execution : is_even.Run heap (n : Int) final output) :
    final = heap.tick "work" (2 * (n + 1)) ∧ output = evenValue n :=
  is_even.Run.eq_of_call execution (calls heap n).1

-- Main result: Running time
/-- The evenness function returns the parity value with exactly two units per
    recursive invocation; no other clock is charged. -/
theorem output_cost (n : Nat) :
    is_even.ReturnsWithCost (n : Int) (evenValue n)
      (Clocks.single "work" (2 * (n + 1))) := by
  refine ⟨({} : Heap).tick "work" (2 * (n + 1)), (calls {} n).1.run, ?_⟩
  change Heap.cost ({} : Heap) (({} : Heap).tick "work" (2 * (n + 1))) = _
  rw [← Heap.charge_single, Heap.cost_charge]

end ParityAnalysis
