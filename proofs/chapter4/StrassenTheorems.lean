import Algo2LeanLib.CallCost
import StrassenExecution
import StrassenDeterminism

open Algo2LeanCore Algo2LeanGenerated
open Algo2LeanCore.MatrixHeap
open MatrixStrassenExecution
open StrassenValues (strassenValue strassen_entry strassen_outside)

namespace MatrixStrassenVerified

/-- A terminating compiled execution returns a genuine array of row arrays,
with the seven-product value and exactly the four specified counter increments.
Input matrices and their rows can share references. -/
theorem output_with_cost (initial : Heap) (a b : CollectionRef) (av bv : Values)
    (depth : Nat) (sa : Stored initial a av) (sb : Stored initial b bv) :
    ∃ after result, strassen.ReturnsWithCost (initial, a, b, (2^depth : Nat))
      (after, result) (costs depth) ∧ Stored after result (strassenValue depth av bv) := by
  obtain ⟨after, result, summary, _, value, clocks⟩ :=
    strassen_summary depth initial a b av bv sa sb
  refine ⟨after, result, ⟨summary.run, ?_⟩, value⟩
  funext name
  change after.clocks name - initial.clocks name = costs depth name
  rw [clocks name]
  omega

/-- Compare any completed execution with the independently constructed
terminating execution, including its complete heap and all named counters. -/
theorem execution_correct (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.Run initial (a, b, (2^depth : Nat)) after result) :
    Extends initial after ∧ Stored after result (strassenValue depth av bv) ∧
      Heap.cost initial after = costs depth ∧ initial.nextCollection ≤ result := by
  obtain ⟨correctHeap, correctRef, summary, frame, value, clocks, fresh⟩ :=
    strassen_summary_fresh depth initial a b av bv sa sb
  obtain ⟨rfl, rfl⟩ := MatrixStrassenDeterminism.executions_unique _ _ _ _ _ _ run summary.run
  refine ⟨frame, value, ?_, fresh⟩
  funext name
  change after.clocks name - initial.clocks name = costs depth name
  rw [clocks name]
  omega

/-- Every well-formed power-of-two square matrix multiplication terminates. -/
theorem terminates (initial : Heap) (a b : CollectionRef) (av bv : Values)
    (depth : Nat) (sa : Stored initial a av) (sb : Stored initial b bv) :
    ∃ after result, strassen.Returns (initial, a, b, (2^depth : Nat)) (after, result) := by
  obtain ⟨after, result, run, _⟩ := output_with_cost initial a b av bv depth sa sb
  exact ⟨after, result, run.returns⟩

-- Main result: Correctness
/-- Each returned cell is the usual finite row-by-column dot product. The
representation uses real nested row references, including shared input rows. -/
theorem every_output_entry (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth row column : Nat) (sa : Stored initial a av) (sb : Stored initial b bv)
    (validRow : row < 2^depth) (validColumn : column < 2^depth)
    (run : strassen.Returns (initial, a, b, (2^depth : Nat)) (after, result)) :
    cell after result row column =
      Chapter4Math.dot (2^depth) (fun inner => av row inner) (fun inner => bv inner column) := by
  have value := (execution_correct initial after a b result av bv depth sa sb run).2.1
  rw [value.cell]
  exact strassen_entry depth av bv row column validRow validColumn

/-- Entries outside the finite result square are zero in either coordinate. -/
theorem every_output_outside (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (row column : Int)
    (sa : Stored initial a av) (sb : Stored initial b bv)
    (outside : row < 0 ∨ ((2^depth:Nat):Int) ≤ row ∨ column < 0 ∨ ((2^depth:Nat):Int) ≤ column)
    (run : strassen.Returns (initial, a, b, (2^depth : Nat)) (after, result)) :
    cell after result row column = 0 := by
  have value := (execution_correct initial after a b result av bv depth sa sb run).2.1
  rw [value.cell]
  exact strassen_outside depth av bv row column outside

/-- All old integer rows, outer arrays, and objects are preserved, including
references shared within or between input matrices. -/
theorem every_execution_preserves (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.Run initial (a, b, (2^depth : Nat)) after result) : Extends initial after :=
  (execution_correct initial after a b result av bv depth sa sb run).1

/-- The returned outer array is freshly allocated and valid. -/
theorem every_execution_fresh (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.Run initial (a, b, (2^depth : Nat)) after result) :
    initial.nextCollection ≤ result ∧ result < after.nextCollection := by
  have correct := execution_correct initial after a b result av bv depth sa sb run
  exact ⟨correct.2.2.2, correct.2.1.1.1⟩

/-- Every finite output row is valid, freshly allocated, and distinct from the
other output rows, so later mutation of one row cannot change another. -/
theorem every_execution_fresh_rows (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.Run initial (a, b, (2^depth : Nat)) after result) :
    FreshRows initial after result (2^depth) := by
  obtain ⟨correctHeap, correctRef, summary, _, _, _, _, fresh⟩ :=
    strassen_summary_rows depth initial a b av bv sa sb
  obtain ⟨rfl, rfl⟩ := MatrixStrassenDeterminism.executions_unique _ _ _ _ _ _ run summary.run
  exact fresh

/-- The exact clock increments are linked to every completed execution. -/
theorem every_output_costs (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (charged : Clocks)
    (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.ReturnsWithCost (initial, a, b, (2^depth : Nat)) (after, result) charged) :
    charged = costs depth :=
  run.2.symm.trans (execution_correct initial after a b result av bv depth sa sb run.1).2.2.1

-- Main result: Running time
/-- For n = 2^depth, every execution charges exactly 7^depth leaf products and
    between 7^depth and 33·7^depth total units: Θ(n^(log₂ 7)) counted work.
    Units count leaf products, recursive calls, copied cells, and linear-combination
    cells. Array allocations, loop bookkeeping, and integer bit complexity are
    excluded. The separate recurrence analysis sharpens the upper constant to 13. -/
theorem runtime_bounds (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (charged : Clocks)
    (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.ReturnsWithCost (initial, a, b, (2^depth : Nat)) (after, result) charged) :
    charged "products" = 7^depth ∧
      7^depth ≤ charged "products" + charged "calls" +
        charged "linear_cells" + charged "copied_cells" ∧
      charged "products" + charged "calls" + charged "linear_cells" +
        charged "copied_cells" ≤ 33*7^depth := by
  rw [every_output_costs initial after a b result av bv depth charged sa sb run]
  have bound := Chapter4Math.strassen_total_theta 30 depth
  simp only [Chapter4Math.strassenCellWork] at bound
  simp [costs]
  omega


/-- All four source clocks: products, recursive calls, combinations and copies. -/
def runtime (charged : Clocks) : Nat :=
  charged "products" + charged "calls" + charged "linear_cells" + charged "copied_cells"

private theorem work_bounds (depth : Nat) :
    7^depth ≤ runtime (MatrixStrassenExecution.costs depth) ∧
    runtime (MatrixStrassenExecution.costs depth) ≤ 13*7^depth := by
  have overhead := Chapter4Math.strassenOverhead_exact depth
  have small : 3 * Chapter4Math.strassenOverhead depth ≤ 7^depth :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq overhead)
  have scaled := Nat.mul_le_mul_left 10 small
  have calls := Chapter4Math.calls7_bound depth
  simp only [runtime, MatrixStrassenExecution.costs]
  simp
  omega

-- Main result: Correctness and running time
/-- For n=2^depth, a finite Strassen call returns the ordinary matrix product,
preserves old storage, and returns a fresh outer array with distinct fresh rows.
The exact counter increments and both runtime bounds concern this same call.
The uniform upper constant may be chosen as 13; all input sharing is permitted. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          strassen.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
          Stored after result (strassenValue depth av bv) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result (2^depth) ∧
          heap.Increments after (MatrixStrassenExecution.costs depth) ∧
          7^depth ≤ runtime (heap.cost after) ∧ runtime (heap.cost after) ≤ C*7^depth := by
  refine ⟨13, by decide, ?_⟩
  intro heap a b av bv depth sa sb
  obtain ⟨after, result, call, frame, stored, increments, fresh, freshRows⟩ :=
    MatrixStrassenExecution.strassen_summary_rows depth heap a b av bv sa sb
  have charged : heap.Increments after (MatrixStrassenExecution.costs depth) := increments
  refine ⟨after, result, call, ?_, frame, fresh, stored.1.1, freshRows, charged, ?_⟩
  · exact stored
  · rw [charged.cost]
    exact work_bounds depth


/-- Reusable total call contract: product, preserved caller storage, a fresh
outer array with independent finite rows, and exact increments of every clock. -/
theorem call (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result,
      strassen.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
      Stored after result (strassenValue depth av bv) ∧ Extends heap after ∧
      heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
      FreshRows heap after result (2^depth) ∧ heap.Increments after (costs depth) := by
  obtain ⟨_, _, contract⟩ := correctness_and_running_time
  obtain ⟨after, result, execution, stored, frame, lower, upper, fresh, charged, _⟩ :=
    contract heap a b av bv depth sa sb
  exact ⟨after, result, execution, stored, frame, lower, upper, fresh, charged⟩

end MatrixStrassenVerified
