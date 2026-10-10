import StrassenExecution
import StrassenDeterminism

open Algo2LeanCore Algo2LeanGenerated
open MatrixStrassenExecution MatrixStrassenAnalysis
open StrassenValues (strassenValue strassen_entry strassen_outside)

namespace MatrixStrassenVerified

/-- A terminating run of the compiled source returns the seven-product value
    and charges exactly the four specified counters. -/
theorem output_with_cost (a b : Seq) (depth : Nat) :
    strassen.ReturnsWithCost (a, b, (2^depth : Nat))
      (strassenValue depth a b) (costs depth) := by
  let initial := (({} : Heap).allocate a).allocate b
  have left : Stored initial 0 a := by
    refine ⟨by simp [initial], ?_⟩
    intro index
    simp [initial, Heap.read, Heap.allocate]
  have right : Stored initial 1 b := by
    refine ⟨by simp [initial], ?_⟩
    intro index
    simp [initial, Heap.read, Heap.allocate]
  obtain ⟨after, ref, summary, _, value, charged⟩ :=
    strassen_summary depth initial 0 1 a b left right
  refine ⟨after, ref, ⟨summary.1, summary.2.root⟩, funext value.read, ?_⟩
  funext name
  change after.clocks name - initial.clocks name = costs depth name
  rw [charged name]
  omega

/-- Correctness and costs describe every completed source execution. -/
theorem output_with_cost_iff (a b result : Seq) (depth : Nat) (charged : Clocks) :
    strassen.ReturnsWithCost (a, b, (2^depth : Nat)) result charged ↔
      result = strassenValue depth a b ∧ charged = costs depth :=
  MatrixStrassenDeterminism.output_with_cost_iff_of_run _ _ _
    (output_with_cost a b depth) result charged

/-- Every power-of-two square matrix multiplication terminates. -/
theorem terminates (a b : Seq) (depth : Nat) :
    ∃ result, strassen.Returns (a, b, (2^depth : Nat)) result :=
  ⟨strassenValue depth a b, (output_with_cost a b depth).returns⟩

-- Main result: Correctness
/-- Each returned cell is the ordinary finite row-column dot product. -/
theorem every_output_entry (a b result : Seq) (depth row column : Nat)
    (validRow : row < 2^depth) (validColumn : column < 2^depth)
    (run : strassen.Returns (a, b, (2^depth : Nat)) result) :
    result ((row*(2^depth)+column : Nat) : Int) =
      Chapter4Math.dot (2^depth)
        (fun inner => a ((row*(2^depth)+inner : Nat) : Int))
        (fun inner => b ((inner*(2^depth)+column : Nat) : Int)) := by
  obtain ⟨charged, completed⟩ := run.withCost
  obtain ⟨rfl, _⟩ := (output_with_cost_iff a b result depth charged).mp completed
  exact strassen_entry depth a b row column validRow validColumn

/-- The infinite output sequence is zero outside the finite matrix. -/
theorem every_output_outside (a b result : Seq) (depth : Nat) (index : Int)
    (outside : index < 0 ∨ ((2^depth * 2^depth : Nat) : Int) ≤ index)
    (run : strassen.Returns (a, b, (2^depth : Nat)) result) : result index = 0 := by
  obtain ⟨charged, completed⟩ := run.withCost
  obtain ⟨rfl, _⟩ := (output_with_cost_iff a b result depth charged).mp completed
  exact strassen_outside depth a b index outside

/-- Arbitrary-heap executions preserve every previously allocated sequence,
    including aliased inputs, at all integer indices. -/
theorem every_execution_preserves (initial after : Heap) (a b result : SeqRef)
    (depth : Nat)
    (run : strassen.Run initial (a, b, (2^depth : Nat)) after result) :
    Preserves initial after := by
  have left : Stored initial a (initial.read a) := ⟨run.1.1, fun _ => rfl⟩
  have right : Stored initial b (initial.read b) := ⟨run.1.2, fun _ => rfl⟩
  obtain ⟨correctHeap, correctRef, summary, frame, _, _⟩ :=
    strassen_summary depth initial a b (initial.read a) (initial.read b) left right
  obtain ⟨rfl, rfl⟩ := MatrixStrassenDeterminism.executions_unique _ _ _ _ _ _
    run ⟨summary.1, summary.2.root⟩
  exact frame

/-- Every completed execution returns a valid new reference, distinct from all
    sequence objects that were already allocated when the call began. -/
theorem every_execution_fresh (initial after : Heap) (a b result : SeqRef)
    (depth : Nat)
    (run : strassen.Run initial (a, b, (2^depth : Nat)) after result) :
    initial.nextRef ≤ result ∧ result < after.nextRef := by
  have left : Stored initial a (initial.read a) := ⟨run.1.1, fun _ => rfl⟩
  have right : Stored initial b (initial.read b) := ⟨run.1.2, fun _ => rfl⟩
  obtain ⟨correctHeap, correctRef, summary, _, stored, _, fresh⟩ :=
    strassen_summary_fresh depth initial a b (initial.read a) (initial.read b) left right
  obtain ⟨rfl, rfl⟩ := MatrixStrassenDeterminism.executions_unique _ _ _ _ _ _
    run ⟨summary.1, summary.2.root⟩
  exact ⟨fresh, stored.allocated⟩

-- Main result: Running time
/-- Exact leaf products and matching asymptotic bounds for total
    charged scalar, copy, linear-combination, and recursive-call work.
    With n=2^depth these are the discrete form of Θ(n^(log₂ 7)). -/
theorem runtime_bounds (a b result : Seq) (depth : Nat) (charged : Clocks)
    (run : strassen.ReturnsWithCost (a, b, (2^depth : Nat)) result charged) :
    charged "products" = 7^depth ∧
      7^depth ≤ charged "products" + charged "calls" +
        charged "linear_cells" + charged "copied_cells" ∧
      charged "products" + charged "calls" + charged "linear_cells" +
        charged "copied_cells" ≤ 33*7^depth := by
  obtain ⟨_, rfl⟩ := (output_with_cost_iff a b result depth charged).mp run
  have bound := Chapter4Math.strassen_total_theta 30 depth
  simp only [Chapter4Math.strassenCellWork] at bound
  simp [costs]
  omega

end MatrixStrassenVerified
