import Substitution
import RecursionTree
import StrassenTheorems

/-!
Worked uses of the general §4.3–4.4 methods. The Strassen theorems concern the
existing compiled program and all four of its measured work categories.
The balanced linear-work example is a numerical recurrence, not a new proof
of merge sort's source-level runtime.
-/
namespace Chapter4RecurrenceApplications

open Algo2LeanCore Algo2LeanGenerated
open Algo2LeanCore.MatrixHeap
open Chapter4Substitution Chapter4RecursionTree

/-- Sum exactly the four clocks already linked to Strassen's source execution. -/
def strassenWork (depth : Nat) : Nat :=
  MatrixStrassenExecution.costs depth "products" +
  MatrixStrassenExecution.costs depth "calls" +
  MatrixStrassenExecution.costs depth "linear_cells" +
  MatrixStrassenExecution.costs depth "copied_cells"

@[simp] theorem strassenWork_zero : strassenWork 0 = 2 := by decide

theorem strassenWork_step (depth : Nat) :
    strassenWork (depth+1) = 7*strassenWork depth + (30*4^depth+1) := by
  simp [strassenWork, MatrixStrassenExecution.costs, Chapter4Math.calls,
    Chapter4Math.strassenOverhead, Nat.pow_succ]
  omega

/-- The generic tree expansion counts leaves, copying, combinations and calls.
It applies to this program because its exact clock recurrence was proved above. -/
theorem strassen_tree_expansion (depth : Nat) :
    strassenWork depth = 7^depth*2 +
      weightedTolls 7 depth (fun k => 30*4^k+1) := by
  simpa using balanced_unroll 7 strassenWork (fun k => 30*4^k+1) strassenWork_step depth

/-- Strengthening the induction hypothesis absorbs the additive toll. A plain
    candidate C*7^k cannot close substitution while a positive toll remains. -/
def strengthenedWork (depth : Nat) : Nat := strassenWork depth + 10*4^depth+1

theorem strengthenedWork_step (depth : Nat) :
    strengthenedWork (depth+1) ≤ 7*strengthenedWork depth := by
  simp only [strengthenedWork, strassenWork_step, Nat.pow_succ]
  omega

/-- General upper/lower substitution supplies explicit constants for every
    depth. This improves the earlier valid upper constant 33 to 13. -/
theorem strassen_substitution_bounds (depth : Nat) :
    7^depth ≤ strassenWork depth ∧ strassenWork depth ≤ 13*7^depth := by
  have lower := depth_lower strassenWork (fun k => 7^k) 7 (fun k => 30*4^k+1)
    (by simp)
    (fun k => Nat.le_of_eq (strassenWork_step k).symm)
    (fun k => by simp [Nat.pow_succ]; omega) depth
  have upper := depth_upper strengthenedWork (fun k => 13*7^k) 7 (fun _ => 0)
    (by simp [strengthenedWork])
    (fun k => by simpa using strengthenedWork_step k)
    (fun k => by simp [Nat.pow_succ]; omega) depth
  exact ⟨lower, by simp only [strengthenedWork] at upper; omega⟩

/-- Natural-valued eventual Θ bound, with explicit witnesses available above. -/
theorem strassen_theta : IsTheta strassenWork (fun k => 7^k) := by
  constructor
  · exact ⟨13, 0, by decide, fun k _ => (strassen_substitution_bounds k).2⟩
  · exact ⟨1, 0, by decide, fun k _ => by simpa using (strassen_substitution_bounds k).1⟩

/-- The new substitution bound holds for every completed source execution. -/
theorem runtime_via_substitution (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (charged : Clocks)
    (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.ReturnsWithCost (initial,(a,b,(2^depth:Nat))) (after,result) charged) :
    7^depth ≤ charged "products" + charged "calls" +
      charged "linear_cells" + charged "copied_cells" ∧
    charged "products" + charged "calls" + charged "linear_cells" +
      charged "copied_cells" ≤ 13*7^depth := by
  rw [MatrixStrassenVerified.every_output_costs initial after a b result av bv depth charged sa sb run]
  exact strassen_substitution_bounds depth

/-- The exact recursion-tree sum describes those same source counters. -/
theorem runtime_via_tree (initial after : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (charged : Clocks)
    (sa : Stored initial a av) (sb : Stored initial b bv)
    (run : strassen.ReturnsWithCost (initial,(a,b,(2^depth:Nat))) (after,result) charged) :
    charged "products" + charged "calls" + charged "linear_cells" +
      charged "copied_cells" = 7^depth*2 +
        weightedTolls 7 depth (fun k => 30*4^k+1) := by
  rw [MatrixStrassenVerified.every_output_costs initial after a b result av bv depth charged sa sb run]
  exact strassen_tree_expansion depth

/-- Existence is explicit: the runtime claim is not vacuous for diverging runs. -/
theorem terminates_with_bounds (initial : Heap) (a b : CollectionRef)
    (av bv : Values) (depth : Nat) (sa : Stored initial a av) (sb : Stored initial b bv) :
    ∃ after result charged,
      strassen.ReturnsWithCost (initial,(a,b,(2^depth:Nat))) (after,result) charged ∧
      7^depth ≤ charged "products" + charged "calls" +
        charged "linear_cells" + charged "copied_cells" ∧
      charged "products" + charged "calls" + charged "linear_cells" +
        charged "copied_cells" ≤ 13*7^depth := by
  obtain ⟨after, result, run, _⟩ :=
    MatrixStrassenVerified.output_with_cost initial a b av bv depth sa sb
  exact ⟨after, result, _, run,
    runtime_via_substitution initial after a b result av bv depth _ sa sb run⟩

/-- The usual linear-work balanced recurrence, in depth coordinates n=2^k. -/
theorem balanced_linear_candidate_step (k : Nat) :
    2*((k+1)*2^k)+2^(k+1) = ((k+1)+1)*2^(k+1) := by
  simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul]
  ac_rfl

/-- The generic substitution principle proves the exact n*(log₂ n+1) formula
    on n=2^k, for every solution of this recurrence, not just a fixed definition. -/
theorem balanced_linear_exact (cost : Nat → Nat) (base : cost 0 = 1)
    (step : ∀ k, cost (k+1) = 2*cost k + 2^(k+1)) (depth : Nat) :
    cost depth = (depth+1)*2^depth := by
  apply Nat.le_antisymm
  · exact depth_upper cost (fun k => (k+1)*2^k) 2 (fun k => 2^(k+1))
      (by simp [base]) (fun k => Nat.le_of_eq (step k))
      (fun k => Nat.le_of_eq (balanced_linear_candidate_step k)) depth
  · exact depth_lower cost (fun k => (k+1)*2^k) 2 (fun k => 2^(k+1))
      (by simp [base]) (fun k => Nat.le_of_eq (step k).symm)
      (fun k => Nat.le_of_eq (balanced_linear_candidate_step k).symm) depth

/-- The same balanced recurrence is the exact sum of all internal levels and
    the leaf cost; this checks agreement between the two general methods. -/
theorem balanced_linear_tree (depth : Nat) :
    (balancedTree 2 1 (fun k => 2^(k+1)) depth).totalCost = (depth+1)*2^depth := by
  apply balanced_linear_exact (fun k => (balancedTree 2 1 (fun j => 2^(j+1)) k).totalCost)
    (depth := depth)
  · simp [balancedTree, Tree.totalCost]
  · intro k
    simp [balancedTree, Tree.totalCost, Nat.add_comm, Nat.two_mul]

end Chapter4RecurrenceApplications
