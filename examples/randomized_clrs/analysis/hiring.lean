import Algo.hiring_contract.Analysis
import Algo.hiring_costs.Analysis

/-!
Randomized hiring reuses the imported Fisher–Yates shuffle and the deterministic
record-count scan. The detailed contracts are in the imported analysis; these
main results give the user-facing correctness and expected hiring guarantee.
-/

noncomputable section
namespace HiringAnalysis
open Algo2LeanGenerated Algo.hiring
open scoped ENNReal

-- Main result: Correctness
/-- The returned number counts strict records in a uniformly shuffled candidate
order; the underlying sequence is a permutation of the original input. -/
theorem correctness (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef) :
    randomized_hire_assistant.returnProbability heap (ref, n)
      (fun final result => ShuffleAnalysis.Rearranges heap final ref 0 n ∧
        result = (recordCount (final.read ref) n : Int)) = 1 :=
  randomized_correctness heap ref n valid

-- Main result: Running time
/-- The full execution performs exactly n interviews on average, and only H_n
hires on average for distinct candidate scores. Both are total path costs. -/
theorem running_time (heap : Heap) (ref : SeqRef) (n : Nat)
    (valid : ref < heap.nextRef)
    (distinct : Function.Injective (fun i : Fin n => heap.read ref i.val)) :
    randomized_hire_assistant.expectedCost heap (ref, n) "interviews" = (n : ℝ≥0∞) ∧
    randomized_hire_assistant.expectedCost heap (ref, n) "hires" = HiringRecords.harmonic n :=
  ⟨expected_interview_cost heap ref n valid, expected_hire_cost heap ref n valid distinct⟩

end HiringAnalysis
