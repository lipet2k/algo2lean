import Algo.client.Probability
import Algo.sampler.Analysis
import Algo2LeanProbability.CallContext

/-!
The caller reuses the sampler's proved reward formula twice. The imported
sampler's transition rules are not inspected here; the only operational bridge
checks the generated caller's import wrapper and its return continuation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace ClientAnalysis
open Algo2LeanGenerated Algo.client Algo.client.Algo2LeanGenerated
open Algo2LeanCore Algo2LeanProbability
open scoped ENNReal

private def insideSampler : Frame → Bool
  | .import_0 _ _ _ => true
  | _ => false

/-- Reuse a completed sampler contract at either call site. The continuation
    may observe the sampled value and the actual returned heap together. -/
private theorem imported_bit (heap : Heap) (pc : Nat) (locals : Int → State_pair)
    (reward : Heap × (Int × Int) → ENNReal) :
    callExpected nextChoice pair.outcome
      (.active heap (.import_0 (Algo.sampler.entry_bit ()) []
        (fun result => match result with | .fn_bit value => .fn_pair pc (locals value))) []) reward =
      ∑ value ∈ Finset.Ico (0 : Int) 2,
        callExpected nextChoice pair.outcome
          (.active (heap.tick "draws") (.fn_pair pc (locals value)) []) reward *
          (2 : ENNReal)⁻¹ := by
  let resume : Algo.sampler.Algo2LeanGenerated.Result → Frame :=
    fun result => match result with | .fn_bit value => .fn_pair pc (locals value)
  let continuation : Heap × Int → ENNReal := fun result =>
    callExpected nextChoice pair.outcome (.active result.1 (.fn_pair pc (locals result.2)) []) reward
  have reuse := callExpected_import Algo.sampler.Algo2LeanGenerated.nextChoice nextChoice
    Algo.sampler.bit.outcome pair.outcome Frame.import_0 insideSampler resume []
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intro result; cases result; rfl)
    heap (Algo.sampler.entry_bit ()) reward continuation
    (by intro h result; cases result; rfl)
  apply reuse.trans
  have contract := SamplerAnalysis.bit_hasLaw heap continuation
  simp only [if_pos (show Algo.sampler.bit.ValidInput heap () from trivial)] at contract
  change callExpected Algo.sampler.Algo2LeanGenerated.nextChoice Algo.sampler.bit.outcome
    (.active heap (Algo.sampler.entry_bit ()) []) continuation =
    pmfExpected (SamplerAnalysis.bitLaw heap) continuation at contract
  rw [contract, SamplerAnalysis.bitLaw, pmfExpected_map, pmfExpected_uniformInt]
  norm_num [Int.toNat, continuation]

/-- The two calls are composed from the original sampler analysis. The joint
    result keeps the actual initial counters and all unrelated heap storage. -/
theorem pair_expected (heap : Heap) (reward : Heap → (Int × Int) → ENNReal) :
    pair.expectedReturn heap () reward =
      ∑ first ∈ Finset.Ico (0 : Int) 2,
        (∑ second ∈ Finset.Ico (0 : Int) 2,
          reward ((heap.tick "draws").tick "draws") (first, second) * (2 : ENNReal)⁻¹) *
          (2 : ENNReal)⁻¹ := by
  let payoff : Heap × (Int × Int) → ENNReal := fun result => reward result.1 result.2
  let firstLocals (value : Int) : State_pair := {t4 := value}
  simp only [pair.expectedReturn, if_pos (show pair.ValidInput heap () from trivial)]
  rw [callExpected_next nextChoice pair.outcome (pair.initial heap ())
    (.active heap (.import_0 (Algo.sampler.entry_bit ()) []
      (fun result => match result with | .fn_bit value => .fn_pair 5 (firstLocals value))) [])
    rfl rfl payoff]
  rw [imported_bit]
  apply Finset.sum_congr rfl
  intro first firstMember
  let middle := heap.tick "draws"
  let saved : State_pair := {v0 := first, t4 := first}
  let secondLocals (value : Int) : State_pair := {v0 := first, t3 := value, t4 := first}
  rw [callExpected_next nextChoice pair.outcome
    (.active middle (.fn_pair 5 (firstLocals first)) [])
    (.active middle (.fn_pair 4 saved) []) rfl rfl payoff]
  rw [callExpected_next nextChoice pair.outcome
    (.active middle (.fn_pair 4 saved) [])
    (.active middle (.import_0 (Algo.sampler.entry_bit ()) []
      (fun result => match result with | .fn_bit value => .fn_pair 3 (secondLocals value))) [])
    rfl rfl payoff]
  rw [imported_bit]
  congr 1
  apply Finset.sum_congr rfl
  intro second secondMember
  let final := middle.tick "draws"
  let finished : State_pair := {v0 := first, v1 := second, t3 := second, t4 := first}
  rw [callExpected_next nextChoice pair.outcome
    (.active final (.fn_pair 3 (secondLocals second)) [])
    (.active final (.fn_pair 2 finished) []) rfl rfl payoff]
  rw [callExpected_next nextChoice pair.outcome
    (.active final (.fn_pair 2 finished) [])
    (.active final (.fn_pair 1 {finished with t2 := (first, second)}) []) rfl rfl payoff]
  rw [callExpected_next nextChoice pair.outcome
    (.active final (.fn_pair 1 {finished with t2 := (first, second)}) [])
    (.done final (.fn_pair (first, second))) rfl rfl payoff]
  rw [callExpected_return nextChoice pair.outcome _ (final, (first, second)) rfl payoff]

def pairLaw (heap : Heap) : PMF (Heap × (Int × Int)) :=
  (SamplerAnalysis.bitLaw heap).bind (fun first =>
    (SamplerAnalysis.bitLaw first.1).map (fun second => (second.1, (first.2, second.2))))

/-- A client of the sampler exports another complete law for further callers. -/
theorem pair_hasLaw (heap : Heap) : pair.HasLaw heap () (pairLaw heap) := by
  intro payoff
  change pair.expectedReturn heap () (fun final value => payoff (final, value)) =
    pmfExpected (pairLaw heap) payoff
  rw [pair_expected]
  simp only [pairLaw, SamplerAnalysis.bitLaw, pmfExpected_bind, pmfExpected_map,
    pmfExpected_uniformInt]
  norm_num [Int.toNat]

/-- Every pair of binary outcomes has probability one quarter. -/
theorem pair_probability (heap : Heap) (first second : Int)
    (firstBit : first = 0 ∨ first = 1) (secondBit : second = 0 ∨ second = 1) :
    pair.returnProbability heap () (fun _ result => result = (first, second)) = 1 / 4 := by
  classical
  rw [pair.returnProbability_eq_expectedReturn heap () trivial, pair_expected]
  rcases firstBit with rfl | rfl <;> rcases secondBit with rfl | rfl <;>
    norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} from by decide] <;>
    rw [← ENNReal.mul_inv (a := 2) (b := 2) (Or.inl (by norm_num)) (Or.inr (by norm_num))] <;>
    norm_num

/-- Costs compose from the caller's actual initial counters, rather than from
    freshly reset heaps. Both calls together charge exactly two draws. -/
theorem pair_draws (heap : Heap) :
    pair.returnProbability heap () (fun final _ => Heap.cost heap final "draws" = 2) = 1 := by
  classical
  rw [pair.returnProbability_eq_expectedReturn heap () trivial, pair_expected]
  have cost : Heap.cost heap ((heap.tick "draws").tick "draws") "draws" = 2 := by
    simp only [Heap.cost, Heap.clocks_tick_same]
    omega
  simp only [cost, ↓reduceIte]
  norm_num [show Finset.Ico (0 : Int) 2 = {0, 1} from by decide, Heap.cost,
    Heap.clocks_tick_same, ENNReal.mul_inv_cancel]

end ClientAnalysis
