import Algo.sampler.Probability

/-! A sampler's joint heap/output contract, proved independently of callers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SamplerAnalysis
open Algo2LeanGenerated Algo.sampler Algo.sampler.Algo2LeanGenerated
open Algo2LeanProbability
open scoped ENNReal

/-- A uniform bit charges exactly one draw while retaining all caller storage. -/
theorem bit_expected (heap : Heap) (reward : Heap → Int → ENNReal) :
    bit.expectedReturn heap () reward =
      ∑ value ∈ Finset.Ico (0 : Int) 2,
        reward (heap.tick "draws") value * (2 : ENNReal)⁻¹ := by
  let charged := heap.tick "draws"
  let payoff : Heap × Int → ENNReal := fun result => reward result.1 result.2
  let first : Configuration := .active charged (.fn_bit 4 {}) []
  let second : Configuration := .active charged (.fn_bit 3 {}) []
  let ready : Configuration := .active charged (.fn_bit 2 {t2 := 2}) []
  let resume (value : Int) : Configuration :=
    .active charged (.fn_bit 1 {t0 := value, t2 := 2}) []
  simp only [bit.expectedReturn, if_pos (show bit.ValidInput heap () from trivial)]
  rw [callExpected_next nextChoice bit.outcome (bit.initial heap ()) first rfl rfl payoff]
  rw [callExpected_next nextChoice bit.outcome first second rfl rfl payoff]
  rw [callExpected_next nextChoice bit.outcome second ready rfl rfl payoff]
  rw [callExpected_uniform nextChoice bit.outcome ready 0 2 resume rfl rfl (by omega) payoff]
  apply Finset.sum_congr rfl
  intro value member
  rw [callExpected_next nextChoice bit.outcome (resume value)
    (.done charged (.fn_bit value)) rfl rfl payoff]
  rw [callExpected_return nextChoice bit.outcome _ (charged, value) rfl payoff]
  rfl

/-- The sampler's complete reusable distribution retains heap and clock state. -/
def bitLaw (heap : Heap) : PMF (Heap × Int) :=
  (uniformInt 0 2 (by omega)).map (fun value => (heap.tick "draws", value))

theorem bit_hasLaw (heap : Heap) : bit.HasLaw heap () (bitLaw heap) := by
  intro payoff
  change bit.expectedReturn heap () (fun final value => payoff (final, value)) =
    pmfExpected (bitLaw heap) payoff
  rw [bit_expected, bitLaw, pmfExpected_map, pmfExpected_uniformInt]
  norm_num [Int.toNat]

end SamplerAnalysis
