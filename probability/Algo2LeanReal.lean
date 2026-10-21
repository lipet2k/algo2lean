import Mathlib.Data.Real.Basic
import Algo2LeanLib.Tuple

/-!
# Exact real values

Algorithms using `Real` import this optional library. The deterministic runtime
and integer-only algorithms remain independent of Mathlib and probability.
-/

namespace Algo2LeanGenerated.ValueCodec

/-- Exact real values use the same heap as integer-only modules. Actual Lean type
    equality protects the scalar decoder independently of collection headers. -/
noncomputable def real : ValueCodec ℝ := scalar ℝ

end Algo2LeanGenerated.ValueCodec
