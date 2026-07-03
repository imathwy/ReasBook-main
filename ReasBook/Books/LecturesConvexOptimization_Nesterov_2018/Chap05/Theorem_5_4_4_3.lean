import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealSymmetricMatrixSpace

-- Proof sketch: for `X ∈ int(𝕊ⁿ₊)` and a symmetric direction `Δ`, conjugate by `X^(-1 / 2)` to
-- reduce the first three directional derivatives of `X ↦ -log det X` to sums of eigenvalue
-- powers of `Q = X^(-1 / 2) Δ X^(-1 / 2)`. Then the barrier-parameter bound with `ν = n`
-- follows from Cauchy--Schwarz, and the self-concordance inequality follows from the estimate
-- `|∑ λᵢ^3| ≤ (∑ λᵢ^2)^(3 / 2)`.
/-- Theorem 5.4.4.3: the log-determinant function `X ↦ -log det X` is an `n`-self-concordant
barrier on the interior of the positive-semidefinite cone `𝕊ⁿ₊`. -/
theorem negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone
    (n : ℕ) :
    IsSelfConcordantBarrierOnWith
      (𝕊^n₊₊ : Set (𝕊^n))
      n
      (logDetBarrierAmbient n) := by
  sorry

end
