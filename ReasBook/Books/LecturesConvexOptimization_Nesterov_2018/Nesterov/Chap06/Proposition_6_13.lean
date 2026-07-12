import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_6

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

open scoped Matrix.Norms.L2Operator

/- Proposition 6.13 lies in the Euclidean matrix operator-norm / Gram-spectrum domain.

Primary domain:
- real matrices equipped with the Euclidean induced operator norm.

Sampled owner-style declarations:
- `Matrix.greatestEigenvalue` and the notation `λ_max(H)` in `Chap04/Definition_4_1_6`, the
  project owner for the largest real spectral value;
- mathlib's scoped `Matrix.Norms.L2Operator` norm `‖A‖`, the canonical Euclidean operator norm on
  matrices;
- the Gram matrix expression `Aᵀ * A`, whose largest eigenvalue controls the Euclidean operator
  norm.

Best owner abstraction:
- source-facing: the Euclidean operator norm of a real matrix;
- core/canonical: the ambient `Matrix.Norms.L2Operator` norm together with `λ_max`;
- bridge/view: the equivalent `sSup (spectrum ℝ (Aᵀ * A))` formulation used downstream.
-/

-- Proof sketch: square the Euclidean operator norm, rewrite `‖A x‖^2` as the Rayleigh quotient
-- `xᵀ (Aᵀ * A) x`, identify its maximum over the unit sphere with `λ_max(Aᵀ * A)`, and then take
-- square roots.
/-- Proposition 6.13: for a real matrix `A`, the operator norm induced by the Euclidean norms on
`ℝ^n` and `ℝ^m` is the square root of the largest eigenvalue of the Gram matrix `Aᵀ * A`. -/
theorem l2OperatorNorm_eq_sqrt_greatestEigenvalue_transpose_mul_self
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Real.sqrt (λ_max((Aᵀ * A : Matrix (Fin n) (Fin n) ℝ))) := sorry

-- Proof sketch: unfold `λ_max` in the main theorem as the supremum of the real spectrum of the
-- Gram matrix `Aᵀ * A`.
/-- Rewriting the Euclidean operator norm formula through the definition
`λ_max(H) = sSup (spectrum ℝ H)` recovers the spectrum-supremum form used elsewhere in the
chapter. -/
theorem l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Real.sqrt (sSup (spectrum ℝ (Aᵀ * A))) := sorry

end
