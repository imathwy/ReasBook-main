import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace
open scoped BigOperators Matrix.Norms.L2Operator RealSymmetricMatrixSpace

/- Proposition 6.35 lies in the chapter's symmetric-matrix spectral-smoothing / log-sum-exp
domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.eigenvalues`, the canonical real symmetric-matrix
  carrier and ordered eigenvalue owner;
- Chapter 5 `RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup`,
  `RealSymmetricMatrixSpace.symmetricMatrixNormedSpace`, and
  `RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace`, the inherited normed-space structure on
  `𝕊^n`;
- Chapter 5 `logSumExp`, the intrinsic finite-family log-sum-exp owner, specialized here to
  `EuclideanSpace ℝ (Fin n)`;
- mathlib's scoped `Matrix.Norms.L2Operator` norm, the canonical ambient matrix operator norm;
- mathlib `Matrix.IsHermitian.eigenvalues`, already packaged by the Chapter 5 owner `eigenvalues`.

Best owner abstraction:
- source-facing: the entropy smoothing on `𝕊^n` and the Hessian quadratic-form bound;
- core/canonical: `𝕊^n`, `RealSymmetricMatrixSpace.eigenvalues`, `logSumExp`, and the ambient
  matrix `L²` operator norm;
- bridge/view: the spectral-`∞` interpretation of that ambient operator norm for symmetric
  matrices, and the `n = 0` reduction of log-sum-exp to the empty sum.

Primitive data:
- `n : ℕ`
- `X : 𝕊^n`

Derived API:
- the entropy smoothing `X ↦ log (∑ i, exp (λᵢ(X)))`;
- Proposition 6.35's smoothness and Hessian bound.

Source/core/bridge triage:
- source-facing: `entropySmoothing` and the Hessian quadratic-form estimate;
- core/canonical: `𝕊^n`, `eigenvalues`, `logSumExp`, and the ambient matrix `L²` operator norm;
- bridge/view: the textbook spectral interpretation of that operator norm on symmetric matrices.

The previous version also rebuilt finite-dimensional `ℓ_p` and spectral-norm owners locally.
Those are already owned by the chapter's `EuclideanSpace` / `WithLp` norm layer and by the
canonical ambient matrix operator norm, so this file now keeps only the new Chapter 6
entropy-smoothing owner and uses the established norm surfaces directly.
-/

variable {n : ℕ}

/-- The entropy-smoothing spectral function `E(X) = log (∑ᵢ exp (λᵢ(X)))` on `𝕊^n`. -/
def entropySmoothing (X : 𝕊^n) : ℝ :=
  logSumExp (WithLp.toLp 2 (eigenvalues X))

/-- Evaluating `entropySmoothing` at `X` gives `log (∑ᵢ exp (λᵢ(X)))`. -/
theorem entropySmoothing_apply (X : 𝕊^n) :
    entropySmoothing X =
      Real.log (∑ i : Fin n, Real.exp (eigenvalues X i)) := by
  rw [entropySmoothing, logSumExp_apply]

-- Proof sketch: regard `entropySmoothing` as the spectral function attached to the scalar
-- log-sum-exp map on `ℝⁿ`; smoothness follows from smooth spectral calculus, and the Hessian bound
-- is obtained by diagonalizing `X`, reducing to the scalar Hessian
-- `Diag(p) - p pᵀ`, and comparing the spectral Hessian with commuting directions.
/-- Proposition 6.35: the entropy-smoothing function
`E(X) = log (∑ᵢ exp (λᵢ(X)))` on `𝕊^n` is twice Fréchet differentiable, and its Hessian quadratic
form in any symmetric direction `H` is bounded above by the square of the ambient matrix `L²`
operator norm, i.e. by the square of the spectral norm of `H`. -/
theorem entropySmoothing_contDiff_and_hessianQuadraticForm_le (n : ℕ) :
    ContDiff ℝ 2 (entropySmoothing : 𝕊^n → ℝ) ∧
      ∀ X H : 𝕊^n,
        (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X) ![H, H] ≤
          (‖((H : Matrix (Fin n) (Fin n) ℝ))‖) ^ (2 : ℕ) := sorry

end
