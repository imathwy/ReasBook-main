import Nesterov.Chap04.Definition_4_1_6
import Nesterov.Chap05.Definition_5_4_4_2
import Nesterov.Chap06.Definition_6_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open NormedSpace
open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

/- Proposition 6.36 lies in Chapter 6's symmetric-matrix spectral smoothing domain.

Sampled owner-style declarations:
- `𝕊^n`, `RealSymmetricMatrixSpace.isHermitian`, and `RealSymmetricMatrixSpace.eigenvalues` in
  `Chap05/Definition_5_4_4_1` and `Chap05/Definition_5_4_4_2`, the chapter owners for real
  symmetric matrices and their intrinsic spectral data;
- `Matrix.leastEigenvalue` and the notation `λ_min(H)` in `Chap04/Definition_4_1_6`, showing the
  project style for extremal spectral scalars: the ambient-spectrum owner is primitive, and any
  coordinate/eigenvalue-list formula is a bridge theorem;
- `Matrix.greatestEigenvalue` and the notation `λ_max(H)` in `Chap04/Definition_4_1_6`, the
  project owner for largest real spectral values;
- `entropySmoothing` in `Chap06/Proposition_6_35`, the unscaled spectral log-sum-exp owner;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, the positive-parameter owner
  for the smoothed maximal eigenvalue on `𝕊^n`;
- mathlib `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`,
  `Matrix.IsSymm.exp`, and `Matrix.IsHermitian.trace_eq_sum_eigenvalues`, the canonical ambient
  spectral and exponential bridges.

Best owner abstraction:
- source-facing: Proposition 6.36's approximation and derivative formulas for the smoothed maximal
  eigenvalue;
- core/canonical: `𝕊^n`, `λ_max((X : Matrix (Fin n) (Fin n) ℝ))`, and
  `logSumExpMaxEigenvalueSmoothing`;
- bridge/view: the top-ordered-eigenvalue formula for `0 < n`, the matrix-exponential trace
  formula, and the normalized exponential matrix realizing the derivative.

Primitive data:
- `n : ℕ`;
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- a symmetric matrix `X : 𝕊^n`.

Derived API:
- the intrinsic maximal-eigenvalue owner `λ_max((X : Matrix (Fin n) (Fin n) ℝ))`;
- the bridge
  `λ_max((X : Matrix (Fin n) (Fin n) ℝ)) = eigenvalues X ⟨0, hn⟩` for `n > 0`;
- `RealSymmetricMatrixSpace.exponentialGradient`;
- the trace-form bridge for `logSumExpMaxEigenvalueSmoothing`;
- Proposition 6.36's approximation and differentiability statements.

This refinement removes the local ambient-matrix wrappers
`realSymmetricMatrix_isHermitian`, `symmetricMatrixEigenvalues`,
`symmetricMatrixMaxEigenvalue`, and `matrixExponentialSmoothing`, rewrites the file onto the
existing symmetric-matrix owner surface used elsewhere in the chapter, and keeps the ordered
eigenvalue formula only as a bridge from the intrinsic `λ_max` owner.
-/

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

namespace RealSymmetricMatrixSpace

/-- For `0 < n`, the supremum of the real spectrum of a symmetric matrix is its top ordered
eigenvalue. -/
theorem greatestEigenvalue_eq_eigenvalues_zero
    (hn : 0 < n) (X : SymmMat) :
    λ_max((X : Mat)) = eigenvalues X ⟨0, hn⟩ := sorry

/-- The normalized matrix exponential appearing in the derivative formula for the smoothed maximal
eigenvalue, packaged directly in the symmetric-matrix owner `𝕊^n`. -/
def exponentialGradient
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) : 𝕊^n :=
  ⟨(Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ))))⁻¹ •
      exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ)), by
    have h_scaled : (((μ : ℝ)⁻¹) • (X : Matrix (Fin n) (Fin n) ℝ)).IsSymm :=
      (isSymm X).smul ((μ : ℝ)⁻¹)
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simpa using
      (h_scaled.exp.smul
        ((Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ))))⁻¹))⟩

/-- Expanding `exponentialGradient μ X` gives the normalized exponential matrix
`Trace (exp (X / μ))⁻¹ exp (X / μ)`. -/
@[simp] theorem coe_exponentialGradient
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    ((exponentialGradient μ X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ))))⁻¹ •
        exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ)) :=
  rfl

end RealSymmetricMatrixSpace

open RealSymmetricMatrixSpace

-- Proof sketch: diagonalize `X`, use the spectral mapping theorem for the matrix exponential, and
-- rewrite the trace of `exp (X / μ)` as the sum of the exponentials of the ordered eigenvalues.
/-- Proposition 6.36 bridge: the Chapter 6 smoothing owner agrees with the textbook
matrix-exponential trace formula
`μ log (Trace (exp (X / μ)))`. -/
theorem logSumExpMaxEigenvalueSmoothing_eq_matrixExponentialTrace
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    logSumExpMaxEigenvalueSmoothing μ X =
      (μ : ℝ) * Real.log
        (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ)))) := sorry

-- Proof sketch: compare the finite sum `∑ i, exp (λᵢ(X) / μ)` with its largest summand and with
-- `n` times that largest summand, then identify that largest ordered eigenvalue with the
-- supremum of the real spectrum.
/-- Proposition 6.36 (1): for a positive smoothing parameter `μ`, the smoothed maximal eigenvalue
approximates the maximal eigenvalue of `X`, expressed intrinsically as the supremum of the real
spectrum, within the additive error `μ log n`. -/
theorem greatestEigenvalue_le_logSumExpMaxEigenvalueSmoothing_le
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    λ_max((X : Mat)) ≤ logSumExpMaxEigenvalueSmoothing μ X ∧
      logSumExpMaxEigenvalueSmoothing μ X ≤
        λ_max((X : Mat)) + (μ : ℝ) * Real.log (n : ℝ) := sorry

-- Proof sketch: differentiate the trace-form expression
-- `μ log (Trace (exp (X / μ)))`, use cyclicity of the trace to rewrite the Fréchet derivative as
-- the Frobenius pairing with the normalized exponential, and keep the derivative on the intrinsic
-- carrier `𝕊^n` so no separate symmetry side condition is needed.
/-- Proposition 6.36 (2): for `μ > 0`, the smoothed maximal eigenvalue is differentiable on
`𝕊^n`, and its Fréchet derivative in direction `H` is the Frobenius pairing with the normalized
matrix exponential. -/
theorem differentiableAt_logSumExpMaxEigenvalueSmoothing_and_fderiv_eq_frobeniusInner
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    DifferentiableAt ℝ (logSumExpMaxEigenvalueSmoothing μ) X ∧
      ∀ H : SymmMat,
        fderiv ℝ (logSumExpMaxEigenvalueSmoothing μ) X H =
          ⟪exponentialGradient μ X, H⟫_F := sorry

/-- Proposition 6.36 (2), ambient bridge: expanding the Chapter 5 Frobenius pairing in the
derivative formula recovers the textbook trace pairing with the normalized matrix exponential. -/
theorem differentiableAt_logSumExpMaxEigenvalueSmoothing_and_fderiv_eq_trace
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    DifferentiableAt ℝ (logSumExpMaxEigenvalueSmoothing μ) X ∧
      ∀ H : SymmMat,
        fderiv ℝ (logSumExpMaxEigenvalueSmoothing μ) X H =
          Matrix.trace ((H : Mat) * (exponentialGradient μ X : Mat)) := by
  refine ⟨
    (differentiableAt_logSumExpMaxEigenvalueSmoothing_and_fderiv_eq_frobeniusInner μ X).1,
    ?_⟩
  intro H
  rw [(differentiableAt_logSumExpMaxEigenvalueSmoothing_and_fderiv_eq_frobeniusInner μ X).2 H]
  change Matrix.trace ((H : Mat) * ((exponentialGradient μ X : Mat)ᵀ)) =
    Matrix.trace ((H : Mat) * (exponentialGradient μ X : Mat))
  rw [(RealSymmetricMatrixSpace.isSymm (exponentialGradient μ X)).eq]

end
