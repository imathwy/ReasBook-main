import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_10
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace StrictPositiveSemidefiniteCone
open scoped Matrix.Norms.Frobenius MatrixOrder RealSymmetricMatrixSpace

/- Lemma 5.4.4.1 lies in the strict positive-definite symmetric-matrix / log-determinant-barrier
domain.

Sampled owner-style declarations:
* `logDetBarrier` and `logDetBarrierAmbient` from `Definition_5_4_4_5`, the source-facing barrier
  and its ambient formula bridge;
* `logDetBarrier_eq_neg_sum_log_eigenvalues` from `Theorem_5_4_4_2`, which already states Chapter 5
  barrier facts on the intrinsic domain `𝕊^n₊₊`;
* `RealSymmetricMatrixSpace.frobeniusInner` from `Definition_5_4_4_2`, the symmetric-space owner
  for the Frobenius pairing on `𝕊^n`, together with the intrinsic bridges `sandwich` and `cube`;
* `StrictPositiveSemidefiniteCone.inv` and `StrictPositiveSemidefiniteCone.sqrtInv` from
  `Definition_5_4_4_5`, the strict-cone bridges returning `X⁻¹` and `X^{-1/2}` to `𝕊^n`;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` from
  `Theorem_5_4_4_3`, which differentiates the ambient extension on the symmetric ambient space.

Source/core/bridge triage:
* source-facing: the barrier `logDetBarrier n : 𝕊^n₊₊ → ℝ` together with the Chapter 5
  directional-derivative owners `lineDeriv`, `secondDirectionalDerivative`, and
  `thirdDirectionalDerivative` for its symmetric-space extension;
* core/canonical: differentiation of the symmetric-space extension `logDetBarrierAmbient n`;
* bridge/view: the ambient trace formula `Matrix.trace (Aᵀ * B)`.

Primitive data:
* `n : ℕ`.

Derived API:
* the Chapter 5 Frobenius owner `RealSymmetricMatrixSpace.frobeniusInner`;
* convexity and `C³` regularity from the upstream barrier owner
  `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone`;
* the directional-derivative formulas stated with the Chapter 5 owners
  `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`.

This refinement removes the duplicate root-level Frobenius owner and keeps the public derivative
surface on the Chapter 5 directional owners rather than on raw `fderiv` / `iteratedFDeriv`.
The public statements are source-facing in the point `X : 𝕊^n₊₊` and direction `Δ : 𝕊^n`, using
the chapter owner `⟪·, ·⟫_F` on symmetric matrices and ambient trace formulas only as local bridge
syntax where the derivative formulas naturally live in the matrix algebra.
-/

section

variable (n : ℕ)

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n
local notation "logDetBarrierAmbientSymm" => logDetBarrierAmbient n

/-- Lemma 5.4.4.1 (1): at a strict-cone point, the first directional derivative of the
log-determinant barrier in a symmetric direction is the Frobenius pairing with `-X⁻¹`. -/
theorem logDetBarrier_lineDeriv_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    lineDeriv ℝ logDetBarrierAmbientSymm X Δ =
      ⟪-inv X, Δ⟫_F := sorry

/-- Lemma 5.4.4.1 (2): the second directional derivative is the Frobenius self-pairing of
`√(X⁻¹) Δ √(X⁻¹)`. -/
theorem logDetBarrier_secondDirectional_eq_frobeniusNormSq
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      ⟪sandwich (sqrtInv X) Δ, sandwich (sqrtInv X) Δ⟫_F :=
  sorry

/-- Lemma 5.4.4.1 (3): the second directional derivative is the Frobenius pairing of `X⁻¹ Δ X⁻¹`
with `Δ`. -/
theorem logDetBarrier_secondDirectional_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      ⟪sandwich (inv X) Δ, Δ⟫_F :=
  sorry

/-- Lemma 5.4.4.1 (4): the second directional derivative is the trace of
`(√(X⁻¹) Δ √(X⁻¹))²`. -/
theorem logDetBarrier_secondDirectional_eq_trace_sq
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      Matrix.trace (((sandwich (sqrtInv X) Δ : Mat) ^ (2 : ℕ))) := sorry

/-- Lemma 5.4.4.1 (5): the third directional derivative is `-2` times the Frobenius pairing of the
identity with `(√(X⁻¹) Δ √(X⁻¹))³`. -/
theorem logDetBarrier_thirdDirectional_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    thirdDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      -2 *
        ⟪(1 : SymmMat), cube (sandwich (sqrtInv X) Δ)⟫_F :=
      sorry

/-- Lemma 5.4.4.1 (6): the third directional derivative is `-2` times the trace of
`(√(X⁻¹) Δ √(X⁻¹))³`. -/
theorem logDetBarrier_thirdDirectional_eq_trace_cube
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    thirdDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      -2 * Matrix.trace (cube (sandwich (sqrtInv X) Δ) : Mat) := sorry

end

end
