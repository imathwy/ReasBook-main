import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_41
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_43

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open scoped BigOperators
open scoped MatrixOrder
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Theorem 6.10 lies in the chapter's real-symmetric spectral-power-series / Hessian domain.

Sampled owner-style declarations:
- Chapter 6 `AnalyticSymmetricSpectralFunction` in `Definition_6_43`, the source-facing owner for
  analytic symmetric spectral functions with positive radius and coefficient sign condition
  `0 ≤ a_k` for `k ≥ 2`;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the chapter owner for the ordered eigenvalue
  vector of a real symmetric matrix on `𝕊^n`;
- mathlib `CFC.abs`, together with `CFC.abs_nonneg` and Hermitian eigenvalues, as the canonical
  absolute-value owner for real symmetric matrices;
- mathlib `iteratedFDeriv` and `iteratedDeriv`, the canonical Hessian quadratic-form owner and
  one-variable second-derivative owner for scalar-valued maps;
- `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing` in `Theorem_6_9`, the chapter
  trace-power Hessian estimate used termwise in the power-series proof route.

Best owner abstraction:
- source-facing: the Hessian quadratic-form inequality for the spectral sum
  `X ↦ ∑ i, f (λᵢ(X))` attached to an analytic symmetric spectral function `Φ`;
- core/canonical: `AnalyticSymmetricSpectralFunction`, `𝕊^n`, `eigenvalues`, `CFC.abs`,
  `iteratedFDeriv`, and `iteratedDeriv`;
- bridge/view: the power-series expansion into trace-power owners together with Theorem 6.9's
  termwise spectral bound.

Primitive data:
- an owner `Φ : AnalyticSymmetricSpectralFunction`, whose primitive fields are the coefficients,
  positive convergence radius, and the source-essential sign condition `0 ≤ coeff k` for `k ≥ 2`;
- a symmetric matrix `X : SymmMat` and a symmetric direction `H : SymmMat`;
- the spectral-domain hypothesis `hX : X ∈ Φ.dom`.

Derived API:
- the source-facing spectral owner `Φ.matrixFun`;
- the right-hand eigenvalue-square bound through the eigenvalues of `CFC.abs X` and
  `CFC.abs H`.

Source/core/bridge triage:
- source-facing: Theorem 6.10's Hessian bound for the spectral sum itself;
- core/canonical: the chapter `𝕊^n`, `eigenvalues`, and absolute-value owners together with
  `iteratedFDeriv`;
- bridge/view: the trace-power series decomposition used only in the proof strategy.

The previous version also dropped the source-essential coefficient sign condition in degrees
`k ≥ 2`, which makes the claimed inequality false already in the scalar case. This refinement
therefore moves the theorem to the existing owner `AnalyticSymmetricSpectralFunction`, whose
primitive data already includes that sign condition, and deletes the parallel raw coefficient /
radius interface.
-/

namespace AnalyticSymmetricSpectralFunction

-- Proof sketch: expand the spectral function induced by `Φ` as the convergent trace-power series
-- `∑ k, Φ.coeff k * π[k] X`, differentiate termwise on a neighborhood inside the spectral domain,
-- apply the Chapter 6 power-trace Hessian estimate term-by-term, use `Φ.coeff_nonneg` for
-- summability of the termwise bounds, and then resum to identify the coefficient sum with the
-- `iteratedDeriv 2 (FormalMultilinearSeries.ofScalarsSum Φ.coeff)` at the eigenvalues of
-- `CFC.abs X`.
/-- Theorem 6.10: if `Φ` is an analytic symmetric spectral function, then for every symmetric
matrix `X` in its spectral domain and every symmetric direction `H`, the Hessian quadratic form of
the induced spectral function `Φ.matrixFun`
is bounded above by
`∑ i, iteratedDeriv 2 (FormalMultilinearSeries.ofScalarsSum Φ.coeff) (λᵢ(CFC.abs X)) *
  (λᵢ(CFC.abs H))^2`. -/
theorem hessianQuadraticForm_le_absEigenvalueSquareSum
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) (H : SymmMat) :
    (iteratedFDeriv ℝ 2 Φ.matrixFun X) ![H, H] ≤
      ∑ i : Fin n,
        iteratedDeriv 2 (FormalMultilinearSeries.ofScalarsSum Φ.coeff)
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i)) *
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (2 : ℕ)) := sorry

end AnalyticSymmetricSpectralFunction
