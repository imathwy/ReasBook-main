import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_41
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open scoped BigOperators MatrixOrder RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Theorem 6.9 lies in the chapter's symmetric-matrix trace-power / Hessian spectral domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the source-facing trace-power
  owner on `𝕊^n`;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the chapter's intrinsic ordered eigenvalue
  owner on `𝕊^n`;
- mathlib `CFC.abs`, together with `CFC.abs_nonneg` and Hermitian eigenvalues, as the canonical
  absolute-value owner for real symmetric matrices;
- mathlib `iteratedFDeriv`, the canonical Hessian quadratic-form owner for scalar-valued maps.

Best owner abstraction:
- source-facing: the Hessian quadratic-form bound for the Chapter 6 owner `π_k(X) = Trace (X^k)`
  on `𝕊^n`, together with the intrinsic spectral data coming from the matrix absolute values
  `CFC.abs X` and `CFC.abs H`;
- core/canonical: `π[k] : 𝕊^n → ℝ`, `iteratedFDeriv ℝ 2`, `eigenvalues`, and `CFC.abs`;
- bridge/view: Proposition 6.33's second-derivative expansion and the spectral inequality from
  Lemma 6.14.

Primitive data:
- `k : ℕ`;
- `X H : 𝕊^n`.

Derived API:
- the source-facing trace-power owner `π[k]`;
- the Hessian quadratic form `iteratedFDeriv ℝ 2 (π[k] : 𝕊^n → ℝ) X ![H, H]`;
- the Hermitian eigenvalue vectors of the matrix absolute values `CFC.abs X` and `CFC.abs H`.

Source/core/bridge triage:
- source-facing: Theorem 6.9's Hessian quadratic-form inequality on `𝕊^n`;
- core/canonical: `π[k]`, `iteratedFDeriv`, `eigenvalues`, and `CFC.abs`;
- bridge/view: the ambient trace/Frobenius expansion used only in Proposition 6.33.
-/

/-- Theorem 6.9: for every natural number `k`, the Hessian quadratic form of the Chapter 6
trace-power owner `π_k(X) = Trace (X^k)` at a symmetric matrix `X` in the symmetric direction `H`
is bounded above by `k(k - 1)` times the pairing of the eigenvalues of `(CFC.abs X)^(k - 2)` and
the squared eigenvalues of `CFC.abs H`. -/
theorem powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing
    (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] ≤
      (((k * (k - 1) : ℕ) : ℝ) *
        ∑ i : Fin n,
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (k - 2)) *
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (2 : ℕ))) := sorry
