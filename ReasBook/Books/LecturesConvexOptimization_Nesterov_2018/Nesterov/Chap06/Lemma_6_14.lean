import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_4_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open RealSymmetricMatrixSpace
open PositiveSemidefiniteCone
open scoped BigOperators MatrixOrder NNReal RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Lemma 6.14 lies in the chapter's symmetric-matrix/Frobenius spectral-calculus domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 5 `𝕊^n₊`, `PositiveSemidefiniteCone.nnrpow`, and the induced notation `X ^ p` on
  `𝕊^n₊` in `Definition_5_4_4_3`, the established positive-semidefinite owner and its intrinsic
  nonnegative-power bridge;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the established
  Frobenius owner `⟪·, ·⟫_F` on `𝕊^n`;
- mathlib `CFC.nnrpow`, the canonical ambient nonnegative-spectrum functional-calculus power.

Best owner abstraction:
- source-facing: the symmetric-matrix/Frobenius inequality of Lemma 6.14;
- core/canonical: the chapter carriers `𝕊^n`, `𝕊^n₊`, and `⟪·, ·⟫_F`;
- bridge/view: the ambient matrix real-power operation on a positive-semidefinite symmetric
  matrix, viewed back in `𝕊^n`.

Primitive data:
- nonnegative exponents `p q : ℝ≥0`;
- a positive-semidefinite symmetric matrix `X : 𝕊^n₊`;
- a symmetric direction `H : 𝕊^n`.

Derived API:
- the source-facing PSD power notation `X ^ p` on `𝕊^n₊`;
- the symmetric square `H ^ 2`.

Source/core/bridge triage:
- source-facing: Lemma 6.14 itself on symmetric matrices and the Frobenius pairing;
- core/canonical: `𝕊^n`, `𝕊^n₊`, `X ^ p` on `𝕊^n₊`, `⟪·, ·⟫_F`, and intrinsic eigenvalues on
  `𝕊^n`;
- bridge/view: the coercion from `𝕊^n₊` to `𝕊^n` and then to ambient matrices.

The refinement below reuses the chapter owner `X ^ p` on the intrinsic cone subtype `X : 𝕊^n₊`,
keeps the source-facing inequality on the single mixed trace term that appears in Proposition 6.33,
and does not export a separate owner for a one-off symmetrized package.
-/

-- Proof sketch: diagonalize the positive-semidefinite symmetric matrix `X` orthogonally, compare
-- the mixed power term entrywise using `a^p b^q ≤ a^(p+q)` on the nonnegative eigenvalues of `X`,
-- rewrite the resulting trace as the Frobenius pairing with `X^(p+q)` and
-- `H^2`, and then apply von Neumann's trace inequality to the positive semidefinite matrices
-- `X^(p+q)` and `H^2`.
/-- Lemma 6.14: for nonnegative exponents, a positive-semidefinite symmetric matrix `X`, and a
real symmetric matrix `H`, the single mixed trace term `trace (((X^p H X^q)ᵀ) H)` is bounded by
the Frobenius pairing of `X^(p+q)` with `H^2`, and this is in turn bounded by the pairing of the
eigenvalue vectors of `X^(p+q)` and `H^2`. -/
theorem frobenius_power_sandwich_bound
    (p q : ℝ≥0) (X : 𝕊^n₊) (H : SymmMat) :
    Matrix.trace
        (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat))
      ≤ ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F ∧
    ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
      ≤ ∑ i : Fin n, eigenvalues (X ^ (p + q) : 𝕊^n₊) i * eigenvalues (H ^ (2 : ℕ)) i :=
  sorry
