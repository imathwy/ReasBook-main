import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_3
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealSymmetricMatrixSpace

variable {n : ℕ}

/- Definition 7.44 lies in Chapter 7's real symmetric-matrix spectral-radius / semidefinite-order
domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, the project owner for real symmetric matrices;
- Chapter 5 `𝕊^n₊` and `mem_positiveSemidefiniteCone_iff`, the intrinsic positive-semidefinite cone
  and its bridge to `Matrix.PosSemidef`;
- Chapter 7 `ρ(X)` and
  `realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues` in `Definition_7_17`, the
  canonical spectral-radius surface and its eigenvalue bridge;
- mathlib `Matrix.nonneg_iff_posSemidef`, the canonical proof-layer bridge from matrix order to
  positive semidefiniteness.

Best owner abstraction:
- source-facing: Definition 7.44's least semidefinite bound for the spectral radius;
- core/canonical: the chapter owners `𝕊^n`, `𝕊^n₊`, and the spectral-radius surface `ρ(X)`;
- bridge/view: the cone-membership inequalities `τ I_n ± X ∈ 𝕊^n₊`, equivalently the ambient
  matrix semidefinite conditions and the two-sided matrix-order bound `-τ I_n ≤ X ≤ τ I_n`.

Primitive data:
- `X : 𝕊^n`.

Derived API:
- the spectral-radius owner `ρ(X)`;
- the eigenvalue formula already provided by `Definition_7_17`;
- the semidefinite-bound theorem below, stated directly on `𝕊^n` via membership in `𝕊^n₊`.

This refinement removes the duplicate raw subtype `{M // M.IsSymm}` and the duplicate
Hermitian/eigenvalue bridge from this file. The public surface now grows from the existing chapter
owners `𝕊^n` and `𝕊^n₊`, and the new theorem keeps only the source-facing semidefinite
characterization that is not already owned upstream.
-/

/-- The nonnegative semidefinite cone bounds that dominate a symmetric matrix on both sides. -/
def realSymmetricMatrix_spectralRadiusSemidefiniteBounds
    (X : 𝕊^n) : Set ℝ :=
  {τ : ℝ |
    0 ≤ τ ∧
      τ • (1 : 𝕊^n) - X ∈ 𝕊^n₊ ∧
      τ • (1 : 𝕊^n) + X ∈ 𝕊^n₊}

/-- Definition 7.44: for a real symmetric matrix, the spectral radius is the least nonnegative
real scalar `τ` such that both symmetric matrices `τ I_n - X` and `τ I_n + X` lie in the
positive-semidefinite cone `𝕊^n₊`. -/
-- Proof sketch: use the Chapter 7 owner `ρ(X)` from `Definition_7_17`, rewrite the spectral
-- radius as the operator norm of the associated self-adjoint matrix, apply the standard
-- two-sided order characterization `-τ I ≤ X ≤ τ I`, and translate those order inequalities to
-- intrinsic cone membership in `𝕊^n₊` via `Matrix.nonneg_iff_posSemidef` together with
-- `mem_positiveSemidefiniteCone_iff`. Stating the admissible set over nonnegative scalars keeps
-- the canonical least-bound surface and removes the artificial `n > 0` side condition: when
-- `n = 0`, the cone constraints are vacuous but the extra bound `0 ≤ τ` makes `0` the least
-- admissible scalar.
theorem realSymmetricMatrix_toReal_spectralRadius_isLeast_semidefiniteBound
    (X : 𝕊^n) :
    IsLeast (realSymmetricMatrix_spectralRadiusSemidefiniteBounds X) ρ(X) := sorry

end
