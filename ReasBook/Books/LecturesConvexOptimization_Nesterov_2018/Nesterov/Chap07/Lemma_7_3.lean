import Mathlib.Analysis.InnerProductSpace.Subspace
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_9
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_17
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped SupportFunction RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 7.3 lies in Chapter 7's symmetric-matrix support-function / spectral-radius domain.

Sampled owner-style declarations:
- Chapter 3 `supportFunction` and `supportFunction_apply`, the chapter owner for support functions;
- Chapter 5 `𝕊^n`, `RealSymmetricMatrixSpace.eigenvalues`, and `⟪·, ·⟫_F`, the established
  symmetric-matrix carrier and Frobenius geometry;
- Chapter 7 `spectral_eigenvalue_l1_unit_ball`, the source-facing owner of the set `Q₂`;
- Chapter 7 `ρ(X)`, the canonical spectral-radius surface on `𝕊^n`.

Best owner abstraction:
- source-facing: Lemma 7.3's support-function formula for the spectral radius on `𝕊^n`;
- core/canonical: `spectral_eigenvalue_l1_unit_ball n`, `ξ[·]`, `⟪·, ·⟫_F`, and `ρ(X)`;
- bridge/view: the explicit trace-supremum formula obtained by expanding the owner support function
  on the Frobenius symmetric-matrix space.

Primitive data:
- `X : 𝕊^n`.

Derived API:
- the closedness / convexity / Frobenius-ball bounds for `spectral_eigenvalue_l1_unit_ball n`;
- the explicit trace formula for `(ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal`;
- Lemma 7.3's main identity `ρ(X) = (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal`.

This refinement deletes the duplicate local trace-pairing, Hermitian-set, and semidefinite-gauge
owners, together with the duplicate local Frobenius inner-product instances. The file now reuses
the Chapter 5 owners directly and keeps only the source-facing bridge theorems specific to this
lemma.
-/

-- Proof sketch: the eigenvalue map on `𝕊^n` is continuous, so the defining `ℓ₁`-sublevel set is
-- closed in the inherited Frobenius topology.
/-- The set `Q₂` of symmetric matrices whose eigenvalue `ℓ₁`-sum is at most `1` is closed. -/
theorem isClosed_spectral_eigenvalue_l1_unit_ball
    (n : ℕ) :
    IsClosed (spectral_eigenvalue_l1_unit_ball n) := sorry

-- Proof sketch: `Q₂` is the unit ball of the nuclear norm restricted to symmetric matrices, so
-- it is convex.
/-- The set `Q₂` is convex. -/
theorem convex_spectral_eigenvalue_l1_unit_ball
    (n : ℕ) :
    Convex ℝ (spectral_eigenvalue_l1_unit_ball n) := sorry

-- Proof sketch: if the Frobenius norm is at most `1 / √n`, then Cauchy--Schwarz bounds the
-- eigenvalue `ℓ₁`-norm by `1`.
/-- The Frobenius closed ball of radius `1 / √n` in `𝕊^n` is contained in `Q₂`. -/
theorem closedBall_subset_spectral_eigenvalue_l1_unit_ball
    (n : ℕ) :
    Metric.closedBall (0 : 𝕊^n) (1 / Real.sqrt n) ⊆
      spectral_eigenvalue_l1_unit_ball n := sorry

-- Proof sketch: on `Q₂`, the Frobenius norm is the eigenvalue `ℓ₂`-norm, which is bounded above
-- by the eigenvalue `ℓ₁`-norm.
/-- The set `Q₂` is contained in the Frobenius closed ball of radius `1`. -/
theorem spectral_eigenvalue_l1_unit_ball_subset_closedBall
    (n : ℕ) :
    spectral_eigenvalue_l1_unit_ball n ⊆
      Metric.closedBall (0 : 𝕊^n) (1 : ℝ) := sorry

-- Proof sketch: expand the Chapter 3 support function on the inner-product space `𝕊^n`, then
-- identify the inherited inner product with the Chapter 5 Frobenius trace pairing on symmetric
-- matrices.
/-- Expanding the support function of `Q₂` at `X` gives the textbook trace supremum formula. -/
theorem supportFunction_toReal_Q2_eq_sSup_trace
    (X : SymmMat) :
    (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal =
      sSup ((fun U : SymmMat ↦ Matrix.trace ((X : Mat) * (U : Mat))) ''
        spectral_eigenvalue_l1_unit_ball n) := sorry

-- Proof sketch: Definition 7.17 identifies `ρ(X)` as the canonical spectral-radius owner on
-- `𝕊^n`, and Lemma 7.3 expresses this owner as the support function of `Q₂` with respect to the
-- Frobenius geometry.
/-- Lemma 7.3: for a real symmetric matrix `X`, the spectral radius `ρ(X)` is the support
function of `Q₂`. -/
theorem realSymmetricMatrix_toReal_spectralRadius_eq_supportFunction_Q2
    (X : SymmMat) :
    ρ(X) = (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal := sorry
