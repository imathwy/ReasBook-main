import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_31 (from Chap07) -/
noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.31 lies in the positive-definite matrix / one-sided rounding domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the weighted primal norm;
- `positiveDefMatrixNorm_dualNorm_apply` in `Definition_7_23`, the canonical owner of the weighted
  dual norm `‖g‖[G,*]`;
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner from mathlib.

Best owner abstraction:
- source-facing: the one-sided updated matrix `G(α)` attached to `G`, `g`, and `α`;
- core/canonical: `‖g‖[G,*]` and `Matrix.vecMulVec`;
- bridge/view: the defining closed-form expansion below.

Primitive data:
- a positive-definite matrix `G : {G : Mat // G.PosDef}`;
- a vector `g : E`;
- a scalar parameter `α : ℝ`.

Derived API:
- the weighted dual radius is the existing owner `‖g‖[G,*]`, not a second local wrapper;
- theorem-level nonvanishing assumptions belong to the later containment and determinant-ratio
  statements, not to the matrix-path owner itself;
- the textbook restriction `α ∈ [0, 1]` is theorem-level side data for later estimates, not part of
  the matrix-path data itself.

Source/core/bridge triage:
- source-facing: `oneSidedRoundingUpdatedMatrix`;
- core/canonical: `positiveDefMatrixNorm` and `Matrix.vecMulVec`;
- bridge/view: `oneSidedRoundingUpdatedMatrix_def`.

The previous file duplicated the weighted dual radius as a separate public definition and encoded
proof-only side conditions in the owner data. This refinement keeps the source-facing matrix path as
the owner, reuses the canonical dual norm directly, and leaves nonvanishing and interval
restrictions to the theorem layer where they actually matter.
-/

/-- Definition 7.31: for a positive-definite matrix `G` on `ℝⁿ`, a vector `g ∈ ℝⁿ`, and a scalar
parameter `α`, the one-sided updated matrix is
`(1 - α) G + (α / r + ((r - 1) / 2)^2 (α / r)^2) ggᵀ`, where `r = ‖g‖*_G`. The textbook
restriction `α ∈ [0, 1]` and any later nonvanishing hypotheses are imposed only on the theorem
layer. -/
def oneSidedRoundingUpdatedMatrix
    (G : {G : Mat // G.PosDef}) (g : E) (α : ℝ) : Mat :=
  let r := ‖g‖[G,*]
  (1 - α) • G.1 +
    ((α / r) + (((r - 1) / 2) ^ (2 : ℕ)) * (α / r) ^ (2 : ℕ)) •
      vecMulVec g g

/-- Expanding `oneSidedRoundingUpdatedMatrix G g α` gives the textbook formula for `G(α)` with
`r = ‖g‖*_G`. -/
theorem oneSidedRoundingUpdatedMatrix_def
    (G : {G : Mat // G.PosDef}) (g : E) (α : ℝ) :
    oneSidedRoundingUpdatedMatrix G g α =
      (1 - α) • G.1 +
        ((α / ‖g‖[G,*]) +
            (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) •
          vecMulVec g g :=
  rfl

end

/-! ### Proposition_7_31 (from Chap07) -/
noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open SetConstrainedMinimizationProblem

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/- Proposition 7.31 lies in Chapter 7's fractional-covering / nonnegative-orthant normalization
domain.

Sampled owner-style declarations:
- `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the project owner for the
  orthant constraints `y ≥ 0`;
- `IsPositivelyHomogeneousOn` in `Chap03/Definition_3_1_7`, the chapter owner for positive
  homogeneity on cones;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  `EReal` owner for infima over explicit feasible sets;
- `maximalValueOn` in `Chap07/Definition_7_56`, the Chapter 7 maximization-side owner for
  suprema over explicit feasible sets;
- `FractionalCoveringProblem.optimalValue` in `Chap07/Definition_7_67`, the nearby chapter owner
  showing the same fractional-covering domain should route source values through those `EReal`
  optimization owners.

Best owner abstraction:
- source-facing: the Proposition 7.31 values `φ⋆`, the reciprocal-ratio supremum, and the
  normalized-slice supremum;
- core/canonical: `nonnegativeOrthant`, `IsPositivelyHomogeneousOn`,
  `SetConstrainedMinimizationProblem.optimalValue`, and `maximalValueOn`;
- bridge/view: the comparison theorems relating those three values.

Primitive data:
- `b : E` and `ψ : E → ℝ`;
- the three feasible subsets of `nonnegativeOrthant m` cut out by the side conditions
  `y ≠ 0`, `0 < ⟪b, y⟫`, and `⟪b, y⟫ = 1`.

Derived API:
- the source-facing value names below, implemented through the canonical `EReal` optimization
  owners;
- the reciprocal and normalization identities proved below.

Source/core/bridge triage:
- source-facing: `fractionalCoveringPhiStar`, `fractionalCoveringReciprocalPsiSup`, and
  `fractionalCoveringNormalizedPsiSup`;
- core/canonical: `nonnegativeOrthant`, `IsPositivelyHomogeneousOn`, `optimalValue`, and
  `maximalValueOn`;
- bridge/view: `fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup`,
  `fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup`, and
  `fractionalCoveringPhiStar_eq_inv_normalizedPsiSup`.

This refinement removes the duplicate raw-`ℝ` extremum wheel and the duplicate raw positive-
homogeneity binder. The three Proposition 7.31 values remain the public source-facing names, but
they are thin bridges to the project's canonical `EReal` optimization owners, and the
homogeneity input is stated through the chapter owner `IsPositivelyHomogeneousOn`. The owner
`fractionalCoveringPhiStar` keeps the source-facing feasible set `y ≥ 0, y ≠ 0`, while positivity
of `ψ` is carried only by the reciprocal bridge theorems where it is actually used to justify the
ratio reformulation.
-/

/-- The infimum `φ⋆ = inf_{y ≥ 0, y ≠ 0} ⟪b, y⟫ / ψ(y)` attached to a positively homogeneous
function on the nonnegative orthant. Positivity of `ψ` on this feasible set is a separate
hypothesis of the bridge theorems below, not part of the owner definition. -/
def fractionalCoveringPhiStar
    (b : E) (ψ : E → ℝ) : EReal :=
  (.mk (nonnegativeOrthant m ∩ {y | y ≠ 0}) (fun y : E ↦ inner ℝ b y / ψ y) :
    SetConstrainedMinimizationProblem E).optimalValue

/-- The supremum of the reciprocal ratio `ψ(y) / ⟪b, y⟫` over the nonnegative orthant where the
pairing with `b` is strictly positive. -/
def fractionalCoveringReciprocalPsiSup
    (b : E) (ψ : E → ℝ) : EReal :=
  maximalValueOn (nonnegativeOrthant m ∩ {y | 0 < inner ℝ b y})
    (fun y : E ↦ ψ y / inner ℝ b y)

/-- The supremum of `ψ` over the normalized nonnegative slice `⟪b, y⟫ = 1`. -/
def fractionalCoveringNormalizedPsiSup
    (b : E) (ψ : E → ℝ) : EReal :=
  maximalValueOn (nonnegativeOrthant m ∩ {y | inner ℝ b y = 1}) ψ

-- Proof sketch: for every nonzero nonnegative `y`, the hypotheses give `0 < ⟪b, y⟫` and
-- `0 < ψ(y)`, so `⟪b, y⟫ / ψ(y) = (ψ(y) / ⟪b, y⟫)⁻¹`; then take the infimum and supremum over
-- the corresponding feasible-set images.
/-- The fractional covering infimum is the reciprocal of the supremum of the reciprocal ratio
`ψ(y) / ⟪b, y⟫`. -/
theorem fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup
    (b : E) (ψ : E → ℝ)
    (hb_pos_on_orthant :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < inner ℝ b y)
    (hψ_pos :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < ψ y) :
    fractionalCoveringPhiStar b ψ = (fractionalCoveringReciprocalPsiSup b ψ)⁻¹ := sorry

-- Proof sketch: for `y ≥ 0` with `0 < ⟪b, y⟫`, normalize to `y / ⟪b, y⟫`; positive homogeneity
-- gives `ψ(y) / ⟪b, y⟫ = ψ(y / ⟪b, y⟫)`. Conversely, any point on the slice `⟪b, y⟫ = 1`
-- contributes the same value to both suprema.
/-- The reciprocal-ratio supremum equals the supremum of `ψ` on the normalized slice
`⟪b, y⟫ = 1`. -/
theorem fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup
    (b : E) (ψ : E → ℝ)
    (hψ_hom : IsPositivelyHomogeneousOn 1 (nonnegativeOrthant m) ψ) :
    fractionalCoveringReciprocalPsiSup b ψ = fractionalCoveringNormalizedPsiSup b ψ := sorry

-- Proof sketch: combine `fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup` with
-- `fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup`.
/-- Proposition 7.31: if `ψ` is positive on the nonzero nonnegative orthant, positively
homogeneous of degree `1`, and `⟪b, y⟫` is positive on every nonzero nonnegative vector, then the
value `φ⋆ = inf_{y ≥ 0, y ≠ 0} ⟪b, y⟫ / ψ(y)` is the reciprocal of the supremum of `ψ` on the
normalized slice `⟪b, y⟫ = 1`. -/
theorem fractionalCoveringPhiStar_eq_inv_normalizedPsiSup
    (b : E) (ψ : E → ℝ)
    (hb_pos_on_orthant :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < inner ℝ b y)
    (hψ_pos :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < ψ y)
    (hψ_hom : IsPositivelyHomogeneousOn 1 (nonnegativeOrthant m) ψ) :
    fractionalCoveringPhiStar b ψ = (fractionalCoveringNormalizedPsiSup b ψ)⁻¹ := by
  rw [fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup b ψ hb_pos_on_orthant hψ_pos,
    fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup b ψ hψ_hom]

end
