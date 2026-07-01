import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Matrix
open LinearMap.BilinMap
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.26 identifies the polar of the quadratic unit sublevel set
  `{x | ⟪x, Qx⟫ ≤ 1}`.
- `core/canonical`: the owner theorem already present upstream is
  the Chapter 15 polar-set owner theorem from `Corollary_15_3_2`,
  together with the source-facing quadratic owner `matrixQuadratic`,
  `matrixQuadratic_isClosedProperConvex`, and
  `matrixQuadratic_positivelyHomogeneousOfDegree_two`.
- `bridge/view`: this item is the explicit quadratic-matrix specialization of that owner theorem,
  obtained by rewriting the `1 / 2`-sublevel sets of `matrixQuadratic Q` and its
  inverse-matrix
  counterpart as the displayed quadratic unit sublevel sets.

Domain-style sampling used here:
- `LinearMap.BilinMap.toQuadraticMap` from `Text_12_3_2`;
- `matrixQuadratic_isClosedProperConvex` from `Text_15_0_25`;
- `matrixQuadratic_positivelyHomogeneousOfDegree_two` from `Text_15_0_25`;
- the Chapter 15 polar-set owner theorem;
- `Corollary_15_3_2`.

Primitive data vs derived API:
- primitive source-facing data: the positive definite matrix `Q` and its quadratic unit sublevel
  set;
- reused owner data: `matrixQuadratic Q` and the chapter polar-set owner theorem;
- derived API: the explicit inverse-matrix formula for the polar quadratic unit sublevel set.

Layer target: `source-facing`, stated directly as an equality of polar sets and quadratic
sublevel sets, without introducing any new wrapper around ellipsoids or quadratic gauges.
-/

-- Proof sketch: apply the Chapter 15 owner theorem
-- the Chapter 15 polar-set owner theorem to
-- `f = matrixQuadratic Q`
-- with the quadratic
-- closed-proper-convex
-- and degree-`2` homogeneity results from Text 15.0.25 and the canonical Hölder-conjugate pair
-- `2, 2`. Then rewrite the `1 / 2`-sublevel conditions
-- `((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin)) x ≤ 1 / 2` and
-- `((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ (Q⁻¹).toEuclideanLin)) xStar ≤ 1 / 2` as
-- `⟪x, toEuclideanLin Q x⟫ ≤ 1` and `⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ 1`.
/-- Text 15.0.26: if `Q` is a positive definite real matrix, then the polar of the quadratic unit
sublevel set `{x | ⟪x, Qx⟫ ≤ 1}` is the inverse-quadratic unit sublevel set
`{xStar | ⟪xStar, Q⁻¹ xStar⟫ ≤ 1}`. -/
theorem polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    Set.polar {x : E | ⟪x, toEuclideanLin Q x⟫ ≤ 1} =
      {xStar : E | ⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ 1} := by
  have htwo : (0 : ℝ) ≤ 2 := by
    norm_num
  have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 := by
    norm_num
  have hsublevel (A : Matrix (Fin n) (Fin n) ℝ) :
      {x : E |
        ((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ A.toEuclideanLin)) x ≤ (1 / 2 : ℝ)} =
        {x : E | ⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ)} := by
    ext x
    change ((1 / 2 : ℝ) * ⟪x, toEuclideanLin A x⟫ ≤ (1 / 2 : ℝ)) ↔ _
    constructor
    · intro hx
      have h' := mul_le_mul_of_nonneg_left hx htwo
      simpa [mul_assoc] using h'
    · intro hx
      simpa using mul_le_mul_of_nonneg_left hx hhalf_nonneg
  have hsublevelEReal (A : Matrix (Fin n) (Fin n) ℝ) :
      {x : E | matrixQuadratic A x ≤ (1 / 2 : ℝ)} =
        {x : E | ⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ)} := by
    ext x
    change
      (((((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ A.toEuclideanLin)) x : ℝ) :
          EReal) ≤
        ((1 / 2 : ℝ) : EReal)) ↔
      (⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ))
    rw [EReal.coe_le_coe_iff]
    change ((1 / 2 : ℝ) * ⟪x, toEuclideanLin A x⟫ ≤ (1 / 2 : ℝ)) ↔
      (⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ))
    constructor
    · intro hx
      have h' := mul_le_mul_of_nonneg_left hx htwo
      simpa [mul_assoc] using h'
    · intro hx
      simpa using mul_le_mul_of_nonneg_left hx hhalf_nonneg
  have hpolar :=
    polar_powerSublevel_eq_conjugatePowerSublevel
      Real.HolderConjugate.two_two
      (matrixQuadratic_isClosedProperConvex hQ.posSemidef)
      (matrixQuadratic_positivelyHomogeneousOfDegree_two Q)
  have hconj : convexConjugate (matrixQuadratic Q) = matrixQuadratic Q⁻¹ := by
    simpa [Function.toEReal, matrixQuadratic] using
      convexConjugate_matrixQuadraticMap_eq_inverse hQ
  calc
    Set.polar {x : E | ⟪x, toEuclideanLin Q x⟫ ≤ 1} =
        Set.polar {x : E | matrixQuadratic Q x ≤ (1 / 2 : ℝ)} := by
          rw [hsublevelEReal Q]
    _ = {xStar : E | convexConjugate (matrixQuadratic Q) xStar ≤ (1 / 2 : ℝ)} := hpolar
    _ = {xStar : E | matrixQuadratic Q⁻¹ xStar ≤ (1 / 2 : ℝ)} := by
          rw [hconj]
    _ = {xStar : E | ⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ (1 : ℝ)} := by
          rw [hsublevelEReal Q⁻¹]

end
