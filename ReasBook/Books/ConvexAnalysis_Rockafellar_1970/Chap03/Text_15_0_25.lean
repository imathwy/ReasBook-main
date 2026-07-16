import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_15_3_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_21
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Matrix
open LinearMap.BilinMap
open scoped GaugePolar RealInnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The quadratic function `x ↦ (1 / 2) ⟪x, Qx⟫`, viewed in the chapter's `EReal` codomain. -/
abbrev matrixQuadratic (Q : Matrix (Fin n) (Fin n) ℝ) : E → EReal :=
  (⇑((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin))).toEReal

/-- The square-root gauge `x ↦ ⟪x, Qx⟫^(1 / 2)` attached to a matrix, viewed in the chapter's
`EReal` codomain. -/
def matrixQuadraticGauge (Q : Matrix (Fin n) (Fin n) ℝ) : E → EReal :=
  fun x ↦ ((Real.sqrt ⟪x, Q.toEuclideanLin x⟫ : ℝ) : EReal)

/-- Evaluating `matrixQuadraticGauge Q` at `x` gives the square root of the quadratic form
`⟪x, Qx⟫`. -/
@[simp] theorem matrixQuadraticGauge_apply (Q : Matrix (Fin n) (Fin n) ℝ) (x : E) :
    matrixQuadraticGauge Q x =
      ((Real.sqrt ⟪x, Q.toEuclideanLin x⟫ : ℝ) : EReal) :=
  rfl

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.25 records the quadratic example `matrixQuadratic Q`,
  i.e. `f x = (1 / 2) ⟪x, Qx⟫`, its inverse-matrix conjugate in the positive-definite case, the
  associated square-root gauge `matrixQuadraticGauge Q = (fun x ↦ ⟪x, Qx⟫^(1 / 2))` on the
  positive-semidefinite locus, and the inverse-matrix formula for its polar.
- `core/canonical`: the ambient owners are `convexConjugate`, the canonical quadratic-form owner
  `LinearMap.BilinMap.toQuadraticMap`, and the Chapter 15 owners `powerGaugeTransform`,
  `IsClosedGauge`, `IsGaugeNorm`, and `gauge_polar`.
- `bridge/view`: `matrixQuadratic Q` is the canonical quadratic owner coerced to the chapter's
  `EReal` codomain, while `powerGaugeTransform 2 (matrixQuadratic Q)` is the Chapter 15 bridge
  back to the source-facing owner `matrixQuadraticGauge Q` under the primitive hypothesis
  `Q.PosSemidef`. The nonsingular conjugate formula is the inverse-matrix specialization of the
  earlier quadratic-owner conjugate API.

Domain-style sampling used here:
- `LinearMap.BilinMap.toQuadraticMap`;
- `convexConjugate_matrixQuadraticMap_eq_inverse`;
- `powerGaugeTransform`;
- `IsGaugeNorm`.

Primitive data vs derived API:
- primitive source-facing data: the matrix `Q`;
- reused owner data: the quadratic owner `matrixQuadratic Q`, the Chapter 15 owner
  `powerGaugeTransform 2 (matrixQuadratic Q)` on the positive-semidefinite locus, the conjugate
  owner `convexConjugate`, the source-facing owner `matrixQuadraticGauge Q`, and the Chapter 15
  gauge owners;
- derived API: the bridge theorems from `powerGaugeTransform` to `matrixQuadraticGauge`, together
  with the closed-proper-convex, conjugate, closed-gauge, norm-gauge, and polar formulas for this
  quadratic specialization.

Layer target: `source-facing`, with the public owner surface centered on the textbook square-root
gauge `matrixQuadraticGauge Q`, while `matrixQuadratic Q` is kept only as the short codomain-lift
bridge needed to state the Chapter 15 owner theorems.
-/

-- Proof sketch: the quadratic form
-- `((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin))` scales by `c^2` under
-- `x ↦ c • x` because `toQuadraticMap` is quadratic. Coercing that scaling law to `EReal` gives
-- degree-`2` positive homogeneity.
/-- The quadratic function attached to a matrix is positively homogeneous of degree `2`. -/
theorem matrixQuadratic_positivelyHomogeneousOfDegree_two
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    (matrixQuadratic Q).PositivelyHomogeneousOfDegree 2 :=
  sorry

-- Proof sketch: for a positive semidefinite matrix,
-- `⟪x, Matrix.toEuclideanLin Q x⟫` is nonnegative, so the negative and `⊤` branches in
-- `powerGaugeTransform 2` never occur. On finite real values,
-- the formula from `powerGaugeTransform_apply_of_nonneg_lt_top` reduces to
-- `sqrt (2 * (1 / 2) * ⟪x, Qx⟫) = sqrt ⟪x, Qx⟫`.
/-- For a positive semidefinite matrix, the Chapter 15 bridge owner
`powerGaugeTransform 2 (matrixQuadratic Q)` is exactly the source-facing square-root gauge
`matrixQuadraticGauge Q`. -/
theorem powerGaugeTransform_two_matrixQuadratic_eq_matrixQuadraticGauge
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    powerGaugeTransform 2 (matrixQuadratic Q) =
      matrixQuadraticGauge Q := sorry

-- Proof sketch: apply the previous square-root identification to the inverse matrix. Positive
-- definiteness is preserved by inversion, so the same power-gauge argument gives the dual formula
-- with `Q⁻¹`.
/-- For a positive definite matrix, the same square-root formula identifies the degree-`2`
power-gauge transform of the inverse quadratic function. -/
theorem powerGaugeTransform_two_inverse_matrixQuadratic_eq_matrixQuadraticGauge
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    powerGaugeTransform 2 (matrixQuadratic Q⁻¹) =
      matrixQuadraticGauge Q⁻¹ := sorry

-- Proof sketch: a positive semidefinite quadratic form on Euclidean space has a closed epigraph,
-- is finite everywhere, and is convex, hence proper. This is the standard quadratic example of a
-- closed proper convex function.
/-- Text 15.0.25 (1): for a symmetric positive semidefinite matrix `Q`, the quadratic function
`f(x) = (1 / 2) ⟪x, Qx⟫`, represented here by `matrixQuadratic Q`,
is a closed proper convex function on `R^n`. -/
theorem matrixQuadratic_isClosedProperConvex
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    (matrixQuadratic Q).IsClosedProperConvex :=
  sorry

-- Proof sketch: apply the nonsingular quadratic-conjugate formula from the quadratic-function
-- item directly to the owner `convexConjugate`. Positive definiteness supplies the invertibility
-- and the inverse quadratic is again given by `Q⁻¹`.
/- Text 15.0.25 (2): the conjugate of `f(x) = (1 / 2) ⟪x, Qx⟫` is
`f*(xStar) = (1 / 2) ⟪xStar, Q⁻¹ xStar⟫`. This is exactly the owner theorem already established in
Text 12.3.2. -/
recall convexConjugate_matrixQuadraticMap_eq_inverse

-- Proof sketch: the preceding closed-proper-convex statement and the degree-`2` homogeneity of the
-- quadratic function put the matrix quadratic exactly in the scope of Corollary 15.3.2. Rewriting
-- its power-gauge transform by the square-root bridge theorem yields the closed-gauge claim for
-- `matrixQuadraticGauge Q`.
/-- Text 15.0.25 (3): the square-root gauge `matrixQuadraticGauge Q`, i.e.
`k(x) = ⟨x, Qx⟩^{1/2}`, is a closed gauge. -/
theorem matrixQuadraticGauge_isClosedGauge
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    IsClosedGauge (matrixQuadraticGauge Q) := sorry

-- Proof sketch: positive definiteness makes `x ↦ ⟨x, Qx⟩^{1/2}` finite everywhere, symmetric, and
-- strictly positive away from the origin. Combined with the previous closed-gauge theorem, these
-- are exactly the extra clauses required for the norm-gauge predicate.
/-- Text 15.0.25 (4): the square-root gauge `matrixQuadraticGauge Q`, i.e.
`k(x) = ⟨x, Qx⟩^{1/2}`, is in fact a norm-gauge. -/
theorem matrixQuadraticGauge_isGaugeNorm
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    IsGaugeNorm (matrixQuadraticGauge Q) := sorry

-- Proof sketch: apply Corollary 15.3.2 to the quadratic function and use the explicit conjugate
-- formula from clause (2). The resulting polar identity is then rewritten on both sides by the two
-- square-root bridge lemmas, producing the inverse-matrix square-root formula.
/-- Text 15.0.25 (5): the polar of `matrixQuadraticGauge Q`, i.e. `k(x) = ⟨x, Qx⟩^{1/2}`, is
`matrixQuadraticGauge Q⁻¹`, i.e. `kᵒ(xStar) = ⟨xStar, Q⁻¹ xStar⟩^{1/2}`. -/
theorem gauge_polar_matrixQuadraticGauge_eq_inverse
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    (matrixQuadraticGauge Q)ᵒ =
      matrixQuadraticGauge Q⁻¹ := sorry

end
