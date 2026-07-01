import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open LinearMap.BilinMap
open scoped Rockafellar
open scoped RealInnerProductSpace

attribute [local instance] Classical.propDecidable

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

namespace LinearMap

/-- `T'` is a range pseudoinverse of `T` when both composites with `T` agree with a projection
onto `range(T)` in the canonical `LinearMap.IsProj` sense, and the image of `T'` lies in
`range(T)`. This owner is purely linear-algebraic and does not depend on any inner-product model.
-/
def IsRangePseudoinverse (T T' : E →ₗ[𝕜] E) : Prop :=
  ∃ p : E →ₗ[𝕜] E,
    LinearMap.IsProj T.range p ∧
      T ∘ₗ T' = p ∧
      T' ∘ₗ T = p ∧
      T'.range ≤ T.range

/-- The identity endomorphism is a range pseudoinverse of itself. -/
@[simp] theorem id_isRangePseudoinverse :
    (LinearMap.id : E →ₗ[𝕜] E).IsRangePseudoinverse (LinearMap.id : E →ₗ[𝕜] E) := by
  refine ⟨LinearMap.id, ?_, ?_, ?_, ?_⟩
  · simpa using (LinearMap.IsProj.top (S := 𝕜) (M := E))
  · simp
  · simp
  · exact le_rfl

end LinearMap

end

section

variable {𝕜 : Type*} [Field 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

local instance : HasPairing E E (WithTopBot 𝕜) := instHasPairingWithTopBot

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.2 computes the conjugate of a quadratic source function and then
  specializes to the matrix pseudoinverse formula.
- `core/canonical`: the owner abstractions are `convexConjugate`, `QuadraticForm 𝕜 E`,
  `LinearMap.halfPairingQuadratic`, `LinearMap.BilinMap.toQuadraticMap`, `HasLinearPairing`,
  `LinearMap.IsProj`, and `LinearMap.range`. The quadratic branch is therefore pairing-owned,
  not tied to one concrete self-dual inner-product model.
- `bridge/view`: real inner-product and Euclidean-matrix statements are downstream specializations
  of this pairing-level owner.

Domain-style sampling used here:
- `convexConjugate`;
- `QuadraticForm 𝕜 E`;
- `LinearMap.halfPairingQuadratic`;
- `LinearMap.BilinMap.toQuadraticMap`;
- `HasLinearPairing`;
- `LinearMap.IsProj`;
- `LinearMap.range`.

Primitive data vs derived API:
- primitive core data: a pairing `HasLinearPairing E E 𝕜`, an endomorphism `T`, its
  pseudoinverse candidate `T'`, and pairing-side nonnegativity of `x ↦ ⟪x, T x⟫ₚ`;
- owner-derived data: the quadratic form
  `(1 / 2 : 𝕜) • toQuadraticMap (HasLinearPairing.pairingLinear.compl₂ T)` and `T.range`;
- derived API: the piecewise conjugate formula, with real inner-product and matrix statements
  recovered as bridges.

Layer target: `core/canonical`. The source-facing theorem is kept at the pairing-level owner and
weaker scalar layer; concrete inner-product and matrix forms remain bridge declarations only.
-/

namespace LinearMap

/-- Pairing-root quadratic owner `x ↦ (1 / 2) ⟪x, T x⟫ₚ`, viewed in `WithTopBot 𝕜`. -/
def halfPairingQuadratic (T : E →ₗ[𝕜] E) : E → WithTopBot 𝕜 :=
  Function.toWithTopBot
    ((1 / 2 : 𝕜) •
      toQuadraticMap ((HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E).compl₂ T))

/-- Unfolding bridge for `halfPairingQuadratic`. -/
@[simp] theorem halfPairingQuadratic_eq_toWithTopBot (T : E →ₗ[𝕜] E) :
    halfPairingQuadratic T =
      ((⇑((1 / 2 : 𝕜) •
          toQuadraticMap
            ((HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E).compl₂ T))).toWithTopBot) :=
  rfl

-- Proof sketch: maximize the concave quadratic
-- `x ↦ ⟪xStar, x⟫ₚ - (1 / 2) ⟪x, T x⟫ₚ`.
/-- Pairing-level quadratic conjugate formula: for a pseudoinverse on `range(T)`, the Fenchel
conjugate of `x ↦ (1 / 2) ⟪x, T x⟫ₚ` is the corresponding pseudoinverse quadratic on `range(T)` and
`⊤` outside `range(T)`. -/
theorem convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse
    (T T' : E →ₗ[𝕜] E)
    [Preorder 𝕜] [SupSet (WithTopBot 𝕜)]
    (hT_nonneg : ∀ x : E, 0 ≤ (⟪x, T x⟫ₚ : 𝕜))
    (hT' : T.IsRangePseudoinverse T') :
    (halfPairingQuadratic T)⋆ =
      fun xStar : E ↦
        if xStar ∈ T.range then
          halfPairingQuadratic T' xStar
        else ⊤ := by
  let _ := hT_nonneg
  let _ := hT'
  sorry

/-- Intrinsic full-range specialization of the quadratic conjugate formula: when `range(T) = ⊤`,
the outside branch disappears and the conjugate is exactly the pseudoinverse quadratic. -/
theorem convexConjugate_halfPairingQuadratic_eq_of_isRangePseudoinverse_of_range_eq_top
    (T T' : E →ₗ[𝕜] E)
    [Preorder 𝕜] [SupSet (WithTopBot 𝕜)]
    (hT_nonneg : ∀ x : E, 0 ≤ (⟪x, T x⟫ₚ : 𝕜))
    (hT' : T.IsRangePseudoinverse T')
    (hT_range : T.range = ⊤) :
    (halfPairingQuadratic T)⋆ = halfPairingQuadratic T' := by
  simpa [hT_range] using
    convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse
      T T' hT_nonneg hT'

end LinearMap

end

section

variable {ι : Type*} [Fintype ι]

attribute [local instance] Classical.decEq

local notation "E" => EuclideanSpace ℝ ι
local notation "M" => Matrix ι ι ℝ

local instance : HasPairing E E (WithTopBot ℝ) := instHasPairingWithTopBot

/-!
Matrix specialization for Text 12.3.2.

- `source-facing`: the textbook statement is phrased for a symmetric positive semidefinite matrix
  `Q` and its Moore-Penrose pseudoinverse `Q'`.
- `core/canonical`: this is a bridge specialization of the pairing-level owner
  `LinearMap.halfPairingQuadratic` and the operator pseudoinverse relation on `Q.toEuclideanLin`.
- `bridge/view`: the declarations below are the Euclidean-matrix specializations of that owner and
  keep the source wording without reintroducing a parallel matrix-root definition.
-/

-- Proof sketch: specialize the operator-level quadratic-conjugate theorem to `Q.toEuclideanLin`
-- and `Q'.toEuclideanLin`, and obtain pairing-side nonnegativity from
-- `Matrix.isPositive_toEuclideanLin_iff`.
/-- Text 12.3.2: if `Q` is positive semidefinite and `Q'` is its Moore-Penrose pseudoinverse, then
the conjugate of `x ↦ (1 / 2) ⟪x, Qx⟫` is the quadratic function of `Q'` on `range(Q)` and `⊤`
outside `range(Q)`. -/
theorem convexConjugate_matrixQuadraticMap_eq_if_mem_range_of_isRangePseudoinverse
    (Q Q' : M) (hQ : Q.PosSemidef)
    (hQ' : Q.toEuclideanLin.IsRangePseudoinverse Q'.toEuclideanLin) :
    (LinearMap.halfPairingQuadratic Q.toEuclideanLin)⋆ =
      fun xStar : E ↦
        if xStar ∈ Q.toEuclideanLin.range then
          LinearMap.halfPairingQuadratic Q'.toEuclideanLin xStar
        else ⊤ := by
  have hQlin : Q.toEuclideanLin.IsPositive := by
    exact
      ((show Q.toEuclideanLin.IsPositive ↔ Q.PosSemidef from
          Matrix.isPositive_toEuclideanLin_iff).2 hQ)
  have hQ_nonneg : ∀ x : E, 0 ≤ (⟪x, Q.toEuclideanLin x⟫ₚ : ℝ) := by
    intro x
    simpa using hQlin.inner_nonneg_right x
  simpa using
    LinearMap.convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse
      Q.toEuclideanLin Q'.toEuclideanLin hQ_nonneg hQ'

-- Proof sketch: for a positive-definite matrix, `Q.toEuclideanLin.range = ⊤`, so the outside
-- branch of the piecewise formula disappears. The Moore-Penrose pseudoinverse is then the
-- ordinary inverse matrix.
/-- In the positive-definite case, the conjugate of `x ↦ (1 / 2) ⟪x, Qx⟫` is the quadratic
function attached to `Q⁻¹`. -/
theorem convexConjugate_matrixQuadraticMap_eq_inverse {Q : M} (hQ : Q.PosDef) :
    (LinearMap.halfPairingQuadratic Q.toEuclideanLin)⋆ =
      LinearMap.halfPairingQuadratic (Q⁻¹).toEuclideanLin := by
  have hQlin : Q.toEuclideanLin.IsPositive := by
    exact
      ((show Q.toEuclideanLin.IsPositive ↔ Q.PosSemidef from
          Matrix.isPositive_toEuclideanLin_iff).2 hQ.posSemidef)
  have hQ_nonneg : ∀ x : E, 0 ≤ (⟪x, Q.toEuclideanLin x⟫ₚ : ℝ) := by
    intro x
    simpa using hQlin.inner_nonneg_right x
  have hQinv : Q.toEuclideanLin.IsRangePseudoinverse (Q⁻¹).toEuclideanLin := by
    sorry
  have hQrange : Q.toEuclideanLin.range = ⊤ := by
    sorry
  simpa using
    LinearMap.convexConjugate_halfPairingQuadratic_eq_of_isRangePseudoinverse_of_range_eq_top
      Q.toEuclideanLin (Q⁻¹).toEuclideanLin hQ_nonneg hQinv hQrange

end
