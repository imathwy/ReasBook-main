import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Matrix
open LinearMap.BilinMap
open scoped RealInnerProductSpace Rockafellar

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
variable (Q : Matrix (Fin n) (Fin n) ℝ) (a : E) (α : ℝ)

set_option quotPrecheck false in
local notation "q" => ((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin))
set_option quotPrecheck false in
local notation "qInv" => ((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ (Q⁻¹).toEuclideanLin))
set_option quotPrecheck false in
local notation "C" => {x : E | q x + ⟪a, x⟫ + α ≤ 0}
set_option quotPrecheck false in
local notation "b" => -((Q⁻¹).toEuclideanLin a)
local notation "β" => qInv a - α

/-!
Source/core/bridge triage:

- `source-facing`: Text 13.5.2 studies the concrete elliptic sublevel set
  `C = {x | (1/2) ⟪x, Qx⟫ + ⟪a, x⟫ + α ≤ 0}` and computes its support function explicitly.
- `core/canonical`: the ambient owners are
  `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`,
  the affine-change owner `convexConjugate_affineChange`, the project support function
  `supportFunction`, the canonical quadratic-form owner
  `LinearMap.BilinMap.toQuadraticMap`, the matrix bridge theorem
  `convexConjugate_matrixQuadraticMap_eq_inverse`, the matrix positivity notion `Matrix.PosDef`,
  and the Euclidean linear action `Matrix.toEuclideanLin`.
- `bridge/view`: the final statement keeps the source-facing sublevel set
  `δᵛ(xStar | C)`.

Domain-style sampling used here:
- `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`;
- `supportFunction`;
- `convexConjugate_affineChange`;
- `LinearMap.BilinMap.toQuadraticMap`;
- `convexConjugate_matrixQuadraticMap_eq_inverse`;
- `Matrix.toEuclideanLin`.

Primitive data vs derived API:
- the primitive source-facing datum is the explicit elliptic sublevel-set defining
  inequality, written locally as `C` and expressed directly from the canonical operator quadratic
  owner `LinearMap.BilinMap.toQuadraticMap`;
- the derived API is the explicit support-function formula, obtained by specializing the owner
  nonpositive-sublevel support-function theorem to an affine quadratic and then rewriting the
  conjugate data in inverse-matrix form, without introducing a second wrapper for quadratic
  sublevel sets.

Layer target: `bridge/view`, keeping the concrete textbook set while expressing its support
function through the chapter's canonical support-function and conjugation owners.
-/

-- Proof sketch: apply Theorem 13.5 to the finite convex quadratic
-- `x ↦ q x + ⟪a, x⟫ + α`,
-- whose conjugate is the inverse
-- quadratic with linear term `b = -(Q⁻¹ a)` and constant term
-- `β = qInv a - α`. The
-- nonemptiness hypothesis gives `β ≥ 0`, so the closed positively homogeneous hull is obtained by
-- minimizing `(1 / (2 * λ)) ⟨xStar, Q⁻¹ xStar⟩ + ⟨b, xStar⟩ + λ β` over `λ > 0`, which yields the
-- displayed affine-plus-square-root expression.
/-- Text 13.5.2: if `C = {x | q x + ⟪a, x⟫ + α ≤ 0}`, i.e.
`C = {x | (1 / 2) ⟪x, Qx⟫ + ⟪a, x⟫ + α ≤ 0}`, with `Q` positive definite and `C` nonempty, then
the support function of `C` is the affine-plus-square-root expression obtained from `Q⁻¹`. -/
theorem supportFunction_ellipticSublevelSet_eq
    (xStar : E) (hQ : Q.PosDef) (hC : Set.Nonempty C) :
    δᵛ(xStar | C) =
      (⟪b, xStar⟫ +
          Real.sqrt (2 * β * ⟪xStar, (Q⁻¹).toEuclideanLin xStar⟫) :
        EReal) :=
  sorry

end
