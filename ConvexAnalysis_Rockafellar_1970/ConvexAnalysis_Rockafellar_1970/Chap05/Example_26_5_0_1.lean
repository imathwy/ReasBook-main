import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Example_26_2_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_26_5

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

local notation "R2" => ℝ × ℝ

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example computes the dual region `C⋆`, the explicit dual value formula on
  `C⋆`, and concludes that this explicit dual branch is again of Legendre type.
- `core/canonical`: the built owner abstractions available in the current item-per-file import
  closure are `Function.IsLegendreTypeOn`, Fenchel conjugation `f⋆`, the effective-domain owner
  `dom(·)`, the finite real branch `realBranch`, the gradient owner `∇`, the Chapter 26 duality
  theorem
  `Function.IsClosedProperConvex`
  `.isLegendreTypeOn_interior_dom_iff_convexConjugate_isLegendreTypeOn_interior_dom`,
  and the upstream primal example owners `quadraticSqrtExampleFunction` and
  `quadraticSqrtExamplePositiveQuadrant`.
- `bridge/view`: the concrete inequalities defining `C⋆` and the closed formula
  `x⋆ ↦ 1 / (√(-2 ξ₁⋆) - ξ₂⋆)` are the source-facing bridge back to those canonical owners.

Domain-style sampling used here:
- `quadraticSqrtExampleFunction` and `quadraticSqrtExamplePositiveQuadrant` from
  `Example_26_2_1`;
- `Function.IsLegendreTypeOn` from `Text_26_5_0_2`;
- `Function.IsClosedProperConvex`
  `.isLegendreTypeOn_interior_dom_iff_convexConjugate_isLegendreTypeOn_interior_dom` from
  `Theorem_26_5`;
- `Function.IsClosedProperConvex`
  `.convexConjugate_realBranch_gradient_eq_inner_sub_of_mem_interior_dom`
  from `Text_26_4_1_2`.

Primitive data vs derived API:
- primitive source-facing data: the explicit dual region and the explicit dual real branch,
  together with the already-defined primal example from `Example_26_2_1`;
- derived API: the gradient-image computation, the identification of the dual region with
  `interior (dom(f⋆))`, the explicit conjugate-value formula, and the final Legendre-type
  conclusion.

Layer target: `source-facing`.
-/

local notation "C" => quadraticSqrtExamplePositiveQuadrant
local notation "f" => quadraticSqrtExampleFunction
local notation "fStar" => ((f⋆ : R2 → EReal))

/-- The explicit dual region
`C⋆ = { (ξ₁⋆, ξ₂⋆) | ξ₁⋆ < 0, ξ₂⋆ < √(-2 ξ₁⋆) }` for the quadratic-over-linear minus square-root
example. -/
def quadraticSqrtExampleDualRegion : Set R2 :=
  {ξStar : R2 | ξStar.1 < 0 ∧ ξStar.2 < Real.sqrt (-2 * ξStar.1)}

local notation "CStar" => quadraticSqrtExampleDualRegion

/-- The explicit dual real branch
`x⋆ ↦ 1 / (√(-2 ξ₁⋆) - ξ₂⋆)` on the dual region `C⋆`. -/
def quadraticSqrtExampleDualRealBranch (ξStar : R2) : ℝ :=
  1 / (Real.sqrt (-2 * ξStar.1) - ξStar.2)

-- Proof sketch: compute the gradient of the finite branch from the explicit formula for
-- `quadraticSqrtExampleFunction.realBranch` on the open positive quadrant.
-- The first coordinate forces
-- `ξ₁⋆ < 0`, and eliminating the primal variables from the two gradient coordinates yields exactly
-- `ξ₂⋆ < √(-2 ξ₁⋆)`. Conversely, solve the gradient equations to reconstruct a point of the open
-- positive quadrant with the prescribed image.
/-- The image of the gradient map for the quadratic-over-linear minus square-root example is the
explicit dual region `C⋆`. -/
theorem quadraticSqrtExample_gradientImage_eq_dualRegion :
    Set.range (fun x : C ↦
      ∇ (f).realBranch (x : R2)) =
      CStar := sorry

-- Proof sketch: the previous theorem identifies the gradient image with the explicit dual region.
-- The canonical Fenchel-conjugate domain on the dual side is
-- `interior (dom(quadraticSqrtExampleFunction⋆))`,
-- and the example asserts that this interior domain is exactly the computed region `C⋆`.
/-- The explicit dual region is the interior of the effective domain of the Fenchel conjugate of
the quadratic-over-linear minus square-root example. -/
theorem quadraticSqrtExampleDualRegion_eq_interior_dom_convexConjugate :
    CStar = interior (dom(fStar)) := sorry

-- Proof sketch: apply the Chapter 26 owner theorem for Fenchel conjugates of Legendre-type
-- pairs to the primal example, then specialize the dual side to the canonical conjugate pair
-- `(interior (dom(f⋆)), f⋆.realBranch)`.
/-- The canonical Fenchel-conjugate dual pair for the quadratic-over-linear minus square-root
example is of Legendre type on `interior (dom(f⋆))`. This is the owner-side Chapter 26 statement
before transporting to the explicit region `C⋆` and explicit branch formula. -/
theorem quadraticSqrtExample_convexConjugate_isLegendreTypeOn_interior_dom :
    Function.IsLegendreTypeOn (interior (dom(fStar))) (fStar).realBranch := sorry

-- Proof sketch: for `ξStar ∈ C⋆`, solve the gradient equations for the unique primal point
-- `x ∈ quadraticSqrtExamplePositiveQuadrant` with
-- `∇ f.realBranch x = ξStar`, then apply
-- Fenchel-Young equality to compute the conjugate value as the affine defect. Substituting the
-- solved coordinates gives the closed formula
-- `1 / (√(-2 ξ₁⋆) - ξ₂⋆)`.
/-- On the explicit dual region `C⋆`, the real branch of the Fenchel conjugate of the
quadratic-over-linear minus square-root example is
`x⋆ ↦ 1 / (√(-2 ξ₁⋆) - ξ₂⋆)`. -/
theorem quadraticSqrtExample_convexConjugate_realBranch_eq_dualRealBranch
    {ξStar : R2} (hξStar : ξStar ∈ CStar) :
    (fStar).realBranch ξStar = quadraticSqrtExampleDualRealBranch ξStar := sorry

-- Proof sketch: start from the canonical conjugate-pair theorem
-- `quadraticSqrtExample_convexConjugate_isLegendreTypeOn_interior_dom`, then transport that owner
-- statement across `quadraticSqrtExampleDualRegion_eq_interior_dom_convexConjugate` and
-- `quadraticSqrtExample_convexConjugate_realBranch_eq_dualRealBranch`.
/-- Example 26.5.0.1: for the quadratic-over-linear minus square-root example, the explicit dual
pair with
`C⋆ = { (ξ₁⋆, ξ₂⋆) | ξ₁⋆ < 0, ξ₂⋆ < √(-2 ξ₁⋆) }`
and
`f⋆(x⋆) = 1 / (√(-2 ξ₁⋆) - ξ₂⋆)`
is of Legendre type. The source-facing branch identification with the Fenchel conjugate is the
companion theorem `quadraticSqrtExample_convexConjugate_realBranch_eq_dualRealBranch`, while the
owner-side canonical statement is
`quadraticSqrtExample_convexConjugate_isLegendreTypeOn_interior_dom`. -/
theorem quadraticSqrtExampleDualPair_isLegendreTypeOn :
    Function.IsLegendreTypeOn CStar quadraticSqrtExampleDualRealBranch := sorry
