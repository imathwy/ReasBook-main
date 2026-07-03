import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_26_5_0_1 (from Chap05) -/
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

/-! ### Text_26_5_0_2 (from Chap05) -/
section

open Filter
open scoped Gradient

variable {E : Type*}

/-!
Source/core/bridge triage:

- `source-facing`: Text 26.5.0.2 names the class of pairs `(C, f)` singled out by the Legendre
  transformation discussion: `C` is a nonempty open set, `f` is strictly convex on `C`, and the
  pair `(C, f)` satisfies the essential-smoothness conditions `(a)(b)(c)` on `C`.
- `core/canonical`: the owner abstraction for the shared `(a)(b)(c)` data is now
  `Function.IsEssentiallySmoothOn`, while the extra Legendre-type data are `IsOpen` and
  `StrictConvexOn`.
- `bridge/view`: Rockafellar's phrase "convex function of Legendre type" is therefore a thin
  extension of the Chapter 26 owner `Function.IsEssentiallySmoothOn`, not a parallel record
  restating differentiability and boundary blow-up fields.

Domain-style sampling used here:
- `Function.IsEssentiallySmoothOn` from Definition 26.1.1;
- `StrictConvexOn` from mathlib's convex-function owner layer;
- `Function.IsClosedProperConvex` from Chapter 12 as the ambient closed/proper/convex owner used
  downstream when this source-facing notion is applied to `interior dom(f)`.

Primitive data vs derived API:
- primitive inputs: the set `C` and the scalar-valued function `f`;
- primitive owner fields: openness of `C`, strict convexity of `f` on `C`, and the inherited
  `Function.IsEssentiallySmoothOn C f` data;
- derived API: convexity of `C`, which already comes canonically from `StrictConvexOn` and is
  therefore reused directly instead of being repackaged as a parallel owner lemma.

Layer target: `source-facing`.
-/

namespace Function

section NormedSpace

variable [SeminormedAddCommGroup E]

/-- Text 26.5.0.2: a pair `(C, f)` is of Legendre type when `C` is open, `f` is strictly convex
and the pair satisfies the essential-smoothness conditions `(a)(b)(c)` on `C`. -/
@[mk_iff] class IsLegendreTypeOn {𝕜 : Type*}
    [NormedLinearOrderedField 𝕜]
    [NormedSpace 𝕜 E] (C : Set E) (f : E → 𝕜) :
    Prop extends IsEssentiallySmoothOn C f where
  isOpen : IsOpen C
  strictConvexOn : StrictConvexOn 𝕜 C f

namespace IsLegendreTypeOn

/-- A Legendre-type pair has a convex source set, canonically inherited from strict convexity. -/
theorem convex {𝕜 : Type*}
    [NormedLinearOrderedField 𝕜]
    [NormedSpace 𝕜 E] {C : Set E} {f : E → 𝕜} (hf : IsLegendreTypeOn C f) : Convex 𝕜 C :=
  hf.strictConvexOn.1

end IsLegendreTypeOn

end NormedSpace

namespace IsLegendreTypeOn

section InnerProductBridge

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- On a Legendre-type pair, the boundary blow-up clause can be stated with the ambient gradient
because the source set is open. -/
theorem boundaryGradientNorm_tendstoTop {C : Set E} {f : E → ℝ} (hf : IsLegendreTypeOn C f)
    {x : E} (hx : x ∈ frontier C) :
    Tendsto (fun y : E ↦ ‖∇ f y‖) (nhdsWithin x C) atTop := by
  let hs : IsEssentiallySmoothOn C f := hf.toIsEssentiallySmoothOn
  exact hs.boundaryGradientNorm_tendstoTop hf.isOpen hx

end InnerProductBridge

end IsLegendreTypeOn

end Function

end

/-! ### Theorem_26_5 (from Chap05) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 26.5 compares the Legendre-type pairs
  `(interior (dom(f)), f.realBranch)` and `(interior (dom(f⋆)), (f⋆).realBranch)`, then records
  the classical Legendre-value formulas and the inverse/homeomorphism behavior of the two gradient
  maps.
- `core/canonical`: the chapter owners already in place are
  `Function.IsLegendreTypeOn`, Fenchel conjugation `f⋆`, the derivative-image bridge from
  `Text_26_4_0_2`, and the gradient owner `∇`.
- `bridge/view`: the homeomorphism is exposed as the explicit gradient map between the two
  interior-domain subtypes; the two value identities are the source-facing bridge back to the
  classical Legendre-conjugate reading.

Domain-style sampling used here:
- `Function.IsLegendreTypeOn` from `Text_26_5_0_2`;
- `Function.convexConjugate_toWithTopBotOn_imageFactorization_eq_apply_sub` from
  `Text_26_4_0_2`;
- `biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom` from
  `Definition_26_4_1_4`;
- `convexConjugate_toWithTopBotOn_gradient_eq_inner_sub` from `Text_26_0_1`.

Primitive data vs derived API:
- primitive source input: a closed proper convex function `f : E → EReal`;
- primitive owner surface: the two Legendre-type predicates on `interior (dom(f))` and
  `interior (dom(f⋆))`;
- derived API: the gradient maps between these two interiors, their homeomorphism package, and the
  two Legendre-value identities.

Layer target:
- the labeled theorem is `source-facing`, stated directly on the chapter owner
  `Function.IsLegendreTypeOn`;
- the remaining declarations are `bridge/view` companions spelling out the gradient/homeomorphism
  and Legendre-value consequences.
-/

namespace Function.IsClosedProperConvex

variable {f : E → EReal}

local notation "C" => interior (dom(f))
local notation "fStar" => ((f⋆ : E → EReal))
local notation "CStar" => interior (dom(fStar))

-- Proof sketch: rewrite Legendre type on `interior (dom(f))` as bi-uniqueness of
-- `_root_.subdifferentialGraph f` via
-- `biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom`.
-- The relation inverse theorem `∂f⋆ = (∂f)⁻¹` preserves bi-uniqueness, so the same criterion for
-- `f⋆` gives the converse direction.
/-- Theorem 26.5: for a closed proper convex function, the primal pair
`(interior (dom(f)), f.realBranch)` is of Legendre type if and only if the dual pair
`(interior (dom(f⋆)), f⋆.realBranch)` is of Legendre type. -/
theorem isLegendreTypeOn_interior_dom_iff_convexConjugate_isLegendreTypeOn_interior_dom
    (hf : f.IsClosedProperConvex) :
    Function.IsLegendreTypeOn C f.realBranch ↔
      Function.IsLegendreTypeOn CStar (fStar).realBranch := sorry

-- Proof sketch: under the Legendre-type hypothesis, Theorem 26.1 identifies `∂f(x)` with the
-- singleton `{∇ f.realBranch x}` on `interior (dom(f))`, while Theorem 23.5 and Corollary 26.4.1
-- identify the range of this single-valued subdifferential with `interior (dom(f⋆))`.
/-- The primal gradient maps `interior (dom(f))` into the dual interior domain
`interior (dom(f⋆))` whenever the primal pair is of Legendre type. -/
theorem mapsTo_gradient_realBranch_interior_dom_convexConjugate_interior_dom_of_isLegendreTypeOn
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    : Set.MapsTo (fun x ↦ ∇ f.realBranch x) C CStar := sorry

-- Proof sketch: apply the previous theorem to `f⋆`, using the main equivalence above to transport
-- the Legendre-type hypothesis from `f` to `f⋆`.
/-- The dual gradient maps `interior (dom(f⋆))` back into the primal interior domain
`interior (dom(f))` whenever the primal pair is of Legendre type. -/
theorem mapsTo_gradient_convexConjugate_realBranch_interior_dom_interior_dom_of_isLegendreTypeOn
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    : Set.MapsTo (fun xStar ↦ ∇ (fStar).realBranch xStar) CStar C :=
  sorry

/-- The primal gradient map, restricted to the interior of the effective domain and viewed as a
map into the interior of the effective domain of the Fenchel conjugate. -/
private def gradientMapInteriorDomToConvexConjugateInteriorDom
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    : C → CStar :=
  Set.MapsTo.restrict (fun x ↦ ∇ f.realBranch x) C CStar
    (mapsTo_gradient_realBranch_interior_dom_convexConjugate_interior_dom_of_isLegendreTypeOn
      hf hleg)

/-- The dual gradient map, restricted to the interior of the effective domain of the Fenchel
conjugate and viewed as a map back into the primal interior domain. -/
private def gradientMapConvexConjugateInteriorDomToInteriorDom
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    : CStar → C :=
  Set.MapsTo.restrict (fun xStar ↦ ∇ (fStar).realBranch xStar) CStar C
    (mapsTo_gradient_convexConjugate_realBranch_interior_dom_interior_dom_of_isLegendreTypeOn
      hf hleg)

-- Proof sketch: use Theorem 23.5 to identify `∂f⋆` with the inverse of `∂f`, then use the
-- singleton-gradient descriptions from Theorem 26.1 on both sides. Since the two domains are
-- exactly the interiors of `dom(f)` and `dom(f⋆)`, composing the dual gradient with the primal
-- gradient gives the identity on the primal interior domain.
/-- The dual gradient map is a left inverse to the primal gradient map on the two interior domains.
-/
private theorem leftInverse_gradientMapConvexConjugateInteriorDomToInteriorDom
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    :
    Function.LeftInverse
      (gradientMapConvexConjugateInteriorDomToInteriorDom hf hleg)
      (gradientMapInteriorDomToConvexConjugateInteriorDom hf hleg) := sorry

-- Proof sketch: repeat the previous argument after swapping `f` and `f⋆`, using the equivalence
-- of Legendre type from the main theorem to stay in the same hypothesis surface.
/-- The dual gradient map is also a right inverse to the primal gradient map on the two interior
domains. -/
private theorem rightInverse_gradientMapConvexConjugateInteriorDomToInteriorDom
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    :
    Function.RightInverse
      (gradientMapConvexConjugateInteriorDomToInteriorDom hf hleg)
      (gradientMapInteriorDomToConvexConjugateInteriorDom hf hleg) := sorry

-- Proof sketch: Theorem 25.5 gives continuity of the primal gradient on the differentiability
-- locus, and a Legendre-type pair is differentiable on all of `interior (dom(f))`. The target
-- membership is already built into the subtype-valued map.
/-- The restricted primal gradient map between the two interior-domain subtypes is continuous. -/
private theorem continuous_gradientMapInteriorDomToConvexConjugateInteriorDom
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    :
    Continuous (gradientMapInteriorDomToConvexConjugateInteriorDom hf hleg) := sorry

-- Proof sketch: apply the previous continuity argument to `f⋆`, transporting the Legendre-type
-- hypothesis by the main equivalence theorem.
/-- The restricted dual gradient map between the two interior-domain subtypes is continuous. -/
private theorem continuous_gradientMapConvexConjugateInteriorDomToInteriorDom
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    :
    Continuous (gradientMapConvexConjugateInteriorDomToInteriorDom hf hleg) := sorry

/-- The canonical homeomorphism between the two interior-domain subtypes furnished by the primal
and dual gradient maps under the Legendre-type hypothesis. This is the source statement that
`∇ f` is a homeomorphism from `interior (dom(f))` onto `interior (dom(f⋆))`. -/
def gradientHomeomorphInteriorDomToConvexConjugateInteriorDom
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    : C ≃ₜ CStar :=
  { toEquiv :=
      { toFun := gradientMapInteriorDomToConvexConjugateInteriorDom hf hleg
        invFun := gradientMapConvexConjugateInteriorDomToInteriorDom hf hleg
        left_inv := leftInverse_gradientMapConvexConjugateInteriorDomToInteriorDom hf hleg
        right_inv := rightInverse_gradientMapConvexConjugateInteriorDomToInteriorDom hf hleg }
    continuous_toFun := continuous_gradientMapInteriorDomToConvexConjugateInteriorDom hf hleg
    continuous_invFun := continuous_gradientMapConvexConjugateInteriorDomToInteriorDom hf hleg }

-- Proof sketch: specialize the Chapter 26 differentiable Legendre-value formula
-- `convexConjugate_toWithTopBotOn_gradient_eq_inner_sub` to the open convex set `interior (dom(f))`
-- and use that a Legendre-type pair supplies the needed openness, convexity, and differentiability.
/-- Under the Legendre-type hypothesis, the Fenchel conjugate evaluated at the primal gradient is
the classical Legendre affine defect `⟪x, ∇ f.realBranch x⟫ - f.realBranch x`. -/
theorem convexConjugate_realBranch_gradient_eq_inner_sub_of_isLegendreTypeOn
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    {x : E} (hx : x ∈ C) :
    (fStar).realBranch (∇ f.realBranch x) =
      (⟪x, ∇ f.realBranch x⟫ - f.realBranch x : ℝ) := sorry

-- Proof sketch: apply the previous theorem to `f⋆`, using the Legendre-type equivalence to obtain
-- the dual Legendre-type hypothesis and then rewrite `f⋆⋆` back to `f`.
/-- Under the Legendre-type hypothesis, the primal branch evaluated at the dual gradient is the
dual affine defect `⟪xStar, ∇ f⋆.realBranch xStar⟫ - f⋆.realBranch xStar`. This is the converse
Legendre-value identity from Theorem 26.5. -/
theorem realBranch_gradient_convexConjugate_eq_inner_sub_of_isLegendreTypeOn
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    {xStar : E} (hxStar : xStar ∈ CStar) :
    f.realBranch (∇ (fStar).realBranch xStar) =
      (⟪xStar, ∇ (fStar).realBranch xStar⟫ - (fStar).realBranch xStar : ℝ) := sorry

-- Proof sketch: the inverse map in the homeomorphism definition was chosen to be the restricted
-- dual gradient map, so this theorem is the source-facing reformulation of that explicit choice.
/-- The inverse of the primal gradient homeomorphism is the dual gradient map. This is the
source-facing formulation of `∇ f⋆ = (∇ f)⁻¹` on the two interior domains. -/
theorem gradientHomeomorphInteriorDomToConvexConjugateInteriorDom_symm_apply
    (hf : f.IsClosedProperConvex) (hleg : Function.IsLegendreTypeOn C f.realBranch)
    (xStar : CStar) :
    ((gradientHomeomorphInteriorDomToConvexConjugateInteriorDom hf hleg).symm xStar : E) =
      ∇ (fStar).realBranch (xStar : E) := sorry

end Function.IsClosedProperConvex

end
