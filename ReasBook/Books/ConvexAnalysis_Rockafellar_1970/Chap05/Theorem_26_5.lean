import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_0_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_5_0_2

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
