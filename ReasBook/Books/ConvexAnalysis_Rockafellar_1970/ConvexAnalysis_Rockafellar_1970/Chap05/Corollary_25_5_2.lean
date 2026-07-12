import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_5

noncomputable section

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 25.5.2 states that the differentiability locus `D` from Theorem 25.5
  is a `G_delta` subset of `interior (dom(f))`.
- `core/canonical`: the owner abstractions are mathlib's `IsGδ`, the ambient interior
  `interior (dom(f))`, and the Chapter 25 owner
  `Function.differentiabilitySetWithinInteriorDom`.
- `bridge/view`: the chapter owner from Theorem 25.5 already fixes the differentiability locus as
  the intrinsic owner `differentiabilitySetWithinInteriorDom f`; any coordinate-direction argument
  from Theorems 25.2 and 25.4 is only an internal route to this owner, not a second public
  surface.

Domain-style sampling used here:
- `Function.HasLinearDirectionalDerivativeAt` from `Chap05.Theorem_25_2`;
- `Function.twoSidedDirectionalDerivativeSet` from `Chap05.Theorem_25_4`;
- `Function.differentiabilitySetWithinInteriorDom` from `Chap05.Theorem_25_5`;
- `IsGδ.setOf_continuousAt` from `Mathlib/Topology/GDelta/MetrizableSpace`;
- `IsGδ.iInter` from mathlib's `Topology/GDelta`.

Primitive data vs derived API:
- primitive source data: a proper convex function `f : E → WithBotTop 𝕜`;
- primitive owner surfaces: `twoSidedDirectionalDerivativeSet f y` in one fixed direction and
  `differentiabilitySetWithinInteriorDom f`;
- derived API: the `IsGδ` conclusions for those intrinsic subtype sets.

Ambient-assumption minimization:
- no inner-product structure appears in the public owner
  `differentiabilitySetWithinInteriorDom f`;
- the surrounding Chapter 25 owner theorem `Function.dense_differentiabilitySetWithinInteriorDom`
  already lives on finite-dimensional normed spaces over `𝕜`, so this corollary should remain on that
  same ambient layer instead of re-specializing to Euclidean gradient infrastructure.

Layer target: `core/canonical`; the corollary stays directly on the differentiability-locus owner
from Theorem 25.5 rather than reopening a coordinate-level public interface.
-/

-- Proof sketch: first show that for each fixed direction `y`, the owner
-- `twoSidedDirectionalDerivativeSet f y` is `G_delta`; then express the intrinsic
-- differentiability locus `differentiabilitySetWithinInteriorDom f` as the finite intersection of
-- these owner sets along a finite basis and apply `IsGδ.iInter`.
/-- For a fixed direction, the intrinsic two-sided directional-derivative locus from Theorem 25.4
is a `G_delta` subset of `interior (dom(f))`. -/
theorem isGδ_twoSidedDirectionalDerivativeSet
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) (y : E) :
    IsGδ (twoSidedDirectionalDerivativeSet f y) := sorry

private theorem differentiabilitySetWithinInteriorDom_eq_iInter_twoSidedDirectionalDerivativeSet
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    differentiabilitySetWithinInteriorDom f =
      ⋂ i, twoSidedDirectionalDerivativeSet f ((Module.finBasis 𝕜 E) i) := sorry

/-- Corollary 25.5.2: for a proper convex function on a finite-dimensional normed space over `𝕜`,
the intrinsic Rockafellar locus in `interior (dom(f))` is a `G_delta` subset. -/
theorem isGδ_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    IsGδ (differentiabilitySetWithinInteriorDom f) := by
  rw [differentiabilitySetWithinInteriorDom_eq_iInter_twoSidedDirectionalDerivativeSet
    hf_proper hf_convex]
  exact IsGδ.iInter fun i ↦
    isGδ_twoSidedDirectionalDerivativeSet hf_proper hf_convex ((Module.finBasis 𝕜 E) i)

end Function

end
