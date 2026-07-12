import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1

-- Declarations for this item will be appended below by the statement pipeline.

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
