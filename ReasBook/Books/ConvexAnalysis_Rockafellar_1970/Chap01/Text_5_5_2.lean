import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.2 states that the function `f = conv(g)` introduced in Text 5.5.1 is
  convex.
- `core/canonical`: the owner abstraction for the conclusion is the chapter predicate
  `Function.IsConvex : (E → WithTopBot 𝕜) → Prop` from Theorem 4.2.
- `bridge/view`: the source-facing owner `conv(g)` from Text 5.5.1 is defined canonically as
  `Function.verticalInfimum (Function.convexEpigraph g)`.
- Primitive data vs derived API: the function `conv(g)` is primitive upstream; its convexity is
  the derived statement here.
- Ambient minimization: the statement uses only the chapter owners `Function.convexHull`,
  `Function.verticalInfimum`, and `Function.IsConvex`, all of which already live on an arbitrary
  additive commutative `𝕜`-module `E`, so any concrete finite-dimensional coordinate model would be
  an unnecessary specialization here.
- Domain-style sampling used here: `Function.IsConvex`, `Function.convexHull`,
  `Function.convexEpigraph`, `Function.isConvex_verticalInfimum`,
  and `_root_.convexHull`.
- Layer target: `source-facing`; this file keeps the textbook theorem about `conv(g)` and reuses
  the earlier chapter owner declarations directly.
-/

namespace Function

-- Proof sketch: rewrite `conv(g)` to the vertical infimum of the convex hull of `epi g`,
-- then apply Theorem 5.3 to that convex set.
/-- Text 5.5.2: the convex hull `conv(g)` of an extended-ordered-valued function `g` is convex. -/
theorem isConvex_conv (g : E → WithTopBot 𝕜) : (conv(g)).IsConvex 𝕜 := by
  -- First identify `conv(g)` with the vertical infimum of the convex hull of `epi g)`.
  rw [Function.convexHull]
  -- Then invoke Theorem 5.3 on the convex hull of the epigraph.
  exact Function.isConvex_verticalInfimum <| by
    simpa [Function.convexEpigraph] using (convex_convexHull 𝕜 (epi g))

end Function

end
