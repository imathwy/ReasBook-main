import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.2 states that the function `f = conv(g)` introduced in Text 5.5.1 is
  convex.
- `core/canonical`: the owner abstraction for the conclusion is the chapter predicate
  `Function.IsConvex : (E → WithBotTop 𝕜) → Prop` from Theorem 4.2.
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

/-- Helper for Text 5.5.2: import-safe owner for the convex hull of the epigraph of `g`. -/
def convexEpigraph (g : E → WithBotTop 𝕜) : Set (E × 𝕜) :=
  _root_.convexHull 𝕜 (epi g)

/-- Helper for Text 5.5.2: import-safe owner for Rockafellar's function convex hull `conv(g)`. -/
def convexHull (g : E → WithBotTop 𝕜) : E → WithBotTop 𝕜 :=
  verticalInfimum (Function.convexEpigraph (𝕜 := 𝕜) g)

/-- Helper for Text 5.5.2: Rockafellar notation for the function convex hull. -/
notation:max "conv(" g ")" => Function.convexHull g

-- Route correction: `Text_5_5_1` duplicates the `verticalInfimum` owner from `Theorem_5_3`,
-- so this file keeps the minimal Text 5.5.1 owner surface locally and still follows the same
-- theorem-5.3 proof route.
-- Proof sketch: rewrite `conv(g)` to the vertical infimum of the convex hull of `epi g`,
-- then apply Theorem 5.3 to that convex set.
/-- Text 5.5.2: the convex hull `conv(g)` of an extended-ordered-valued function `g` is convex. -/
theorem isConvex_conv (g : E → WithBotTop 𝕜) : (conv(g)).IsConvex 𝕜 := by
  -- First identify `conv(g)` with the vertical infimum of the convex hull of `epi g)`.
  rw [Function.convexHull]
  -- Then invoke Theorem 5.3 on the convex hull of the epigraph.
  exact Function.isConvex_verticalInfimum <| by
    simpa [Function.convexEpigraph] using (convex_convexHull 𝕜 (epi g))

end Function

end
