import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w z

section

open Function

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.29.1 says that convexity of a graph function on a product space
  implies convexity of each slice obtained by fixing the first variable.
- `core/canonical`: the owner is global convexity `Function.IsConvex` of a product function
  `f : U × X → WithBotTop α`; this is the intrinsic level where slicing is defined.
- `bridge/view`: the bifunction form is recovered by taking `f = uncurry F`, so the source
  statement is a direct specialization of the intrinsic product-function slice theorem.

Domain-style sampling used here:
- `Function.IsConvex` from `ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2`;
- `Function.IsConvex.convex_epigraph` from the same file as the owner-level epigraph bridge;
- `uncurry` only as the source-facing bridge back to bifunction notation.

Primitive data vs derived API:
- primitive data: a product function `f : U × X → WithBotTop α`;
- primitive owner hypothesis: `f.IsConvex 𝕜`;
- derived conclusion: convexity of every fixed-first-coordinate slice
  `(fun x ↦ f (u, x)).IsConvex 𝕜`.

Layer target: `bridge/view`, with the theorem surface at the intrinsic owner level and bifunction
phrasing treated as a direct specialization.
-/

namespace Function.IsConvex

/-- Proposition 6.29.1, intrinsic owner form: if `f : U × X → [-∞,+∞]` is convex, then every
slice obtained by fixing the first coordinate is convex. -/
-- Proof sketch: fix `u : U`. Apply convexity of `f` to the two epigraph points
-- `((u, x₁), r₁)` and `((u, x₂), r₂)`. Since `u` is preserved by convex combinations in the
-- module `U`, the resulting epigraph point is exactly the one for the slice `x ↦ f (u, x)`.
theorem slice
    {f : U × X → WithBotTop α} (hf : f.IsConvex 𝕜) :
    ∀ u : U, (fun x ↦ f (u, x)).IsConvex 𝕜 := by
  intro u
  rw [isConvex_iff_convex_epigraph]
  let S : Set ((U × X) × α) := {r | f r.1 ≤ r.2}
  have hS : Convex 𝕜 S := by
    simpa [S] using hf.convex_epigraph
  intro p hp q hq a b ha hb hab
  have hp' : (((u, p.1), p.2) : (U × X) × α) ∈ S := by
    simpa [S] using hp
  have hq' : (((u, q.1), q.2) : (U × X) × α) ∈ S := by
    simpa [S] using hq
  simpa [S, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab] using
    hS hp' hq' ha hb hab

/-- Proposition 6.29.1, source-facing bridge form: if the graph function `uncurry F` is
convex, then each slice `F u` is convex. -/
theorem slice_uncurry
    {F : U → X → WithBotTop α} (hF : (uncurry F).IsConvex 𝕜) :
    ∀ u : U, (F u).IsConvex 𝕜 := by
  intro u
  simpa [uncurry] using hF.slice u

end Function.IsConvex

end
