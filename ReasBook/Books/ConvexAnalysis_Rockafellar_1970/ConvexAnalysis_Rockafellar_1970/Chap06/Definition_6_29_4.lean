import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.4: a bifunction is convex exactly when its graph
function is convex. -/
scoped[Rockafellar] notation:70 "convᵇ[" 𝕜 "](" F ")" =>
  Function.IsConvex 𝕜 (Function.uncurry F)

end Rockafellar

section

open scoped Rockafellar

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.4 introduces the phrase “convex bifunction” by requiring the
  graph function from Definition 6.29.2 to be convex on the product space.
- `core/canonical`: the project's convexity owner is already `Function.IsConvex 𝕜`, and
  Definition 6.29.2 already identifies the graph function of `F` with the canonical uncurried map
  `Function.uncurry F`, whose canonical owner surface is `(Function.uncurry F).IsConvex 𝕜`.
- `bridge/view`: no separate `Bifunction.IsConvex` owner should be introduced here; the textbook
  notion is exactly the canonical owner applied to `Function.uncurry F`, and the source-facing
  shorthand is the scoped notation `convᵇ[𝕜](F)`.

Domain-style sampling used here:
- `Function.IsConvexOn` and `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.isConvex_iff_convex_epigraph` from `Chap01.Theorem_4_2`;
- `Function.uncurry` recalled in `Definition_6_29_2`;
- scoped notation `convᵇ[𝕜](F)`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithTopBot α`;
- primitive ambient structure: additive/scalar structures on `U` and `X`, inducing the canonical
  product structure on `U × X`;
- canonical owner surface: `(Function.uncurry F).IsConvex 𝕜`;
- source-facing notation surface: `convᵇ[𝕜](F)`;
- no extra owner wrapper is needed, because the source definition is only this direct owner usage.

Layer target: `core/canonical recall/use`.
-/

variable (F : U → X → WithTopBot α)

recall Function.IsConvex
recall Function.isConvex_iff_convex_epigraph

/- Definition 6.29.4: a bifunction is convex exactly when its graph function from
Definition 6.29.2, namely `Function.uncurry F`, is convex on the product space. The canonical owner
expression for this notion is `(Function.uncurry F).IsConvex 𝕜`, with source-facing notation
`convᵇ[𝕜](F)`. -/
#check (convᵇ[𝕜](F) : Prop)

end
