import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.23: a bifunction is polyhedral exactly when its
graph function has polyhedral epigraph in the Chapter 19 owner sense. -/
scoped notation:70 "polyᵇ " F =>
  Function.HasPolyhedralEpigraph (Function.uncurry F)

end Rockafellar

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Semiring 𝕜] [Preorder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.23 says that a bifunction is polyhedral exactly when its graph
  function is polyhedral.
- `core/canonical`: Definition 6.29.2 already fixes the graph function as `Function.uncurry F`,
  and Chapter 19 already fixes function-side polyhedrality by `Function.HasPolyhedralEpigraph`.
- `bridge/view`: the textbook bifunction wording is just the canonical owner expression
  `((Function.uncurry F).HasPolyhedralEpigraph)`; no separate `Bifunction.IsPolyhedral` owner is
  needed.

Domain-style sampling used here:
- `Function.uncurry` from `Definition_6_29_2`;
- `Function.HasPolyhedralEpigraph` from `Chap04.Text_19_0_8`;
- `Function.HasPolyhedralEpigraph.isPolyhedral` from `Chap04.Text_19_0_8`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive ambient structure: additive/module structures on the bifunction variables `U` and `X`
  (with the product ambient inferred canonically);
- canonical owner surface: `(Function.uncurry F).HasPolyhedralEpigraph`;
- derived API: convexity and other epigraph-side consequences should continue to come from the
  Chapter 19 owner namespace, not from a parallel bifunction wrapper.

Layer target: `core/canonical` source-facing theorem surface.
-/

variable (F : U → X → WithBotTop 𝕜)

/-- Definition 6.29.23, source-facing specification:
a bifunction is polyhedral exactly when its graph function has a polyhedral epigraph in the
canonical Chapter 19 owner `Function.HasPolyhedralEpigraph`. -/
@[simp] theorem poly_iff_uncurry_hasPolyhedralEpigraph :
    (polyᵇ F) ↔ (Function.uncurry F).HasPolyhedralEpigraph :=
  Iff.rfl

end

end Bifunction
