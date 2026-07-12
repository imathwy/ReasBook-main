import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_1_5
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 20.5 asserts local simpliciality for polyhedral convex sets and for
  polytopes.
- `core/canonical`: the primitive owner is `Set.IsFinitelyGeneratedConvex 𝕜`, because finite
  point/direction generation is the structural data behind the source statements.
- `bridge/view`: the source polyhedral clause is recovered through
  `Set.IsPolyhedral.isFinitelyGeneratedConvex`; the polytope clause is recovered through
  `Set.IsPolytope.isFinitelyGeneratedConvex`.
- Primitive data vs derived API: finite generation is the primitive input, while the two
  source-facing forms are thin corollaries.
- Domain-style sampling used here: `Set.IsLocallySimplicial`, `Set.IsFinitelyGeneratedConvex`,
  `Set.IsPolyhedral.isFinitelyGeneratedConvex`, and `Set.IsPolytope.isFinitelyGeneratedConvex`.
- Ambient refinement: the core owner statement and polytope bridge stay on the weaker intrinsic
  affine-neighborhood layer (ordered module plus ambient topology), while the
  polyhedral clause below uses the stronger Chapter 19 topological bridge only where needed.

Layer target: `core/canonical` on `Set.IsFinitelyGeneratedConvex 𝕜`, with source-facing
polyhedral and polytope results kept as thin owner bridges.
-/

namespace Set.IsFinitelyGeneratedConvex

/-- Core owner theorem for Theorem 20.5: every finitely generated convex set in an ordered
`𝕜`-module with ambient topology is locally simplicial. -/
theorem isLocallySimplicial {C : Set E} (hC : C.IsFinitelyGeneratedConvex 𝕜) :
    C.IsLocallySimplicial 𝕜 := by
  sorry

end Set.IsFinitelyGeneratedConvex

namespace Set.IsPolytope

/-! Theorem 20.5 (2), kept on the core owner layer: no polyhedral-face bridge assumptions are
needed beyond finite generation. -/
/-- Every polytope is locally simplicial, via the canonical finite-generation owner bridge. -/
theorem isLocallySimplicial {C : Set E} (hC : C.IsPolytope 𝕜) :
    C.IsLocallySimplicial 𝕜 :=
  hC.isFinitelyGeneratedConvex.isLocallySimplicial

end Set.IsPolytope

end

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Set.IsPolyhedral

/-- Theorem 20.5 (1): every polyhedral convex set is locally simplicial, obtained by transporting
to the canonical finite-generation owner. -/
theorem isLocallySimplicial {C : Set E} (hC : C.IsPolyhedral 𝕜) :
    C.IsLocallySimplicial 𝕜 :=
  hC.isFinitelyGeneratedConvex.isLocallySimplicial

end Set.IsPolyhedral

end
