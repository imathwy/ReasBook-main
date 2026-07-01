import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_19_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 19.2 says that the Fenchel conjugate of a polyhedral convex function on
  a finite-dimensional pairing space is again polyhedral convex on the dual side.
- `core/canonical`: the primitive owner theorem in this file is on
  `Function.HasFinitelyGeneratedConvexEpigraph`; the source-facing theorem is then obtained by
  the Chapter 19.1.2 bridge between polyhedral and finitely generated epigraph owners.
- `bridge/view`: Corollary 19.1.2 already identifies the source-facing polyhedrality predicate
  `Function.HasPolyhedralEpigraph` with
  `Function.HasFinitelyGeneratedConvexEpigraph`, so this file reuses that bridge instead of
  introducing a parallel wrapper owner.

Domain-style sampling used here:
- conjugate notation `f⋆`;
- `Function.HasFinitelyGeneratedConvexEpigraph`.
- `Function.HasPolyhedralEpigraph.hasFinitelyGeneratedConvexEpigraph`;
- `Function.HasFinitelyGeneratedConvexEpigraph.hasPolyhedralEpigraph`.

Primitive data vs derived API:
- primitive input: the function `f : X → WithTopBot 𝕜` on the chapter's ordered extended codomain;
- core owner datum and output: finite generation of `epi f` and `epi (f⋆)`;
- source-facing bridge input/output: polyhedral epigraphs of `f` and `f⋆` on the dual pairing
  space.

Layer target: core theorem first, then source-facing bridge theorem.
-/

variable {𝕜 : Type*} {X : Type*} {XStar : Type*}

namespace Function.HasFinitelyGeneratedConvexEpigraph

variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasPairing X XStar 𝕜]

/-- Theorem 19.2, core owner form: finitely generated convex epigraphs are preserved by Fenchel
conjugation at the primitive pairing layer. -/
theorem convexConjugate
    {f : X → WithTopBot 𝕜} (hf : f.HasFinitelyGeneratedConvexEpigraph) :
    (f⋆).HasFinitelyGeneratedConvexEpigraph := by
  sorry

end Function.HasFinitelyGeneratedConvexEpigraph

section PolyhedralBridge

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasPairing X XStar 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X]
  [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
  [FiniteDimensional 𝕜 XStar]

namespace Function.HasPolyhedralEpigraph

/-- Theorem 19.2, source-facing owner form: the Fenchel conjugate of a function with polyhedral
epigraph is again polyhedral at the intrinsic Chapter 19 owner layer. -/
theorem convexConjugate
    {f : X → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) :
    (f⋆).HasPolyhedralEpigraph := by
  exact (hf.hasFinitelyGeneratedConvexEpigraph.convexConjugate).hasPolyhedralEpigraph

end Function.HasPolyhedralEpigraph

end PolyhedralBridge

end
