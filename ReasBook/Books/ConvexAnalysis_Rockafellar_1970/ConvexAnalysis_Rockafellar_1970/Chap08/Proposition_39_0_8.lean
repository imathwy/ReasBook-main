import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_39_0_2

open scoped SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.8 states that if `C` is convex and `A` is a convex process,
  then `AC := ⋃ u ∈ C, Au` is convex.
- `core/canonical`: the chapter owner for a convex process is `A.IsConvexProcess R` on
  `A : SetRel U X`, and the canonical owner for applying a relation to a set is `A.image C`.
  The primitive owner theorem for convexity of relation images under graph convexity is upstream
  as `SetRel.convex_image_of_convex` in Proposition 39.0.2.
- `bridge/view`: the source union-of-fibers formula is represented through canonical
  singleton-fiber notation `A[[u]]` (equivalently `A.image {u}`) together with
  `SetRel.image_eq_biUnion`.

Primary mathematical domain:
- convex processes acting on convex sets through relation image.

Domain-style sampling used here:
- `SetRel.image` and `SetRel.mem_image` from `Mathlib.Data.Rel`;
- `SetRel.image_eq_biUnion` for rewriting relation images as unions of fibers;
- `SetRel.convex_image_of_convex` from `Chap08.Proposition_39_0_2`.

Primitive data vs derived API:
- primitive owner data: `A : SetRel U X`, `C : Set U`;
- primitive graph assumption: `hA : Convex R A`;
- source-facing corollary assumption: `hA : A.IsConvexProcess R`;
- derived API: convexity of `A.image C`, and the source-facing convex-process corollaries.

Layer target:
- `core/canonical`: reuse upstream `SetRel.convex_image_of_convex` on the primitive
  graph-convex layer;
- `bridge/view`: canonical fiber-union form via singleton-fiber notation `A[[u]]` and
  `SetRel.image_eq_biUnion`;
- `source-facing`: thin convex-process specialization built on the primitive owner theorem.
-/

section ImageConvexityPrimitive

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X} {C : Set U}

-- Proof sketch: rewrite `A.image C` as the canonical biUnion of singleton fibers, then reuse the
-- primitive image-convexity owner from Proposition 39.0.2.
/-- Primitive owner bridge for Proposition 39.0.8: if the graph of `A` is convex and `C` is
convex, then the source fiber-union surface `⋃ u ∈ C, A[[u]]` is convex. -/
theorem convex_iUnion_fiber_of_convex (hA : Convex R A) (hC : Convex R C) :
    Convex R (⋃ u ∈ C, A[[u]]) := by
  simpa [SetRel.image_eq_biUnion] using SetRel.convex_image_of_convex A C hA hC

end ImageConvexityPrimitive

namespace IsConvexProcess

section ImageConvexity

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X} {C : Set U}

/-- Proposition 39.0.8: if `A` is a convex process and `C` is convex, then the image set
`A.image C` is convex. This is the canonical owner form of the source statement
`AC := ⋃ u ∈ C, Au` is convex. -/
theorem convex_image (hA : A.IsConvexProcess R) (hC : Convex R C) :
    Convex R (A.image C) :=
  SetRel.convex_image_of_convex A C hA.convex hC

-- Proof sketch: rewrite the canonical image owner by `SetRel.image_eq_biUnion`.
/-- Proposition 39.0.8 in source-facing fiber-union form: if `A` is a convex process and `C` is
convex, then `⋃ u ∈ C, A[[u]]` is convex (equivalently, `⋃ u ∈ C, {x | u ~[A] x}`). -/
theorem convex_iUnion_fiber (hA : A.IsConvexProcess R) (hC : Convex R C) :
    Convex R (⋃ u ∈ C, A[[u]]) := by
  exact SetRel.convex_iUnion_fiber_of_convex (A := A) hA.convex hC

end ImageConvexity

end IsConvexProcess

end SetRel
