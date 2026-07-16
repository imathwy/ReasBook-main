import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_5

open Convexity

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators Rockafellar

section

variable {R : Type v} [AddCommMonoid R] [One R] [Preorder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.0.7 introduces the predicate that a vector is a mixed convex
  combination drawn from a mixed set with a point part `S₀` and a direction part `S₁`.
- `core/canonical`: the owner abstraction for directions in this chapter is `Module.Ray R E`.
- `bridge/view`: this file keeps both:
  (i) the primitive finite certificate with explicit finite index types over an arbitrary
      direction-carrier set of vectors, and
  (ii) the source-facing ray-indexed owner obtained by specializing that carrier to
      `ray directions`.
- Primitive data vs derived API:
  - primitive data: finite point/direction index types, corresponding point/direction families,
    the point simplex coefficients, and nonnegative direction coefficients;
- derived owner surfaces:
  - `Set.IsMixedConvexCombinationIn` on an arbitrary direction carrier `directionCarrier : Set E`;
  - specialization to direction vectors in `ray directions`, yielding
    `Set.IsMixedConvexCombination`.

Domain-style sampling used here:
- `Module.Ray R E` as the canonical owner for directions;
- `ray`;
- finite sums over arbitrary finite index types in mathlib's `BigOperators` API.

The primitive certificate itself does not use any ray-specific construction; it only needs
`[AddCommMonoid R] [One R] [Preorder R]` and `[SMul R E]`.
-/

/-- Primitive finite mixed-combination certificate on an arbitrary direction-carrier set of
vectors. This is the algebraic core used by Definition 17.0.7 before specializing directions to
`ray directions`. -/
private def IsMixedConvexCombinationCertificate (points directionCarrier : Set E)
    (x : E) (ι κ : Type*) [Fintype ι] [Fintype κ] : Prop :=
  ∃ pointVec : ι → points, ∃ dirVec : κ → directionCarrier,
    ∃ pointCoeff : StdSimplex R ι, ∃ dirCoeff : κ → R,
      x = (∑ i, pointCoeff.weights i • (pointVec i : E)) +
            (∑ j, dirCoeff j • (dirVec j : E)) ∧
      (∀ j, 0 ≤ dirCoeff j)

/-- Definition 17.0.7 core form: a mixed convex combination with fixed finite point/direction
indices over an arbitrary direction-carrier set of vectors. This primitive owner does not depend
on the ray specialization. -/
def IsMixedConvexCombinationWith
    (R : Type v) [AddCommMonoid R] [One R] [Preorder R]
    {E : Type u} [AddCommMonoid E] [SMul R E]
    (points directionCarrier : Set E)
    (x : E) (ι κ : Type*) [Fintype ι] [Fintype κ] : Prop :=
  IsMixedConvexCombinationCertificate (R := R) (E := E) points directionCarrier x ι κ

/-- Owner-level existential mixed-combination predicate on an arbitrary direction-carrier set of
vectors. -/
def IsMixedConvexCombinationIn
    (R : Type v) [AddCommMonoid R] [One R] [Preorder R]
    {E : Type u} [AddCommMonoid E] [SMul R E]
    (points directionCarrier : Set E)
    (x : E) : Prop :=
  ∃ (ι κ : Type (max u v)) (_ : Fintype ι) (_ : Fintype κ),
    IsMixedConvexCombinationWith R points directionCarrier x ι κ

end Set

end

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Set

/-- Definition 17.0.7 on the source-facing ray-owner surface: `x` is a mixed convex combination
of `points` and `directions` iff it is a mixed convex combination on the induced vector-carrier
set `ray directions`. -/
def IsMixedConvexCombination (points : Set E) (directions : Set (Module.Ray R E))
    (x : E) : Prop :=
  IsMixedConvexCombinationIn R points (ray directions) x

end Set

end
