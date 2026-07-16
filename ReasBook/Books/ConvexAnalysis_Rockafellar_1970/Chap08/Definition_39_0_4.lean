import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

open scoped SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.0.4 names those convex processes whose graphs are polyhedral
  convex cones.
- `core/canonical`: the owner for multivalued mappings is `SetRel U X`, while graph polyhedrality
  already lives on the canonical graph-side predicate `Set.IsPolyhedral`.
- `bridge/view`: the graph of `A : SetRel U X` is just the coerced set `(A : Set (U × X))`.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `Set.IsPolyhedral` from `Chap01.Definition_2_1_2`;
- the product-space graph view `(A : Set (U × X))` already used in the surrounding chapter API.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- inherited source-facing structure: `A.IsConvexProcess R`;
- new content in this item: polyhedrality of the graph of `A`.

Layer target: `source-facing`, stated directly on the canonical relation owner.
-/

/-- Definition 39.0.4: a convex process is polyhedral when its graph, viewed as a subset of
`U × X`, is polyhedral. The convex-process hypothesis is retained as inherited structure, so this
owner records exactly the additional graph polyhedrality needed for the source phrase
"polyhedral convex cone". The graph polyhedrality is pairing-parametric at the graph level through
`Y`, rather than frozen to one concrete dual model; this pairing-side parameter is explicit on
the owner because it is mathematically essential and not recoverable from `A` alone. -/
def IsPolyhedralProcess (R : Type u) [Semiring R] [PartialOrder R]
    {U : Type v} [AddCommMonoid U] [SMul R U]
    {X : Type w} [AddCommMonoid X] [SMul R X]
    (Y : Type _) [HasPairing (U × X) Y R] (A : SetRel U X) : Prop :=
  A.IsConvexProcess R ∧ A.IsPolyhedral R Y

theorem isPolyhedralProcess_iff (R : Type u) [Semiring R] [PartialOrder R]
    {U : Type v} [AddCommMonoid U] [SMul R U]
    {X : Type w} [AddCommMonoid X] [SMul R X]
    (Y : Type _) [HasPairing (U × X) Y R] (A : SetRel U X) :
    A.IsPolyhedralProcess R Y ↔ A.IsConvexProcess R ∧ A.IsPolyhedral R Y := Iff.rfl

namespace IsPolyhedralProcess

theorem isConvexProcess {R : Type u} [Semiring R] [PartialOrder R]
    {U : Type v} [AddCommMonoid U] [SMul R U]
    {X : Type w} [AddCommMonoid X] [SMul R X]
    {Y : Type _} [HasPairing (U × X) Y R] {A : SetRel U X}
    (hA : A.IsPolyhedralProcess R Y) : A.IsConvexProcess R :=
  hA.1

theorem isPolyhedral {R : Type u} [Semiring R] [PartialOrder R]
    {U : Type v} [AddCommMonoid U] [SMul R U]
    {X : Type w} [AddCommMonoid X] [SMul R X]
    {Y : Type _} [HasPairing (U × X) Y R] {A : SetRel U X}
    (hA : A.IsPolyhedralProcess R Y) : A.IsPolyhedral R Y :=
  hA.2

end IsPolyhedralProcess

end SetRel
