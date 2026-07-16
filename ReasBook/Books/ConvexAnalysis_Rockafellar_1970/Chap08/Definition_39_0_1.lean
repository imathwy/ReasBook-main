import Mathlib.Data.Rel
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

open scoped SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.0.1 introduces a convex process, i.e. a multivalued mapping whose
  graph is a convex cone containing the origin.
- `core/canonical`: the project owner for multivalued mappings is `SetRel U X`, while the
  graph-side canonical owner already present upstream is `Set.IsConvexCone R`, together with point
  membership in the relation graph.
- `bridge/view`: the textbook graph of a process is just the underlying set
  `(A : Set (U × X))` of the relation owner `A : SetRel U X`.

Primary mathematical domain:
- multivalued linear-convex algebra, with graphs treated canonically as relations.

Domain-style sampling used here:
- `SetRel`, `SetRel.inv`, `SetRel.image`, and `SetRel.preimage` from `Mathlib.Data.Rel`;
- `Set.IsConvexCone` from `Chap01.Definition_2_5_10`;
- `Set.IsCone.smul_mem` from `Chap01.Definition_2_5_9`;
- `Set.IsConvexCone.add_mem` from `Chap01.Definition_2_5_10`, the canonical additive closure lemma
  for convex cones.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive source-facing fields: graph convex-cone ownership and graph membership of the origin;
- derived API: the pointwise graph-closure lemmas `add_mem` and `smul_mem`, plus the class owner
  `SetRel.convexProcessSet R` of convex-process graphs at fixed scalar.

Higher-object discovery:
- no extra project structure packages convex processes beyond their relation graphs;
- the right owner level is therefore a reusable property on `SetRel`, not a separate wrapper of
  graph data or pointwise closure axioms.

Layer target: `source-facing`, but stated directly on the canonical relation owner.

Owner-parameter note:
- the scalar parameter is part of the notion and is not recoverable from `A : SetRel U X`, so the
  public owner keeps it explicit as `A.IsConvexProcess R`.
-/

/-- Definition 39.0.1: a convex process is a multivalued mapping whose graph is a convex cone
containing the origin. The canonical owner is the relation `A : SetRel U X`, so the source notion
is recorded by bundling the existing graph convex-cone owner as a primitive field instead of by a
separate layer of
pointwise closure axioms. -/
class IsConvexProcess (R : Type u) [Semiring R] [PartialOrder R]
    {U : Type v} [AddCommMonoid U] [SMul R U]
    {X : Type w} [AddCommMonoid X] [SMul R X]
    (A : SetRel U X) : Prop where
  isConvexCone : Set.IsConvexCone R A
  zero_mem : (0 : U) ~[A] (0 : X)

/-- Canonical graph-side characterization of a convex process: the graph is a convex cone and
contains the origin. This keeps the bridge surface at the chapter owner `Set.IsConvexCone`,
rather than exposing the lower-level decomposition `Set.IsCone ∧ Convex`. -/
theorem isConvexProcess_iff
    (R : Type u) [Semiring R] [PartialOrder R]
    {U : Type v} [AddCommMonoid U] [SMul R U]
    {X : Type w} [AddCommMonoid X] [SMul R X]
    (A : SetRel U X) :
    A.IsConvexProcess R ↔ Set.IsConvexCone R A ∧ (0 : U) ~[A] (0 : X) := by
  constructor
  · intro hA
    exact ⟨hA.isConvexCone, hA.zero_mem⟩
  · rintro ⟨hA_cone, hA_zero⟩
    exact ⟨hA_cone, hA_zero⟩

section ConvexProcessSet

variable (R : Type u) [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]

/-- The class of convex processes `U ⇸ X` at scalar `R`, viewed as a subset of relation graphs. -/
def convexProcessSet : Set (SetRel U X) :=
  {A : SetRel U X | A.IsConvexProcess R}

@[simp] theorem mem_convexProcessSet_iff {A : SetRel U X} :
    A ∈ (convexProcessSet R : Set (SetRel U X)) ↔ A.IsConvexProcess R := Iff.rfl

end ConvexProcessSet

namespace IsConvexProcess

section

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

/-- The graph of a convex process is a cone. -/
theorem isCone (hA : A.IsConvexProcess R) : Set.IsCone R A :=
  hA.isConvexCone.isCone

/-- The graph of a convex process is convex. -/
theorem convex (hA : A.IsConvexProcess R) : Convex R A :=
  hA.isConvexCone.convex

/-- A convex process is closed under multiplication by positive scalars on its graph. -/
theorem smul_mem (hA : A.IsConvexProcess R) {a : R} (ha : 0 < a)
    {u : U} {x : X} (hux : u ~[A] x) :
    a • u ~[A] a • x :=
  hA.isCone.smul_mem ha hux

end

section

variable {R : Type u} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R] [ZeroLEOneClass R] [AddLeftMono R]
variable {U : Type v} [AddCommMonoid U] [Module R U]
variable {X : Type w} [AddCommMonoid X] [Module R X]
variable {A : SetRel U X}

/-- A convex process is closed under addition on its graph. -/
theorem add_mem (hA : A.IsConvexProcess R)
    {u1 u2 : U} {x1 x2 : X} (h1 : u1 ~[A] x1) (h2 : u2 ~[A] x2) :
    u1 + u2 ~[A] (x1 + x2) :=
  hA.isConvexCone.add_mem h1 h2

end

end IsConvexProcess

end SetRel
