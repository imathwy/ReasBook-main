import Mathlib
import Mathlib.Data.Rel
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_39_0_1 (from Chap08) -/
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

/-! ### Proposition_39_0_1 (from Chap08) -/
/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.1 identifies convex processes with multivalued mappings whose
  graphs are convex cones containing the origin.
- `core/canonical`: Definition 39.0.1 already chose the correct owner
  `SetRel.IsConvexProcess R A` on the relation graph `A : SetRel U X`.
- `bridge/view`: the textbook graph `graph A` is just the relation set `A : Set (U × X)`, and the
  graph-side criterion is the canonical bridge
  `SetRel.isConvexProcess_iff`.

Domain-style sampling used here:
- `SetRel` and graph membership notation from `Mathlib.Data.Rel`;
- `Set.IsConvexCone` from `Chap01.Definition_2_5_10`;
- `SetRel.IsConvexProcess` and its canonical iff bridge theorem from
  `Chap08.Definition_39_0_1`.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive owner predicate: `A.IsConvexProcess R`;
- bridge graph view: `Set.IsConvexCone R A` together with `(0 : U) ~[A] (0 : X)`.

Layer target: `bridge/view`. The proposition is an exact graph-side characterization of the
canonical owner and therefore should be reused directly rather than wrapped in a parallel theorem.

Abstraction checks for this item:
- Codomain/ambient concreteness: no ordered-extended codomain owner is introduced here; this file
  only recalls the relation-graph characterization already owned upstream.
- Scalar/ambient structure: no concrete scalar or model specialization is fixed in this file; the
  reused owner remains parametric in `R`, `U`, and `X` under the canonical assumptions from
  `SetRel.IsConvexProcess`.
- Owner choice: the intrinsic owner is `A.IsConvexProcess R` on `SetRel`; no extra local wrapper
  theorem is introduced.
- Topology language: not applicable; the proposition has no ambient/intrinsic topology surface.
- Owner naming/notation: keep the short canonical owner and its canonical iff bridge
  `SetRel.isConvexProcess_iff` directly.
-/

/- Proposition 39.0.1: a multivalued mapping is a convex process exactly when its graph, viewed as
the relation set `A : Set (U × X)`, is a convex cone containing the origin. This is exactly the
canonical graph-side characterization for `SetRel.IsConvexProcess`. -/
recall SetRel.isConvexProcess_iff

/-! ### Proposition_39_0_2 (from Chap08) -/
open scoped SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.2 records the elementary closure properties of a convex
  process: fibers are convex, `A0` is a convex cone, `dom A` and `range A` are convex cones, and
  `A⁻¹` is again a convex process.
- `core/canonical`: the primitive graph-closure results are stated on the intrinsic graph owner
  `Set.IsConvexCone R A` (and, for images, already on `Convex R A`), then the process-level
  statements are thin specializations through `A.IsConvexProcess R`.
- `bridge/view`: textbook fibers `Au` and `A0` are rendered on the chapter singleton-image
  notation surface as `A[[u]]` and `A[[0]]`, while textbook `range A` is the canonical relation
  codomain `A.cod`.

Layer target: `source-facing`, directly on the canonical relation owner.
-/

section Image

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]

-- Proof sketch: represent points of `A.image C` by graph witnesses `(uᵢ, xᵢ) ∈ A` with `uᵢ ∈ C`,
-- then combine the base points using convexity of `C` and the graph points using convexity of `A`.
/-- Core owner theorem for Chapter 39 images: a relation with convex graph sends convex sets to
convex image sets. -/
theorem convex_image_of_convex (A : SetRel U X) (C : Set U)
    (hA : Convex R A) (hC : Convex R C) :
    Convex R (A.image C) := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  rcases SetRel.mem_image.mp hx₁ with ⟨u₁, hu₁C, hu₁x₁⟩
  rcases SetRel.mem_image.mp hx₂ with ⟨u₂, hu₂C, hu₂x₂⟩
  refine SetRel.mem_image.mpr ⟨a • u₁ + b • u₂, hC hu₁C hu₂C ha hb hab, ?_⟩
  simpa [Prod.smul_mk, Prod.mk_add_mk] using hA hu₁x₁ hu₂x₂ ha hb hab

end Image

section ConvexImage

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMulZeroClass R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: witnesses in `A[[0]]` are graph points `(0, x) ∈ A`; convexity of the graph gives
-- a witness over base point `a • 0 + b • 0 = 0`.
/-- Core owner theorem for Chapter 39 zero fibers: convexity of a relation graph implies convexity
of its zero fiber `A[[0]]`. This keeps the assumption at the primitive convex-graph layer,
independent of cone closure. -/
theorem convex_image_zero_of_convex (hA : Convex R A) :
    Convex R (A[[0]]) := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  rcases SetRel.mem_image.mp hx₁ with ⟨u₁, hu₁, hu₁x₁⟩
  rcases SetRel.mem_image.mp hx₂ with ⟨u₂, hu₂, hu₂x₂⟩
  have hu₁ : u₁ = 0 := by simpa using hu₁
  have hu₂ : u₂ = 0 := by simpa using hu₂
  subst u₁ u₂
  refine SetRel.mem_image.mpr ⟨0, by simp, ?_⟩
  simpa [smul_zero] using hA hu₁x₁ hu₂x₂ ha hb hab

end ConvexImage

section ConvexFibers

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [Module R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: singleton fibers are relation images of singleton base sets; apply the primitive
-- convex-image theorem and `convex_singleton`.
/-- Core owner theorem for Chapter 39 fibers: convexity of a relation graph implies convexity of
every singleton fiber `A[[u]]`. -/
theorem convex_image_singleton_of_convex (hA : Convex R A) (u : U) :
    Convex R (A[[u]]) :=
  SetRel.convex_image_of_convex A {u} hA (convex_singleton u)

end ConvexFibers

section ConvexDomCod

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: witness `uᵢ ∈ dom A` by graph points `(uᵢ, xᵢ) ∈ A`; convexity of the graph gives
-- `(a • u₁ + b • u₂, a • x₁ + b • x₂) ∈ A`.
/-- Core owner theorem for Chapter 39 domains: convexity of a relation graph implies convexity of
its domain. -/
theorem convex_dom_of_convex (hA : Convex R A) : Convex R A.dom := by
  intro u₁ hu₁ u₂ hu₂ a b ha hb hab
  rcases hu₁ with ⟨x₁, hu₁x₁⟩
  rcases hu₂ with ⟨x₂, hu₂x₂⟩
  exact ⟨a • x₁ + b • x₂, hA hu₁x₁ hu₂x₂ ha hb hab⟩

-- Proof sketch: witness `xᵢ ∈ cod A` by graph points `(uᵢ, xᵢ) ∈ A`; convexity of the graph gives
-- `(a • u₁ + b • u₂, a • x₁ + b • x₂) ∈ A`.
/-- Core owner theorem for Chapter 39 codomains: convexity of a relation graph implies convexity
of its codomain/range `A.cod`. -/
theorem convex_cod_of_convex (hA : Convex R A) : Convex R A.cod := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  rcases hx₁ with ⟨u₁, hu₁x₁⟩
  rcases hx₂ with ⟨u₂, hu₂x₂⟩
  exact ⟨a • u₁ + b • u₂, hA hu₁x₁ hu₂x₂ ha hb hab⟩

end ConvexDomCod

namespace Set.IsCone

section ZeroFiber

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [Zero U] [SMulZeroClass R U]
variable {X : Type w} [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: if `x ∈ A[[0]]`, witnessed by `(0, x) ∈ A`, then positive scalar closure of the
-- graph gives `(0, c • x) ∈ A` because `c • 0 = 0`.
/-- Core owner theorem for Chapter 39 zero fibers: cone closure of a relation graph implies cone
closure of the zero fiber `A[[0]]`. -/
theorem isCone_image_zero (hA : Set.IsCone R A) :
    Set.IsCone R (A[[0]]) := by
  intro c x hc hx
  rcases hx with ⟨u, hu0, hux⟩
  have hu : u = 0 := by simpa using hu0
  subst u
  refine ⟨0, by simp, ?_⟩
  have hsmul : (c • (0 : U), c • x) ∈ A := by
    simpa [Prod.smul_mk] using hA.smul_mem hc hux
  have hzero : c • (0 : U) = (0 : U) := by
    simp
  simpa [hzero] using hsmul

end ZeroFiber

section DomCod

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [SMul R U]
variable {X : Type w} [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: if `u ∈ dom A`, pick `x` with `(u, x) ∈ A`; positive scalar closure of the graph
-- gives `(c • u, c • x) ∈ A`.
/-- Core owner theorem for Chapter 39 domains: cone closure of a relation graph implies cone
closure of `A.dom`. -/
theorem isCone_dom (hA : Set.IsCone R A) : Set.IsCone R A.dom := by
  intro c u hc hu
  rcases hu with ⟨x, hux⟩
  exact ⟨c • x, hA.smul_mem hc hux⟩

-- Proof sketch: if `x ∈ cod A`, pick `u` with `(u, x) ∈ A`; positive scalar closure of the graph
-- gives `(c • u, c • x) ∈ A`, hence `c • x ∈ cod A`.
/-- Core owner theorem for Chapter 39 codomains: cone closure of a relation graph implies cone
closure of `A.cod`. -/
theorem isCone_cod (hA : Set.IsCone R A) : Set.IsCone R A.cod := by
  intro c x hc hx
  rcases hx with ⟨u, hux⟩
  exact ⟨c • u, hA.smul_mem hc hux⟩

end DomCod

section Inverse

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [SMul R U]
variable {X : Type w} [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: swap graph coordinates and apply cone closure to the swapped witness.
/-- Core owner theorem for Chapter 39 inverses: cone closure of a relation graph is preserved by
relation inversion. -/
theorem inverse (hA : Set.IsCone R A) : Set.IsCone R (A⁻¹) := by
  intro c p hc hp
  rcases p with ⟨x, u⟩
  change (c • x, c • u) ∈ A⁻¹
  have hux : (u, x) ∈ A := by
    simpa [SetRel.mem_inv] using hp
  have hsmul : (c • u, c • x) ∈ A := hA.smul_mem hc hux
  simpa [SetRel.mem_inv] using hsmul

end Inverse

end Set.IsCone

namespace Set.IsConvexCone

section Fibers

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [Module R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: witnesses in `A[[u]]` are graph points `(u, x) ∈ A`; convexity of the
-- graph gives the convex combination witness over the same base point `u`. The ambient
-- `Module R U` structure is used precisely to make the singleton base set convex via
-- `convex_singleton`, i.e. through `(a + b) • u = a • u + b • u` and `1 • u = u`.
/-- Every singleton fiber `A[[u]]` of a relation with convex-cone graph is convex. -/
theorem convex_image_singleton (hA : Set.IsConvexCone R A) (u : U) :
    Convex R (A[[u]]) :=
  SetRel.convex_image_singleton_of_convex hA.convex u

end Fibers

section ZeroFiberCone

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMulZeroClass R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: if `x ∈ A0`, witnessed by `(0, x) ∈ A`, then positive scalar closure of the graph
-- gives `(0, c • x) ∈ A` because `c • 0 = 0`.
/-- The zero fiber `A0 = A[[0]]` of a relation with convex-cone graph is a cone. -/
theorem isCone_image_zero (hA : Set.IsConvexCone R A) :
    Set.IsCone R (A[[0]]) :=
  Set.IsCone.isCone_image_zero hA.isCone

/-- The zero fiber `A0 = A[[0]]` of a relation with convex-cone graph is convex. -/
theorem convex_image_zero (hA : Set.IsConvexCone R A) :
    Convex R (A[[0]]) :=
  SetRel.convex_image_zero_of_convex hA.convex

/-- The zero fiber `A0 = A[[0]]` of a relation with convex-cone graph is a convex cone. -/
theorem isConvexCone_image_zero (hA : Set.IsConvexCone R A) :
    Set.IsConvexCone R (A[[0]]) :=
  ⟨Set.IsConvexCone.isCone_image_zero hA, Set.IsConvexCone.convex_image_zero hA⟩

end ZeroFiberCone

section DomCod

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: if `u ∈ dom A`, pick `x` with `(u, x) ∈ A`; positive scalar closure of the graph
-- gives `(c • u, c • x) ∈ A`.
/-- The domain of a relation with convex-cone graph is a cone. -/
theorem isCone_dom (hA : Set.IsConvexCone R A) : Set.IsCone R A.dom :=
  Set.IsCone.isCone_dom hA.isCone

-- Proof sketch: witness `uᵢ ∈ dom A` by graph points `(uᵢ, xᵢ) ∈ A`; convexity of the graph gives
-- `(a • u₁ + b • u₂, a • x₁ + b • x₂) ∈ A`.
/-- The domain of a relation with convex-cone graph is convex. -/
theorem convex_dom (hA : Set.IsConvexCone R A) : Convex R A.dom :=
  SetRel.convex_dom_of_convex hA.convex

/-- The domain of a relation with convex-cone graph is a convex cone. -/
theorem isConvexCone_dom (hA : Set.IsConvexCone R A) : Set.IsConvexCone R A.dom :=
  ⟨Set.IsConvexCone.isCone_dom hA, Set.IsConvexCone.convex_dom hA⟩

-- Proof sketch: if `x ∈ cod A`, pick `u` with `(u, x) ∈ A`; positive scalar closure of the graph
-- gives `(c • u, c • x) ∈ A`, hence `c • x ∈ cod A`.
/-- The codomain/range `A.cod` of a relation with convex-cone graph is a cone. -/
theorem isCone_cod (hA : Set.IsConvexCone R A) : Set.IsCone R A.cod :=
  Set.IsCone.isCone_cod hA.isCone

-- Proof sketch: witness `xᵢ ∈ cod A` by graph points `(uᵢ, xᵢ) ∈ A`; convexity of the graph gives
-- `(a • u₁ + b • u₂, a • x₁ + b • x₂) ∈ A`.
/-- The codomain/range `A.cod` of a relation with convex-cone graph is convex. -/
theorem convex_cod (hA : Set.IsConvexCone R A) : Convex R A.cod :=
  SetRel.convex_cod_of_convex hA.convex

/-- The codomain/range `A.cod` of a relation with convex-cone graph is a convex cone. -/
theorem isConvexCone_cod (hA : Set.IsConvexCone R A) : Set.IsConvexCone R A.cod :=
  ⟨Set.IsConvexCone.isCone_cod hA, Set.IsConvexCone.convex_cod hA⟩

end DomCod

section Inverse

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: swap graph coordinates. The cone and convexity conditions are preserved under
-- this swap.
/-- The inverse relation `A⁻¹` of a relation with convex-cone graph again has convex-cone graph. -/
theorem inverse (hA : Set.IsConvexCone R A) : Set.IsConvexCone R (A⁻¹) := by
  refine ⟨?_, ?_⟩
  · exact Set.IsCone.inverse hA.isCone
  · intro p hp q hq a b ha hb hab
    rcases p with ⟨x₁, u₁⟩
    rcases q with ⟨x₂, u₂⟩
    change (a • x₁ + b • x₂, a • u₁ + b • u₂) ∈ A⁻¹
    have hu₁x₁ : (u₁, x₁) ∈ A := by
      simpa [SetRel.mem_inv] using hp
    have hu₂x₂ : (u₂, x₂) ∈ A := by
      simpa [SetRel.mem_inv] using hq
    have hconv : (a • u₁ + b • u₂, a • x₁ + b • x₂) ∈ A :=
      hA.convex hu₁x₁ hu₂x₂ ha hb hab
    simpa [SetRel.mem_inv] using hconv

end Inverse

end Set.IsConvexCone

namespace IsConvexProcess

section Fibers

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [Module R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: witnesses in `A[[u]]` are graph points `(u, x) ∈ A`; convexity of the
-- graph gives the convex combination witness over the same base point `u`. The ambient
-- `Module R U` structure is used precisely to make the singleton base set convex via
-- `convex_singleton`, i.e. through `(a + b) • u = a • u + b • u` and `1 • u = u`.
/-- Proposition 39.0.2: every fiber `A[[u]]` of a convex process is convex. -/
theorem convex_image_singleton (hA : A.IsConvexProcess R) (u : U) :
    Convex R (A[[u]]) :=
  Set.IsConvexCone.convex_image_singleton hA.isConvexCone u

end Fibers

section ZeroFiber

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

/-- The zero fiber `A0` of a convex process contains `0`. -/
theorem zero_mem_image_zero (hA : A.IsConvexProcess R) :
    (0 : X) ∈ A[[0]] := by
  exact ⟨0, by simp, hA.zero_mem⟩

end ZeroFiber

section ZeroFiberCone

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMulZeroClass R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: if `x ∈ A0`, witnessed by `(0, x) ∈ A`, then positive scalar closure of the graph
-- gives `(0, c • x) ∈ A` because `c • 0 = 0`.
/-- The zero fiber `A0 = A[[0]]` is a cone. -/
theorem isCone_image_zero (hA : A.IsConvexProcess R) :
    Set.IsCone R (A[[0]]) :=
  Set.IsCone.isCone_image_zero hA.isCone

/-- The zero fiber `A0 = A[[0]]` is convex. -/
theorem convex_image_zero (hA : A.IsConvexProcess R) :
    Convex R (A[[0]]) :=
  SetRel.convex_image_zero_of_convex hA.convex

/-- Proposition 39.0.2: `A0 = A[[0]]` is a convex cone. -/
theorem isConvexCone_image_zero (hA : A.IsConvexProcess R) :
    Set.IsConvexCone R (A[[0]]) :=
  Set.IsConvexCone.isConvexCone_image_zero hA.isConvexCone

end ZeroFiberCone

section DomCod

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: if `u ∈ dom A`, pick `x` with `(u, x) ∈ A`; positive scalar closure of the graph
-- gives `(c • u, c • x) ∈ A`.
/-- The domain of a convex process is a cone. -/
theorem isCone_dom (hA : A.IsConvexProcess R) : Set.IsCone R A.dom :=
  Set.IsCone.isCone_dom hA.isCone

-- Proof sketch: witness `uᵢ ∈ dom A` by graph points `(uᵢ, xᵢ) ∈ A`; convexity of the graph gives
-- `(a • u₁ + b • u₂, a • x₁ + b • x₂) ∈ A`.
/-- The domain of a convex process is convex. -/
theorem convex_dom (hA : A.IsConvexProcess R) : Convex R A.dom :=
  SetRel.convex_dom_of_convex hA.convex

/-- Proposition 39.0.2: `dom A` is a convex cone. -/
theorem isConvexCone_dom (hA : A.IsConvexProcess R) : Set.IsConvexCone R A.dom :=
  Set.IsConvexCone.isConvexCone_dom hA.isConvexCone

-- Proof sketch: if `x ∈ cod A`, pick `u` with `(u, x) ∈ A`; positive scalar closure of the graph
-- gives `(c • u, c • x) ∈ A`, hence `c • x ∈ cod A`.
/-- The codomain/range `A.cod` of a convex process is a cone. -/
theorem isCone_cod (hA : A.IsConvexProcess R) : Set.IsCone R A.cod :=
  Set.IsCone.isCone_cod hA.isCone

-- Proof sketch: witness `xᵢ ∈ cod A` by graph points `(uᵢ, xᵢ) ∈ A`; convexity of the graph gives
-- `(a • u₁ + b • u₂, a • x₁ + b • x₂) ∈ A`.
/-- The codomain/range `A.cod` of a convex process is convex. -/
theorem convex_cod (hA : A.IsConvexProcess R) : Convex R A.cod :=
  SetRel.convex_cod_of_convex hA.convex

/-- Proposition 39.0.2: `range A` (canonical owner `A.cod`) is a convex cone. -/
theorem isConvexCone_cod (hA : A.IsConvexProcess R) : Set.IsConvexCone R A.cod :=
  Set.IsConvexCone.isConvexCone_cod hA.isConvexCone

end DomCod

section Inverse

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {A : SetRel U X}

-- Proof sketch: swap graph coordinates. The cone and convexity conditions are preserved under
-- this swap, and `(0,0)` remains fixed.
/-- Proposition 39.0.2: the inverse process `A⁻¹` of a convex process is again a convex
process. -/
theorem inverse (hA : A.IsConvexProcess R) : (A⁻¹).IsConvexProcess R := by
  refine ⟨Set.IsConvexCone.inverse hA.isConvexCone, ?_⟩
  simpa [SetRel.mem_inv] using hA.zero_mem

end Inverse

end IsConvexProcess

/- The domain/codomain identities for `A⁻¹` are already canonical `SetRel` owner lemmas. -/
recall SetRel.dom_inv
recall SetRel.cod_inv

end SetRel

/-! ### Example_39_0_3 (from Chap08) -/
open scoped SetRel

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Example 39.0.3 defines, from a map `B`, the process sending a
  nonnegative `u` to the lower set `{x | x ≤ B u}` and sending negative `u` to `∅`.
- `core/canonical`: convex processes in this chapter already live on the relation owner
  `A : SetRel U X` via `A.IsConvexProcess R`.
- `bridge/view`: the source set-valued formula is therefore best encoded directly as the graph
  relation `{(u, x) | 0 ≤ u ∧ x ≤ B u}` attached to `B`.

Primary mathematical domain:
- lower-set processes on ordered types, with linear-map convexity as a specialization.

Domain-style sampling used here:
- `SetRel`, `SetRel.inv`, and `SetRel.image` from `Mathlib.Data.Rel`;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- order inequalities `0 ≤ u` and `x ≤ B u`.

Primitive data vs derived API:
- primitive owner data: a map `B : U → X`;
- primitive source-facing object: the relation `Function.lowerSetProcess B`;
- derived API: graph membership, the forward-fiber formulas on `SetRel.image ({u} : Set U)`, and
  the linear-map convex-process property.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owner.
-/

namespace Function

section

variable {U : Type v} [Zero U] [LE U]
variable {X : Type w} [LE X]

/-- Example 39.0.3: for a map `B` between ordered types, the associated
process is the relation sending `u` to `{x | x ≤ B u}` when `u ≥ 0`, and to `∅` otherwise. On the
canonical relation owner, this is exactly the graph relation `0 ≤ u ∧ x ≤ B u`. -/
def lowerSetProcess (B : U → X) : SetRel U X :=
  {(u, x) | 0 ≤ u ∧ x ≤ B u}

-- Proof sketch: unfold `Function.lowerSetProcess` and the `SetRel` membership notation; the
-- statement is definitional.
/-- Membership in `B.lowerSetProcess` is the conjunction `u ≥ 0` and `x ≤ B u`. -/
@[simp] theorem mem_lowerSetProcess_iff
    (B : U → X) {u : U} {x : X} :
    u ~[B.lowerSetProcess] x ↔ 0 ≤ u ∧ x ≤ B u := by
  rfl

end

section

variable {U : Type v} [Zero U] [LE U]
variable {X : Type w} [Preorder X]

/-- Membership in `B.lowerSetProcess` as lower-set membership. -/
@[simp] theorem mem_lowerSetProcess_iff_mem_Iic
    (B : U → X) {u : U} {x : X} :
    u ~[B.lowerSetProcess] x ↔ 0 ≤ u ∧ x ∈ Set.Iic (B u) := by
  simp [Set.mem_Iic, B.mem_lowerSetProcess_iff]

-- Proof sketch: expand `SetRel.image` on the singleton `{u}` and unfold graph membership in
-- `B.lowerSetProcess`; splitting on `0 ≤ u` yields the source-facing piecewise process formula.
-- The fiber of `B.lowerSetProcess` is the source piecewise map:
-- `Set.Iic (B u)` on `u ≥ 0`, and `∅` on `¬ (0 ≤ u)`.
open Classical in theorem lowerSetProcess_image_singleton
    (B : U → X) (u : U) :
    B.lowerSetProcess.image ({u} : Set U) =
      if 0 ≤ u then Set.Iic (B u) else (∅ : Set X) := by
  by_cases hu : 0 ≤ u
  · ext x
    simp [Function.lowerSetProcess, hu]
  · ext x
    simp [Function.lowerSetProcess, hu]

attribute [simp] lowerSetProcess_image_singleton

-- Proof sketch: specialize `lowerSetProcess_image_singleton` at a nonnegative `u`.
/-- For `u ≥ 0`, the fiber is the lower set `Set.Iic (B u)`. -/
@[simp] theorem lowerSetProcess_image_singleton_of_nonneg
    (B : U → X) {u : U} (hu : 0 ≤ u) :
    B.lowerSetProcess.image ({u} : Set U) = Set.Iic (B u) := by
  simp [Function.lowerSetProcess_image_singleton, hu]

-- Proof sketch: specialize `lowerSetProcess_image_singleton` at `¬ (0 ≤ u)`.
/-- For `¬ (0 ≤ u)`, the fiber of `B.lowerSetProcess` at `u` is empty. -/
@[simp] theorem lowerSetProcess_image_singleton_of_not_nonneg
    (B : U → X) {u : U} (hu : ¬ 0 ≤ u) :
    B.lowerSetProcess.image ({u} : Set U) = (∅ : Set X) := by
  simp [Function.lowerSetProcess_image_singleton, hu]

end

end Function

namespace LinearMap

section

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [Module R U] [Preorder U] [AddLeftMono U]
variable [PosSMulMono R U]
variable {X : Type w} [AddCommMonoid X] [Module R X] [Preorder X] [AddLeftMono X]
variable [PosSMulMono R X]

-- Proof sketch: on the graph relation `{(u, x) | 0 ≤ u ∧ x ≤ B u}`, addition preserves both the
-- nonnegativity condition on `u` and the upper-bound condition on `x` by linearity of `B` and
-- ordered-module monotonicity. Positive scalar multiplication does the same, and `(0, 0)` belongs
-- to the graph because `B 0 = 0`.
/-- This lower-set relation attached to a linear map is a convex process. -/
theorem lowerSetProcess_isConvexProcess
    (B : U →ₗ[R] X) :
    (Function.lowerSetProcess B).IsConvexProcess R := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro c p hc hp
      rcases p with ⟨u, x⟩
      rcases hp with ⟨hu, hx⟩
      refine ⟨smul_nonneg (le_of_lt hc) hu, ?_⟩
      simpa [map_smul] using smul_le_smul_of_nonneg_left hx (le_of_lt hc)
    · intro p hp q hq a b ha hb hab
      rcases p with ⟨u1, x1⟩
      rcases q with ⟨u2, x2⟩
      rcases hp with ⟨hu1, hx1⟩
      rcases hq with ⟨hu2, hx2⟩
      refine ⟨add_nonneg (smul_nonneg ha hu1) (smul_nonneg hb hu2), ?_⟩
      have h1 : a • x1 ≤ a • B u1 := smul_le_smul_of_nonneg_left hx1 ha
      have h2 : b • x2 ≤ b • B u2 := smul_le_smul_of_nonneg_left hx2 hb
      have hsum : a • x1 + b • x2 ≤ a • B u1 + b • B u2 := add_le_add h1 h2
      simpa [map_add, map_smul] using hsum
  · exact ⟨le_rfl, by simp⟩

end

end LinearMap

/-! ### Definition_39_0_4 (from Chap08) -/
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

/-! ### Definition_39_0_5 (from Chap08) -/
open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.0.5 introduces the closure `cl A` of a convex process and says
  that a process is closed when `cl A = A`.
- `core/canonical`: the owner of a process graph is the existing relation type `SetRel U X`, and
  graph closure is the ambient topological closure `_root_.closure` on subsets of `U × X`.
- `bridge/view`: the process owner from Definition 39.0.1 is the predicate `A.IsConvexProcess R`
  on a relation `A : SetRel U X`, so the theorem that closure preserves convex processes should be
  stated directly on that owner.

Primary mathematical domain:
- convex processes as graph relations in topological modules.

Domain-style sampling used here:
- `SetRel` from `Mathlib.Data.Rel` as the canonical graph owner;
- `_root_.closure` and `_root_.IsClosed` for graph closure and graph closedness;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `Set.IsConvexCone.closure` from `Chap02.Text_6_20` as the owner-level graph-closure theorem.

Primitive data vs derived API:
- primitive source-facing data: the relation graph `A : SetRel U X`;
- primitive owner introduced here: `SetRel.closure A`;
- derived API: graph-closure formula, closedness-as-fixed-point, and the theorem that closure
  preserves the convex-process owner.

Notation decision:
- the chapter closure notation `cl(·)` is extended to relation graphs in the same
  `Rockafellar` notation scope used elsewhere in the project, so source-facing Chapter 39
  statements can use `cl(A)` directly while the canonical owner remains `SetRel.closure`.

Layer target: `source-facing`, stated directly on the canonical relation owner.
-/

section Closure

variable {U : Type u} {X : Type v}
variable [TopologicalSpace (U × X)]

/-- Definition 39.0.5: the closure of a convex process `A` is the relation whose graph is the
ambient topological closure of the graph of `A`. -/
abbrev closure (A : SetRel U X) : SetRel U X :=
  _root_.closure A

scoped[Rockafellar] notation (name := setRelTermCl) "cl(" A ")" => SetRel.closure A

@[simp] theorem coe_closure (A : SetRel U X) :
    (cl(A) : Set (U × X)) = _root_.closure A := rfl

-- Proof sketch: this is the standard set-theoretic inclusion `subset_closure` applied to the
-- graph set `(A : Set (U × X))`.
/-- Every relation is contained in its graph closure. -/
theorem subset_closure (A : SetRel U X) :
    A ⊆ cl(A) := by
  intro p hp
  exact _root_.subset_closure hp

-- Proof sketch: relation membership is pair membership in the graph, and `SetRel.closure` is
-- definitionally the ambient closure of `(A : Set (U × X))`.
/-- A pair `(u, x)` belongs to `SetRel.closure A` exactly when it lies in the ambient closure of
the graph of `A`. -/
@[simp] theorem mem_closure_iff {A : SetRel U X} {u : U} {x : X} :
    u ~[cl(A)] x ↔ (u, x) ∈ _root_.closure A := Iff.rfl

/-- A relation, and in particular a convex process, is closed when its graph is topologically
closed in `U × X`. This is the primitive canonical owner layer for graph closedness. -/
abbrev IsClosed (A : SetRel U X) : Prop :=
  _root_.IsClosed A

@[simp] theorem isClosed_closure (A : SetRel U X) :
    (cl(A)).IsClosed := by
  exact (_root_.isClosed_closure : _root_.IsClosed (_root_.closure A))

-- Proof sketch: this is exactly `closure_eq_iff_isClosed` on the graph set `(A : Set (U × X))`
-- with the owner-level abbreviation `SetRel.IsClosed` unfolded.
/-- Canonical closedness owner for relation graphs: closure fixed points are exactly closed
relations. -/
theorem closure_eq_iff_isClosed (A : SetRel U X) :
    cl(A) = A ↔ A.IsClosed := by
  simpa [SetRel.IsClosed, SetRel.closure] using
    (_root_.closure_eq_iff_isClosed : _root_.closure A = A ↔ _root_.IsClosed A)

@[simp] theorem closure_closure (A : SetRel U X) :
    cl(cl(A)) = cl(A) :=
  (SetRel.closure_eq_iff_isClosed (cl(A))).2 (SetRel.isClosed_closure A)

/-- Definition 39.0.5 textbook fixed-point phrasing: a relation is closed exactly when its graph
closure equals itself. -/
theorem isClosed_iff_closure_eq (A : SetRel U X) :
    A.IsClosed ↔ cl(A) = A := (SetRel.closure_eq_iff_isClosed A).symm

end Closure

namespace IsConvexProcess

section Closure

variable {R : Type w} [Semiring R] [PartialOrder R]
variable {U : Type u} [AddCommMonoid U] [SMul R U]
variable {X : Type v} [AddCommMonoid X] [SMul R X]
variable [TopologicalSpace (U × X)] [ContinuousAdd (U × X)] [ContinuousConstSMul R (U × X)]
variable {A : SetRel U X}

-- Proof sketch: `Set.IsConvexCone.closure` supplies the graph-side closure step on the canonical
-- set owner; the process proof only adds preservation of the origin.
/-- The closure of a convex process is again a convex process.
This is stated at the intrinsic graph level: the ambient topological `R`-module structure required
for closure is only on `U × X`. -/
theorem closure (hA : A.IsConvexProcess R) :
    (cl(A)).IsConvexProcess R := by
  exact ⟨hA.isConvexCone.closure, SetRel.subset_closure A hA.zero_mem⟩

end Closure

end IsConvexProcess

end SetRel

/-! ### Proposition_39_0_6 (from Chap08) -/
open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.6 states three graph-level facts about a convex process:
  closure commutes with inverse, closed fibers are closed, and every nonempty fiber has common
  recession cone `A0`.
- `core/canonical`: the owner abstractions already present are the relation inverse `SetRel.inv`,
  the relation-closure owner `SetRel.closure`, the relation closedness owner `SetRel.IsClosed`,
  the process predicate `SetRel.IsConvexProcess 𝕜`, the relation image owner `A.image s` with
  singleton-fiber notation `A[[u]]`, and the
  recession-cone owner `0⁺[𝕜] C`.
- `bridge/view`: the textbook fiber notation `Au` is rendered canonically as
  `A[[u]]`, while the source zero fiber `A0` is `A[[0]]`.

Domain-style sampling used here:
- `SetRel.inv`, `SetRel.image`, and `SetRel.dom` from `Mathlib.Data.Rel`;
- `_root_.closure` and `_root_.IsClosed` on graph subsets of product spaces;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `SetRel.IsConvexProcess.convex_image_singleton` and
  `SetRel.IsConvexProcess.isConvexCone_image_zero` from `Chap08.Proposition_39_0_2`;
- `Convex.mem_recessionCone_of_nonneg_ray` from `Chap02.Theorem_8_3`.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive graph operations: inverse, relation closure, singleton-fiber image, and zero-fiber
  image;
- derived API: fiber closedness and the common recession-cone formula for closed convex processes.

Layer target:
- clauses (1) and (2) are `bridge/view` facts on the canonical relation owner;
- clause (3) is `source-facing`, stated directly on the existing convex-process owner.

Topology-layer decision:
- this item is about graph closure/closedness of relations, whose canonical owner in this project
  is ambient closedness in `U × X` via `SetRel.closure` / `SetRel.IsClosed`;
- no intrinsic/relative closure owner for relation graphs is introduced here, so ambient topology
  is the primary layer and any relative reformulations are downstream views.
-/

section InverseClosure

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

-- Proof sketch: the inverse relation is the image of the graph under the coordinate-swap
-- homeomorphism `Prod.swap`, and homeomorphisms commute with closure. Rewriting the swapped closed
-- graph back through the canonical surfaces `A⁻¹` and `cl(·)` yields the stated identity.
/-- Proposition 39.0.6 (1): closure commutes with inverse relation. For a convex process this is
the source identity `cl (A⁻¹) = (cl A)⁻¹`. -/
theorem closure_inv (A : SetRel U X) :
    cl(A⁻¹) = (cl(A))⁻¹ := by
  simpa [SetRel.inv] using
    ((Homeomorph.prodComm U X).symm.preimage_closure (A : Set (U × X))).symm

end InverseClosure

section ClosedFibers

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

namespace IsClosed

-- Proof sketch: the fiber `A[[u]]` is the preimage of the graph `A` under the
-- continuous map `x ↦ (u, x)`. A closed relation graph therefore has closed singleton fibers.
/-- Proposition 39.0.6 (2): if a relation is closed, then every singleton fiber
`A[[u]]` is closed. For a closed convex process this is the source assertion that
each set `Au` is closed. -/
theorem image_singleton
    {A : SetRel U X} (hA_closed : A.IsClosed) (u : U) :
    _root_.IsClosed (A[[u]]) := by
  let f : X → U × X := fun x ↦ (u, x)
  have hf : Continuous f := by
    simpa [f] using continuous_const.prodMk continuous_id
  simpa [SetRel.IsClosed, SetRel.image, f] using hA_closed.preimage hf

end IsClosed

end ClosedFibers

section RecessionFibers

variable {𝕜 : Type w} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {U : Type u} [AddCommGroup U] [Module 𝕜 U]
variable {X : Type v} [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace (U × X)] [IsTopologicalAddGroup (U × X)]
variable [ContinuousSMul 𝕜 (U × X)]

namespace IsConvexProcess

-- Proof sketch: one inclusion uses the convex-process graph cone laws together with the zero-fiber
-- cone API from Proposition 39.0.2. For the reverse inclusion, a fiber recession direction gives a
-- nonnegative ray in the graph along direction `(0, y)`; apply
-- `Convex.mem_recessionCone_of_nonneg_ray` to the closed convex graph and evaluate at the origin to
-- recover `(0, y) ∈ A`, i.e. `y ∈ A[[0]]`.
/-- Proposition 39.0.6 (3): for a closed convex process, every nonempty fiber
`A[[u]]` has recession cone `A[[0]]`. Hence all fibers over
points of `A.dom` share the same recession cone `A0`. This owner-level form uses the canonical
relation domain owner `u ∈ A.dom`. -/
theorem recessionCone_image_singleton_eq_image_zero
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜)
    (hA_closed : A.IsClosed)
    (u : U) (hu : u ∈ A.dom) :
    0⁺[𝕜] (A[[u]]) = A[[0]] := by
  rcases hu with ⟨x, hux⟩
  have hx : x ∈ A[[u]] := SetRel.mem_image.mpr ⟨u, by simp, hux⟩
  ext y
  constructor
  · intro hy
    have hRay : ∀ a : 𝕜, 0 ≤ a → (u, x) + a • (0, y) ∈ (A : Set (U × X)) := by
      intro a ha
      have hxay : x + a • y ∈ A[[u]] := (Set.mem_recessionCone_iff.mp hy) x hx a ha
      rcases SetRel.mem_image.mp hxay with ⟨u', hu', hu'xay⟩
      have hu' : u' = u := by simpa using hu'
      subst hu'
      simpa [Prod.mk_add_mk, Prod.smul_mk] using hu'xay
    have hdir : (0, y) ∈ 0⁺[𝕜] (A : Set (U × X)) :=
      hA.convex.mem_recessionCone_of_nonneg_ray (x := (u, x)) hA_closed hRay
    have h0y : (0, y) ∈ (A : Set (U × X)) := by
      have hstep :
          (0 : U × X) + (1 : 𝕜) • (0, y) ∈ (A : Set (U × X)) :=
        (Set.mem_recessionCone_iff.mp hdir) (0, 0) hA.zero_mem 1 (le_of_lt zero_lt_one)
      simpa [Prod.mk_add_mk, Prod.smul_mk] using hstep
    exact SetRel.mem_image.mpr ⟨0, by simp, h0y⟩
  · intro hy0
    rcases SetRel.mem_image.mp hy0 with ⟨u0, hu0, hu0y⟩
    have hu0 : u0 = 0 := by simpa using hu0
    subst hu0
    refine Set.mem_recessionCone_iff.mpr ?_
    intro x hx a ha
    rcases SetRel.mem_image.mp hx with ⟨u', hu', hu'x⟩
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simpa using hx
    · have hsmul : (0 : U) ~[A] a • y := by
        simpa [smul_zero] using hA.smul_mem ha_pos hu0y
      have hsum : u' ~[A] x + a • y := by
        simpa [smul_zero] using hA.add_mem hu'x hsmul
      exact SetRel.mem_image.mpr ⟨u', hu', hsum⟩

/-- Proposition 39.0.6 (3): for a closed convex process, every nonempty fiber
`A[[u]]` has recession cone `A[[0]]`. Hence all fibers over
points of `A.dom` share the same recession cone `A0`. This bridge form uses explicit nonemptiness
of the singleton fiber. -/
theorem recessionCone_image_singleton_eq_image_zero_of_nonempty
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜)
    (hA_closed : A.IsClosed)
    (u : U) (hu : (A[[u]]).Nonempty) :
    0⁺[𝕜] (A[[u]]) = A[[0]] := by
  rcases hu with ⟨x, hx⟩
  rcases SetRel.mem_image.mp hx with ⟨u', hu', hu'x⟩
  have hu' : u' = u := by simpa using hu'
  have hudom : u ∈ A.dom := ⟨x, by simpa [hu'] using hu'x⟩
  exact hA.recessionCone_image_singleton_eq_image_zero hA_closed u hudom

end IsConvexProcess

end RecessionFibers

end SetRel

/-! ### Proposition_39_0_7 (from Chap08) -/
open scoped SetRel Rockafellar

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.7 introduces two operations on convex processes: codomain
  scalar multiplication `(a A)u := a (A u)` and fiberwise Minkowski addition
  `(A + B)u := A u + B u`.
- `core/canonical`: convex processes already live on the relation owner `A : SetRel U X` via
  `A.IsConvexProcess R`, and the chapter already provides the canonical fiberwise-sum owner `+ᶠ`
  on subsets of a product.
- `bridge/view`: codomain scalar multiplication is post-composition with the graph relation of the
  output scaling map `a • ·`, while the source domain formula is the `SetRel.dom` projection of
  the graph-level fiberwise sum.

Primary mathematical domain:
- convex processes as graph relations in ordered semimodule-like settings.

Domain-style sampling used here:
- `SetRel.dom`, `SetRel.image`, and relation membership notation from `Mathlib.Data.Rel`;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `Set.fiberwiseSum`, notation `+ᶠ`, and `Set.mem_fiberwiseSum` from `Chap01.Theorem_3_6`.

Primitive data vs derived API:
  `A.IsConvexProcess R`, post-composition `A ○ (a • ·).graph`, and the chapter
  fiberwise-sum owner `A +ᶠ B`;
- derived API: the two closure theorems for convex processes and the domain identity for the
  fiberwise sum.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owner.
-/

section RightScalarMul

variable {S : Type*} {U : Type v} {X : Type w}
variable [SMul S X]

/-- Source-facing notation for Proposition 39.0.7 (1): `a •ʳ A` denotes codomain scaling of the
process `A` by the scalar `a`. -/
scoped[SetRel] infixr:73 " •ʳ " => fun a A => A ○ Function.graph (a • ·)

-- Proof sketch: unfold `a •ʳ A` as relation composition with a graph relation, then use
-- `SetRel.mem_comp` and `Function.mem_graph`.
/-- Membership in `a •ʳ A` means that the output is a scalar multiple of some output related by
`A` over the same input. -/
@[simp] theorem mem_rightScalarMul_iff {a : S} {A : SetRel U X} {u : U} {x : X} :
    u ~[a •ʳ A] x ↔ ∃ y : X, u ~[A] y ∧ a • y = x := by
  constructor
  · intro hux
    rcases SetRel.mem_comp.mp hux with ⟨y, huy, hyx⟩
    exact ⟨y, huy, Function.mem_graph.mp hyx⟩
  · rintro ⟨y, huy, hyx⟩
    exact SetRel.mem_comp.mpr ⟨y, huy, Function.mem_graph.mpr hyx⟩

end RightScalarMul

section FiberwiseSum

variable {U : Type u} {X : Type v}
variable [Add X]

/-- Relation-surface membership for the chapter fiberwise sum owner. -/
@[simp] theorem mem_fiberwiseSum {A B : SetRel U X} {u : U} {x : X} :
    u ~[A +ᶠ B] x ↔ ∃ x₁ x₂ : X, u ~[A] x₁ ∧ u ~[B] x₂ ∧ x₁ + x₂ = x := by
  simp [Set.mem_fiberwiseSum]

end FiberwiseSum

namespace IsConvexProcess

section RightScalarMul

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {S : Type*}
variable {X : Type w} [AddCommMonoid X] [SMul R X] [DistribSMul S X] [SMulCommClass S R X]
variable {A : SetRel U X}

-- Proof sketch: `a •ʳ A = A ○ (a • ·).graph`; combine convex-process
-- closure of `A` with closure of post-composition by the graph of codomain scaling.
/-- Proposition 39.0.7 (1): codomain scaling `(a A)u := a (A u)` preserves convex processes.
The source statement is recovered by taking `S = R`. -/
theorem rightScalarMul (hA : A.IsConvexProcess R) (a : S) :
    (a •ʳ A).IsConvexProcess R := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro c p hc hp
    rcases p with ⟨u, x⟩
    change c • u ~[a •ʳ A] c • x
    rcases mem_rightScalarMul_iff.mp hp with ⟨y, hy, hyx⟩
    refine mem_rightScalarMul_iff.mpr ⟨c • y, hA.smul_mem hc hy, ?_⟩
    calc
      a • (c • y) = c • (a • y) := by simpa using (smul_comm a c y)
      _ = c • x := by rw [hyx]
  · rintro ⟨u₁, x₁⟩ hx ⟨u₂, x₂⟩ hy c d hc hd hcd
    rcases mem_rightScalarMul_iff.mp hx with ⟨y₁, hy₁, hyx₁⟩
    rcases mem_rightScalarMul_iff.mp hy with ⟨y₂, hy₂, hyx₂⟩
    change c • u₁ + d • u₂ ~[a •ʳ A] (c • x₁ + d • x₂)
    refine mem_rightScalarMul_iff.mpr ⟨c • y₁ + d • y₂, ?_, ?_⟩
    · simpa [Prod.smul_mk, Prod.mk_add_mk] using hA.convex hy₁ hy₂ hc hd hcd
    · calc
        a • (c • y₁ + d • y₂) = a • (c • y₁) + a • (d • y₂) := smul_add a _ _
        _ = c • (a • y₁) + d • (a • y₂) := by
          rw [smul_comm a c y₁, smul_comm a d y₂]
        _ = c • x₁ + d • x₂ := by rw [hyx₁, hyx₂]
  · exact mem_rightScalarMul_iff.mpr ⟨0, hA.zero_mem, by simp⟩

end RightScalarMul

section FiberwiseSum

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [DistribSMul R X]
variable {A B : SetRel U X}

-- Proof sketch: combine graph witnesses fiberwise. Addition in each process provides the two
-- witnesses over `u₁ + u₂`, positive scalar closure scales each witness separately, and
-- `Convex.fiberwiseSum` supplies convexity of the graph-level sum.
/-- Proposition 39.0.7 (2): the fiberwise Minkowski sum `(A + B)u := A u + B u` of two convex
processes is again a convex process. -/
theorem fiberwiseSum (hA : A.IsConvexProcess R) (hB : B.IsConvexProcess R) :
    SetRel.IsConvexProcess R (A +ᶠ B) := by
  refine ⟨⟨?_, Convex.fiberwiseSum hA.convex hB.convex⟩, ?_⟩
  · intro c p hc hp
    rcases p with ⟨u, x⟩
    rcases mem_fiberwiseSum.mp hp with ⟨x₁, x₂, hx₁, hx₂, rfl⟩
    exact mem_fiberwiseSum.mpr
      ⟨c • x₁, c • x₂, hA.smul_mem hc hx₁, hB.smul_mem hc hx₂, by simp [smul_add]⟩
  · exact mem_fiberwiseSum.mpr
      ⟨0, 0, hA.zero_mem, hB.zero_mem, by simp⟩

end FiberwiseSum

end IsConvexProcess

section FiberwiseSum

variable {U : Type u} {X : Type v}
variable [Add X]

-- Proof sketch: unfold `SetRel.dom` and `SetRel.mem_fiberwiseSum`; a witness in the fiberwise sum
-- over `u` is exactly a pair of witnesses showing `u ∈ A.dom` and `u ∈ B.dom`, and conversely.
/-- Proposition 39.0.7 (3): the domain of the fiberwise Minkowski sum is the intersection of the
domains of the two processes. -/
theorem dom_fiberwiseSum (A B : SetRel U X) :
    SetRel.dom (A +ᶠ B) = A.dom ∩ B.dom := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    rcases mem_fiberwiseSum.mp hx with ⟨x₁, x₂, hx₁, hx₂, _⟩
    exact ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    refine ⟨x₁ + x₂, ?_⟩
    exact mem_fiberwiseSum.mpr ⟨x₁, x₂, hx₁, hx₂, rfl⟩

end FiberwiseSum

end SetRel

/-! ### Proposition_39_0_8 (from Chap08) -/
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
