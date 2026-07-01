import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

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
