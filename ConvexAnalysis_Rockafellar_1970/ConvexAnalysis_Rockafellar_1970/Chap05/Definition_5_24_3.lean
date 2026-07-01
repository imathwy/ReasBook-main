import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.3 introduces the graph of the subdifferential multifunction,
  i.e. the set of pairs `(x, x⋆)` with `x⋆ ∈ ∂f(x)`.
- `core/canonical`: the chapter owner for the subdifferential itself is `_root_.subdifferentialAt`,
  while graph-shaped multivalued objects in the project are organized as relations `SetRel`.
- `bridge/view`: the source graph of `∂f` is therefore the canonical relation view
  `subdifferentialGraph f Y : SetRel E Y` (defaulting to `Y = StrongDual 𝕜 E`), not a second
  packaged owner beside `_root_.subdifferentialAt`.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean),
  the Chapter 23 owner for the subdifferential itself;
- `SetRel`, `SetRel.dom`, and `SetRel.cod` from mathlib's
  [Data/Rel](.lake/packages/mathlib/Mathlib/Data/Rel.lean),
  the canonical owner layer for graphs/domains/ranges of multivalued mappings;
- `Function.subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean),
  the Fréchet-Riesz vector-valued bridge reused in the inner-product-space specialization below.

Primitive data vs derived API:
- primitive owner input: the subdifferential owner `_root_.subdifferentialAt f x`;
- derived bridge API: the relation `subdifferentialGraph f`, the source-set image owner
  `subdifferentialImage f S`, and their pointwise membership theorems.

Layer target: `bridge/view`. Definition 5.24.3 does not introduce a second owner beside
`subdifferentialAt`; it places the existing owner in the chapter's canonical `SetRel` graph/image
language.
-/

/-- Definition 5.24.3: the graph of the subdifferential multifunction is the relation whose pairs
are exactly `(x, x⋆)` with `x⋆ ∈ ∂f(x)`. The codomain owner is pairing-parametric and defaults to
`StrongDual 𝕜 E`. -/
abbrev subdifferentialGraph (f : E → WithTopBot 𝕜)
    (Y : Type (max u v) := StrongDual 𝕜 E)
    [HasPairing E Y 𝕜] : SetRel E Y :=
  {p | p.2 ∈ ∂[Y]f(p.1)}

scoped[Rockafellar] notation "gph∂[" Y_ "](" f ")" =>
  _root_.subdifferentialGraph (f := f) (Y := Y_)
scoped[Rockafellar] notation "gph∂(" f ")" =>
  _root_.subdifferentialGraph (f := f)

/-- A pair belongs to the canonical graph relation of the subdifferential exactly when its second
coordinate is a subgradient at its first coordinate. -/
@[simp] theorem mem_subdifferentialGraph {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} {xStar : Y} :
    x ~[gph∂[Y](f)] xStar ↔ xStar ∈ ∂[Y]f(x) :=
  by rfl

/-- Pairing transport API for `subdifferentialGraph`: if two pairings on `(E, Y, 𝕜)` are
pointwise equal, they induce the same graph relation. -/
theorem subdifferentialGraph_eq_of_pairing_eq
    {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    {pairing₁ pairing₂ : HasPairing E Y 𝕜}
    (hpair : ∀ x : E, ∀ y : Y,
      @HasPairing.pairing E Y 𝕜 pairing₁ x y =
        @HasPairing.pairing E Y 𝕜 pairing₂ x y) :
    @_root_.subdifferentialGraph 𝕜 _ _ _ E _ _ _ f Y pairing₁ =
      @_root_.subdifferentialGraph 𝕜 _ _ _ E _ _ _ f Y pairing₂ := by
  ext p
  rcases p with ⟨x, xStar⟩
  change
      xStar ∈ @_root_.subdifferentialAt 𝕜 _ _ E _ f x Y pairing₁ ↔
      xStar ∈ @_root_.subdifferentialAt 𝕜 _ _ E _ f x Y pairing₂
  rw [subdifferentialAt_eq_of_pairing_eq (f := f) (x := x) (Y := Y) hpair]

/-- The source set `∂f(S)` of all subgradients taken at base points in `S`, defined intrinsically
as the relation image of `S` under the canonical graph owner `subdifferentialGraph`. The codomain
owner is pairing-parametric and defaults to `StrongDual 𝕜 E`. -/
abbrev subdifferentialImage (f : E → WithTopBot 𝕜) (S : Set E)
    (Y : Type (max u v) := StrongDual 𝕜 E) [HasPairing E Y 𝕜] : Set Y :=
  SetRel.image (subdifferentialGraph (Y := Y) f) S

scoped[Rockafellar] notation "∂[" Y_ "]" f "(" S ")" =>
  _root_.subdifferentialImage (f := f) (S := S) (Y := Y_)
scoped[Rockafellar] notation "∂" f "(" S ")" =>
  _root_.subdifferentialImage (f := f) (S := S)

/-- Pairing-level membership form of `subdifferentialImage`. -/
@[simp] theorem mem_subdifferentialImage_pairing {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {S : Set E} {xStar : Y} :
    xStar ∈ (∂[Y]f(S)) ↔ ∃ x ∈ S, xStar ∈ ∂[Y]f(x) := by
  constructor
  · intro hxStar
    rcases (SetRel.mem_image.mp hxStar) with ⟨x, hxS, hxGraph⟩
    exact ⟨x, hxS, (mem_subdifferentialGraph.mp hxGraph)⟩
  · rintro ⟨x, hxS, hxSubgrad⟩
    exact SetRel.mem_image.mpr ⟨x, hxS, (mem_subdifferentialGraph.mpr hxSubgrad)⟩

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

/-- Membership in `∂f(S)` means exactly that the candidate dual vector belongs to
`subdifferentialAt f x` at some base point `x ∈ S`. -/
@[simp] theorem mem_subdifferentialImage
    {f : E → WithTopBot 𝕜} {S : Set E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂ f(S)) ↔ ∃ x ∈ S, xStar ∈ ∂ f at x := by
  exact
    mem_subdifferentialImage_pairing
      (f := f) (Y := StrongDual 𝕜 E) (S := S) (xStar := xStar)

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
Source/core/bridge triage for the inner-product-space graph bridge.

- `source-facing`: later Section 24 items in textbook coordinate models speak about vector
  subgradients `x⋆ ∈ ∂f(x)`.
- `core/canonical`: the owner graph remains `_root_.subdifferentialGraph f`, here specialized to
  the continuous-dual codomain.
- `bridge/view`: `Function.subdifferentialGraph f` transports that owner along the canonical
  inner-product-to-dual map, so it is only the vector-valued graph view of the same object.

Domain-style sampling used here:
- `_root_.subdifferentialGraph` from this file;
- `Function.subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean);
- mathlib's canonical embedding owner `InnerProductSpace.toDualMap`, and its complete-space
  specialization equivalence `InnerProductSpace.toDual`.

Primitive data vs derived API:
- primitive owner: `_root_.subdifferentialGraph f`, the canonical dual-valued graph relation;
- derived bridge API: the relation `Function.subdifferentialGraph f`, obtained by pulling that
  owner back along `Prod.map id (InnerProductSpace.toDualMap 𝕜 E)`, and its pointwise membership
  simplification in vector form.

Layer target: `bridge/view`.
-/

namespace Function

/-- On an ordered inner-product space, the vector-valued subdifferential graph is the canonical
pullback of the intrinsic dual-valued graph `_root_.subdifferentialGraph` along
`InnerProductSpace.toDualMap` on the second coordinate. -/
abbrev subdifferentialGraph (f : E → WithTopBot 𝕜) : SetRel E E :=
  (Prod.map id (InnerProductSpace.toDualMap 𝕜 E)) ⁻¹' (_root_.subdifferentialGraph f)

@[simp] theorem mem_subdifferentialGraph {f : E → WithTopBot 𝕜} {x xStar : E} :
    x ~[subdifferentialGraph f] xStar ↔ xStar ∈ subdifferentialAt f x :=
  by rfl

/-- The domain of the vector-valued subdifferential graph agrees with the domain of the
intrinsic dual-valued graph on complete spaces. This is the owner-level Fréchet-Riesz bridge for
graph-domain
statements. -/
theorem subdifferentialGraph_dom_eq_intrinsic (f : E → WithTopBot 𝕜) [CompleteSpace E] :
    (subdifferentialGraph f).dom = (_root_.subdifferentialGraph f).dom := by
  ext x
  rw [SetRel.mem_dom, SetRel.mem_dom]
  constructor
  · rintro ⟨xStar, hxStar⟩
    refine ⟨InnerProductSpace.toDualMap 𝕜 E xStar, ?_⟩
    have hxMem : xStar ∈ subdifferentialAt f x :=
      Function.mem_subdifferentialGraph.mp hxStar
    have hxDual : InnerProductSpace.toDualMap 𝕜 E xStar ∈ ∂ f at x := by
      change InnerProductSpace.toDualMap 𝕜 E xStar ∈
          _root_.subdifferentialAt (Y := StrongDual 𝕜 E) f x
      exact hxMem
    exact _root_.mem_subdifferentialGraph.mpr hxDual
  · rintro ⟨xDual, hxDual⟩
    refine ⟨(InnerProductSpace.toDual 𝕜 E).symm xDual, ?_⟩
    have hrepr :
        InnerProductSpace.toDualMap 𝕜 E ((InnerProductSpace.toDual 𝕜 E).symm xDual) = xDual := by
      ext z
      change inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm xDual) z = xDual z
      exact InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (E := E) (x := z) (y := xDual)
    have hxDualMem : xDual ∈ ∂ f at x :=
      _root_.mem_subdifferentialGraph.mp hxDual
    have hxMem : (InnerProductSpace.toDual 𝕜 E).symm xDual ∈ subdifferentialAt f x := by
      change InnerProductSpace.toDualMap 𝕜 E ((InnerProductSpace.toDual 𝕜 E).symm xDual) ∈
          _root_.subdifferentialAt (Y := StrongDual 𝕜 E) f x
      rw [hrepr]
      exact hxDualMem
    exact Function.mem_subdifferentialGraph.mpr hxMem

end Function

end
