import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3

noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.2 introduces the range of the subdifferential multifunction,
  written in the source as the union of fibers `⋃ {∂f(x)}`.
- `core/canonical`: for set-valued maps, mathlib's owner abstraction for the range is the relation
  codomain `SetRel.cod`. The primitive owner object here is the pairing-level relation
  `(x, x⋆) ↦ x⋆ ∈ ∂[Y]f(x)`.
- `bridge/view`: the textbook union formula for `range ∂f` is the specialization of `SetRel.cod`
  to this relation.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from
  [Definition_23_0_6](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_23_0_6.lean),
  which is the chapter owner for the subdifferential itself;
- `SetRel.cod` and `SetRel.mem_cod` from mathlib's
  [Data/Rel](.lake/packages/mathlib/Mathlib/Data/Rel.lean), the canonical owner API for the
  codomain/range of a relation.
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean),
  which provides the stronger graph/image bridge layer used below.

Primitive data vs derived API:
- primitive owner: the pairing-level relation `(x, x⋆) ↦ x⋆ ∈ ∂[Y]f(x)`;
- derived API: the source-facing union reformulation of its codomain;
  the existence-style membership shape is already the exact canonical owner theorem
  `SetRel.mem_cod`.

Layer target: `bridge/view`. The item does not introduce a second owner beside
`subdifferentialAt`; it specializes the canonical relation-codomain owner to the subdifferential
relation, with the graph/image lemmas kept as bridge API.
-/

set_option quotPrecheck false in
/-- Definition 5.24.2: the range of `∂f` is the codomain of its subdifferential relation. -/
abbrev codSubdifferential (f : E → WithTopBot 𝕜) {Y : Type (max u v)} [HasPairing E Y 𝕜] :
    Set Y :=
  SetRel.cod (fun p : E × Y ↦
    Prod.snd p ∈ subdifferentialAt (Y := Y) f (Prod.fst p))

set_option quotPrecheck false in
scoped[Rockafellar] notation "cod∂[" Y_ "](" f ")" =>
  _root_.codSubdifferential (f := f) (Y := Y_)

/-- A dual-side point lies in `cod∂[Y](f)` exactly when it is a subgradient at some base point. -/
@[simp] theorem mem_codSubdifferential {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {xStar : Y} :
    xStar ∈ cod∂[Y](f) ↔ ∃ x, xStar ∈ ∂[Y]f(x) := by
  rw [SetRel.mem_cod]
  exact Iff.rfl

/-- Definition 5.24.2, textbook wording: the range of `∂f` is the union of the fibers
`subdifferentialAt f x`. -/
theorem subdifferentialGraph_cod_eq_iUnion_subdifferentialAt (f : E → WithTopBot 𝕜)
    {Y : Type (max u v)} [HasPairing E Y 𝕜] :
    cod∂[Y](f) = ⋃ x, ∂[Y]f(x) := by
  ext xStar
  constructor
  · intro hxStar
    rcases (mem_codSubdifferential (f := f) (Y := Y) (xStar := xStar)).mp hxStar with ⟨x, hxSubgrad⟩
    exact Set.mem_iUnion.mpr ⟨x, hxSubgrad⟩
  · intro hxStar
    rcases Set.mem_iUnion.mp hxStar with ⟨x, hxSubgrad⟩
    exact (mem_codSubdifferential (f := f) (Y := Y) (xStar := xStar)).mpr ⟨x, hxSubgrad⟩

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

section

variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

set_option quotPrecheck false in
scoped[Rockafellar] notation "cod∂(" f ")" =>
  _root_.codSubdifferential (f := f) (Y := StrongDual 𝕜 E)

end

/-- The canonical range owner `cod∂[Y](f)` is the image of `univ` under the subdifferential
graph relation, i.e. the global subdifferential image. -/
theorem codSubdifferential_eq_subdifferentialImage_univ
    (f : E → WithTopBot 𝕜) {Y : Type (max u v)} [HasPairing E Y 𝕜] :
    cod∂[Y](f) = subdifferentialImage (f := f) (S := Set.univ) (Y := Y) := by
  change (subdifferentialGraph (Y := Y) f).cod =
      SetRel.image (subdifferentialGraph (Y := Y) f) Set.univ
  exact (SetRel.image_univ_right (R := subdifferentialGraph (Y := Y) f)).symm

/-- Default-codomain specialization of the range owner: `cod∂(f)` is exactly the global
subdifferential image at codomain `StrongDual 𝕜 E`. -/
theorem codSubdifferential_eq_subdifferentialImage_univ_default
    [HasPairing E (StrongDual 𝕜 E) 𝕜] (f : E → WithTopBot 𝕜) :
    cod∂(f) = subdifferentialImage (f := f) (S := Set.univ) := by
  simpa using codSubdifferential_eq_subdifferentialImage_univ
    (f := f) (Y := StrongDual 𝕜 E)

end

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
Source/core/bridge triage for the inner-product-space range bridge.

- `source-facing`: later Section 24 items in the textbook model speak about vector
  subgradients.
- `core/canonical`: the owner range remains `_root_.subdifferentialGraph f |>.cod`, valued in the
  continuous dual.
- `bridge/view`: `Function.subdifferentialGraph f` transports that owner graph along
  `InnerProductSpace.toDualMap 𝕜 E`, so its codomain is exactly the vector-valued range of `∂f`.

Domain-style sampling used here:
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean);
- `Function.subdifferentialAt` and `Function.subdifferentialGraph` from the Chapter 23/24 owner
  file graph;
- mathlib's canonical inner-product-to-dual map `InnerProductSpace.toDualMap`.

Primitive data vs derived API:
- primitive owner: `Function.subdifferentialGraph f`;
- derived API: the source-facing union reformulation of
  `(Function.subdifferentialGraph f).cod`; the existence-style membership shape is already the
  exact owner theorem `SetRel.mem_cod`.

Layer target: `bridge/view`.
-/

namespace Function

/-- Vector-valued range owner for the inner-product-space bridge. -/
scoped[Rockafellar] notation "cod∂ᵥ(" f ")" => SetRel.cod (Function.subdifferentialGraph f)

/-- Definition 5.24.2, textbook wording on an ordered inner-product space: the range of the
vector-valued subdifferential is the union of the sets `subdifferentialAt f x`. -/
theorem subdifferentialGraph_cod_eq_iUnion_subdifferentialAt (f : E → WithTopBot 𝕜) :
    cod∂ᵥ(f) = ⋃ x, ∂ᵥf(x) := by
  ext xStar
  constructor
  · intro hxStar
    rcases SetRel.mem_cod.mp hxStar with ⟨x, hxGraph⟩
    exact Set.mem_iUnion.mpr ⟨x, mem_subdifferentialGraph.mp hxGraph⟩
  · intro hxStar
    rcases Set.mem_iUnion.mp hxStar with ⟨x, hxSubgrad⟩
    exact SetRel.mem_cod.mpr ⟨x, mem_subdifferentialGraph.mpr hxSubgrad⟩

end Function

end
