import StacksProject_2024.Chap08.Lemma_8_8_1.HomPresheafComparison
import Mathlib.Tactic.StacksAttribute

universe u v uD vD w uY vY

namespace CategoryTheory

open Bicategory
open BasedFunctor
open FibredCategoryMor
open InducedCategory.Hom
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

/-- Helper for Lemma 8.8.1: universe-aligned restatement of `Presheaf.imageSieve_mem`. The
`fibredMorphismPresheafMap` presheaves are valued in the slice-site universe `Type (max u v)`, so
forcing the value universe through this bridge makes `WEqualsLocallyBijective`/sheafification
instances resolve. -/
theorem imageSieve_mem_type
    {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D)
    {F G : Dᵒᵖ ⥤ Type w} (f : F ⟶ G) [Presheaf.IsLocallySurjective K f]
    {T : D} (s : G.obj (op T)) :
    Presheaf.imageSieve f s ∈ K T :=
  Presheaf.imageSieve_mem K f s

/-- Helper for Lemma 8.8.1: universe-aligned restatement of `Presheaf.localPreimage`. -/
noncomputable def localPreimage_type
    {D : Type uD} [Category.{vD} D]
    {F G : Dᵒᵖ ⥤ Type w} (f : F ⟶ G)
    {T : D} (s : G.obj (op T)) {V : D} (g : V ⟶ T)
    (hg : Presheaf.imageSieve f s g) :
    F.obj (op V) :=
  Presheaf.localPreimage f s g hg

/-- Helper for Lemma 8.8.1: universe-aligned restatement of `Presheaf.app_localPreimage`. -/
theorem app_localPreimage_type
    {D : Type uD} [Category.{vD} D]
    {F G : Dᵒᵖ ⥤ Type w} (f : F ⟶ G)
    {T : D} (s : G.obj (op T)) {V : D} (g : V ⟶ T)
    (hg : Presheaf.imageSieve f s g) :
    f.app (op V) (localPreimage_type f s g hg) = G.map g.op s := by
  simpa using Presheaf.app_localPreimage f s g hg

/-- Helper for Lemma 8.8.1: the local surjectivity half of the stackification condition turns
the image sieve of a target-side Hom section into an explicit cover of the terminal object in the
slice site `J.over U`. -/
noncomputable abbrev stackification_hom_image_cover
    {X : FibredCategoryOver.{u, v, uY, vY} C} {Y : StackOver.{u, v, uY, vY} J}
    (G : X ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {U : C} {x y : X.p.Fiber U}
    [(J.over U).WEqualsLocallyBijective (Type vY)]
    (β :
      ((canonicalFiberPseudofunctor Y.p).presheafHom
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        ((FibredCategoryMor.fiberFunctor G U).obj y)).obj
          (Opposite.op (Over.mk (𝟙 U)))) :
    (J.over U).Cover (Over.mk (𝟙 U)) :=
  -- `fibredMorphismPresheafMap G x y` lies in `(J.over U).W`, hence is locally surjective; its
  -- image sieve at `β` is the desired cover.
  haveI := (hG.morphismPresheafMap_W U x y).isLocallySurjective
  ⟨Presheaf.imageSieve (fibredMorphismPresheafMap G x y) β,
    imageSieve_mem_type (J.over U) (fibredMorphismPresheafMap G x y) β⟩

/-- Helper for Lemma 8.8.1: over the canonical image-sieve cover of a target-side Hom section,
the stackification morphism admits explicit source-side local preimages. This extracts the exact
coverwise lifting operator promised by the source proof from `morphismPresheafMap_W`. -/
theorem stackification_coverwise_hom_lift
    {X : FibredCategoryOver.{u, v, uY, vY} C} {Y : StackOver.{u, v, uY, vY} J}
    (G : X ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {U : C} {x y : X.p.Fiber U}
    [(J.over U).WEqualsLocallyBijective (Type vY)]
    (β :
      ((canonicalFiberPseudofunctor Y.p).presheafHom
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        ((FibredCategoryMor.fiberFunctor G U).obj y)).obj
          (op (Over.mk (𝟙 U))))
    (I : (stackification_hom_image_cover (J := J) G hG (x := x) (y := y) β).Arrow) :
    ∃ γI :
        ((canonicalFiberPseudofunctor X.p).presheafHom x y).obj (op I.Y),
      (fibredMorphismPresheafMap G x y).app (op I.Y) γI =
        (((canonicalFiberPseudofunctor Y.p).presheafHom
          ((FibredCategoryMor.fiberFunctor G U).obj x)
          ((FibredCategoryMor.fiberFunctor G U).obj y)).map I.f.op) β := by
  -- `I.f` belongs to the image sieve of `β` (the cover), so the local preimage operator gives the
  -- required source-side section, and `app_localPreimage` is exactly the asserted equation.
  haveI := (hG.morphismPresheafMap_W U x y).isLocallySurjective
  exact
    ⟨localPreimage_type (fibredMorphismPresheafMap G x y) β I.f I.hf,
      app_localPreimage_type (fibredMorphismPresheafMap G x y) β I.f I.hf⟩

end

end CategoryTheory
