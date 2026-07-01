import Mathlib
import stacks_project.Chap04.Definition_4_39_3
import stacks_project.Chap04.Lemma_4_35_9
import stacks_project.Chap04.Lemma_4_39_5

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open scoped Bicategory

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open Functor BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y Z : FibredInSetoidsOver C}

/- Domain-style sampling for Lemma 4.39.6:
- primary domain: categories fibred in setoids over a fixed base, their presheaves of fiberwise
  isomorphism classes, and the induced comparison with categories fibred in sets;
- inspected owner-level declarations:
  `Functor.fiberIsoClassPresheaf`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets`,
  `presheafToFibredInSetsOver`;
- best owner abstraction: the core/canonical owners are the presheaf
  `X.p.fiberIsoClassPresheaf` and the associated fibred-in-sets object
  `X.associatedFibredInSets`; the functorial constructions in this file should be thin bridge/view
  data built directly from those owners;
- primitive data: a bundled fibred-in-setoids object or morphism over `C`;
- derived API: the induced presheaf morphism on isomorphism classes, the induced fibred-in-sets
  morphism, and the quotient-level comparison on homs.

Source/core/bridge triage:
- `source-facing`: `fibredInSetoidsToPresheaf`, `fibredInSetoidsToFibredInSets`, and the final
  hom-level comparison;
- `core/canonical`: `Functor.fiberIsoClassPresheaf`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets`,
  `presheafToFibredInSetsOver`;
- `bridge/view`: the helper proofs relating morphisms in `FibredInSetoidsOver C` to morphisms of
  the associated presheaves and associated fibred-in-sets objects. -/

private noncomputable def fiberIsoClassPresheafMapApp
    (F : X ⟶ Y) (U : Cᵒᵖ) :
    (X.p.fiberIsoClassPresheaf).obj U →
      (Y.p.fiberIsoClassPresheaf).obj U :=
  isomorphismClasses.map
    ((FibredInGroupoidsMor.fiberFunctor F (unop U)).toCatHom)

-- Proof sketch: both composites apply the fiberwise map induced by `F` together with the canonical
-- pullback functors on `X` and `Y`; the commutation with the base projections gives a canonical
-- comparison in each target fiber, and setoidness makes that comparison unique on isomorphism
-- classes.
private theorem fiberIsoClassPresheafMap_naturality
    (F : X ⟶ Y) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (X.p.fiberIsoClassPresheaf).map f ≫
        fiberIsoClassPresheafMapApp F V =
      fiberIsoClassPresheafMapApp F U ≫
        (Y.p.fiberIsoClassPresheaf).map f := sorry

/-- A morphism of fibred categories over `C` induces a morphism between the presheaves of
isomorphism classes of objects in the fibers. -/
private noncomputable def fibredInSetoidsToPresheafMap (F : X ⟶ Y) :
    X.p.fiberIsoClassPresheaf ⟶ Y.p.fiberIsoClassPresheaf where
  app U := fiberIsoClassPresheafMapApp F U
  naturality := fun {_ _} f ↦ fiberIsoClassPresheafMap_naturality F f

-- Proof sketch: the identity morphism of `X` induces the identity map on each fiber, hence also
-- the identity natural transformation on the presheaf of isomorphism classes.
private theorem fibredInSetoidsToPresheafMap_id
    (X : FibredInSetoidsOver C) :
    fibredInSetoidsToPresheafMap (𝟙 X) =
      𝟙 X.p.fiberIsoClassPresheaf := sorry

-- Proof sketch: the presheaf map attached to a composite is computed fiberwise from the composite
-- of the induced fiber functors, so functoriality reduces to functoriality of those fiberwise
-- maps on isomorphism classes.
private theorem fibredInSetoidsToPresheafMap_comp
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    fibredInSetoidsToPresheafMap (F ≫ G) =
      fibredInSetoidsToPresheafMap F ≫ fibredInSetoidsToPresheafMap G := sorry

/-- The presheaf of isomorphism classes in the fibers defines a functor from categories fibred in
setoids over `C` to presheaves of sets on `C`. -/
noncomputable def fibredInSetoidsToPresheaf :
    FibredInSetoidsOver C ⥤ Presheaf.{max u₁ v₁} C where
  obj X := X.p.fiberIsoClassPresheaf
  map {X} {Y} F := fibredInSetoidsToPresheafMap F
  map_id X := by
    exact fibredInSetoidsToPresheafMap_id X
  map_comp F G := by
    exact fibredInSetoidsToPresheafMap_comp F G

/-- Lemma 4.39.6 (1): taking isomorphism classes in each fiber and then applying the category of
 elements construction defines a functor from categories fibred in setoids over `C` to categories
 fibred in sets over `C`, reusing the source-facing replacement object
 `FibredInSetoidsOver.associatedFibredInSets` from Lemma 4.39.5. -/
noncomputable abbrev fibredInSetoidsToFibredInSets :
    FibredInSetoidsOver C ⥤ FibredInSetsOver C :=
  fibredInSetoidsToPresheaf ⋙ presheafToFibredInSetsOver

-- Proof sketch: if two `1`-morphisms induce the same morphism after passing to isomorphism
-- classes, then for each source object their images in the target fiber are isomorphic. Because
-- the target is fibred in setoids, these fiberwise isomorphisms are unique and assemble into a
-- unique vertical natural isomorphism.
/-- If two `1`-morphisms become equal after applying
`fibredInSetoidsToFibredInSets`, then they are `2`-isomorphic. Uniqueness is supplied separately
by `fibredInSetoidsOverTwoIso_subsingleton`. -/
theorem fibredInSetoidsToFibredInSets_nonempty_iso_of_map_eq
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y}
    (h : fibredInSetoidsToFibredInSets.map F =
      fibredInSetoidsToFibredInSets.map G) :
    Nonempty (F ≅ G) := sorry

-- Proof sketch: any `2`-morphism between `F` and `G` is vertical over the identity on each base
-- object by `fibredCategoryMor_hom_isHomLift_id`; since `Y` is fibred in setoids, each component
-- lies in a thin fiber and is therefore unique. Componentwise uniqueness then forces equality of
-- `2`-morphisms.
/-- Any two `2`-morphisms between `1`-morphisms of categories fibred in setoids over `C` are
equal. -/
theorem fibredInSetoidsOverTwoHom_subsingleton
    {X Y : FibredInSetoidsOver C} (F G : X ⟶ Y) :
    Subsingleton (F ⟶ G) := sorry

-- Proof sketch: a `2`-isomorphism is determined by its forward and inverse `2`-morphisms, and
-- those are already unique by `fibredInSetoidsOverTwoHom_subsingleton`.
/-- Any two `2`-isomorphisms between `1`-morphisms of categories fibred in setoids over `C` are
equal. -/
theorem fibredInSetoidsOverTwoIso_subsingleton
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y}
    : Subsingleton (F ≅ G) := sorry

-- Proof sketch: combine the quotient-level presheaf statement below with the equivalence of
-- Lemma 4.38.6 between presheaves and categories fibred in sets.
/-- Every morphism between the associated categories fibred in sets comes from a `1`-morphism of
categories fibred in setoids. -/
theorem fibredInSetoidsToFibredInSets_map_surjective
    (X Y : FibredInSetoidsOver C) :
    Function.Surjective
      (fun F : X ⟶ Y ↦ fibredInSetoidsToFibredInSets.map F) := sorry

-- Proof sketch: a `2`-isomorphism between `F` and `G` is a vertical natural isomorphism whose
-- components lie in setoid fibers of `Y`; each component therefore identifies the images of every
-- source object in the quotient by isomorphism classes, so the induced morphisms in
-- `FibredInSetsOver C` agree.
/-- A `2`-isomorphism between morphisms of categories fibred in setoids induces equality after
applying `fibredInSetoidsToFibredInSets`. -/
theorem fibredInSetoidsToFibredInSets_map_eq_of_isomorphic
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y} (τ : F ≅ G) :
    fibredInSetoidsToFibredInSets.map F =
      fibredInSetoidsToFibredInSets.map G := sorry

-- Proof sketch: pass to the quotient of `X ⟶ Y` by `2`-isomorphism and use the previous theorem
-- to show that the induced target morphism depends only on the isomorphism class.
/-- The canonical map sending a `2`-isomorphism class of `1`-morphisms of categories fibred in
setoids over `C` to the induced morphism between their associated categories fibred in sets. -/
noncomputable def fibredInSetoidsHomIsoClassesToFibredInSetsHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) →
      (fibredInSetoidsToFibredInSets.obj X ⟶ fibredInSetoidsToFibredInSets.obj Y) :=
  fun q ↦
    Quotient.liftOn q
      (fun F : X ⟶ Y ↦ fibredInSetoidsToFibredInSets.map F)
      (fun _ _ hFG ↦ by
        rcases hFG with ⟨τ⟩
        exact fibredInSetoidsToFibredInSets_map_eq_of_isomorphic τ)

-- Proof sketch: surjectivity is exactly Lemma 4.39.6 (2). For injectivity, if two classes map to
-- the same target morphism, Lemma 4.39.6 (1) gives a `2`-isomorphism between chosen
-- representatives, and `fibredInSetoidsOverTwoIso_subsingleton` supplies its uniqueness, so the
-- quotient classes coincide.
/-- Lemma 4.39.6 (2): on each hom-category, passing to `2`-isomorphism classes identifies `1`-morphisms of
categories fibred in setoids with morphisms between their images under
`fibredInSetoidsToFibredInSets`. -/
theorem fibredInSetoidsHomIsoClassesToFibredInSetsHom_bijective
    (X Y : FibredInSetoidsOver C) :
    Function.Bijective (fibredInSetoidsHomIsoClassesToFibredInSetsHom X Y) := sorry

-- Proof sketch: if `X` is already fibred in sets, then its fibers are discrete, so the presheaf
-- of isomorphism classes is canonically identified with the presheaf of objects in the fibers.
-- Lemma 4.38.6 then shows that this canonical comparison exhibits `X` as lying in the image of
-- `fibredInSetoidsToFibredInSets`, and in particular as an equivalence over `C`.
/-- Lemma 4.39.6 (3): if `X` is already fibred in sets, then the canonical comparison from `X`,
viewed as a fibred-in-setoids object, to its image under `fibredInSetoidsToFibredInSets` is an
equivalence over the base. -/
theorem fibredInSetoidsToFibredInSets_obj_isEquivalenceOverBase_of_fibredInSets
    (X : FibredInSetsOver C) :
    FibredInSetoidsOver.IsEquivalenceOverBase
      ((FibredInSetoidsOver.toFibredInSets (X : FibredInSetoidsOver C)) :
        (X : FibredInSetoidsOver C) ⟶
          fibredInSetoidsToFibredInSets.obj (X : FibredInSetoidsOver C)) := by
  simpa using
    FibredInSetoidsOver.toFibredInSets_isEquivalenceOverBase
      (X : FibredInSetoidsOver C)

-- Proof sketch: a `2`-isomorphism between `F` and `G` is a vertical natural isomorphism whose
-- components lie in setoid fibers of `Y`; each component therefore identifies the images of every
-- source object in the quotient by isomorphism classes, so the induced presheaf maps are equal.
private theorem fibredInSetoidsToPresheaf_map_eq_of_isomorphic
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y} (τ : F ≅ G) :
    fibredInSetoidsToPresheaf.map F =
      fibredInSetoidsToPresheaf.map G := sorry

-- Proof sketch: an element of `isomorphismClasses.obj (Cat.of (X ⟶ Y))` is a
-- quotient by the relation of admitting a natural isomorphism; the previous theorem shows the map
-- to presheaf morphisms is constant on each equivalence class.
private theorem fibredInSetoidsToPresheaf_map_respects_isomorphismClasses
    (X Y : FibredInSetoidsOver C)
    {F G : X ⟶ Y}
    (hFG : CategoryTheory.IsIsomorphic F G) :
    fibredInSetoidsToPresheaf.map F =
      fibredInSetoidsToPresheaf.map G := sorry

-- Proof sketch: an element of `isomorphismClasses.obj (Cat.of (X ⟶ Y))` is a
-- quotient by the relation of admitting a natural isomorphism; the theorem above on unique
-- `2`-isomorphisms shows that the induced presheaf map depends only on the isomorphism class.
/-- The canonical map sending a `2`-isomorphism class of `1`-morphisms of categories fibred in
setoids over `C` to the induced morphism of presheaves of isomorphism classes. -/
private noncomputable def fibredInSetoidsHomIsoClassesToPresheafHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) →
      (X.p.fiberIsoClassPresheaf ⟶ Y.p.fiberIsoClassPresheaf) :=
  fun q ↦
    Quotient.liftOn q
      (fun F : X ⟶ Y ↦ fibredInSetoidsToPresheaf.map F)
      (fun _ _ hFG ↦
        fibredInSetoidsToPresheaf_map_respects_isomorphismClasses X Y hFG)

-- Proof sketch: the induced map to presheaf morphisms is well defined on `2`-isomorphism classes
-- by the previous helper. Fullness is the existence statement from the quotient construction of
-- Lemma 4.39.5, while faithfulness reduces equal induced presheaf maps to a unique vertical
-- natural isomorphism between the corresponding based functors because every fiber of the target
-- is a setoid.
/-- On each hom-category, the canonical map from `2`-isomorphism classes of `1`-morphisms to
morphisms of the associated presheaves of isomorphism classes is bijective. -/
private theorem fibredInSetoidsHomIsoClassesToPresheafHom_bijective
    (X Y : FibredInSetoidsOver C) :
    Function.Bijective (fibredInSetoidsHomIsoClassesToPresheafHom X Y) := sorry

namespace FibredInSetoidsOver

/-- On each hom-category, passing to `2`-isomorphism classes identifies
`1`-morphisms of categories fibred in setoids with morphisms between their associated categories
fibred in sets. -/
noncomputable def hom_isoClasses_equiv_fibredInSetsHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) ≃
      (fibredInSetoidsToFibredInSets.obj X ⟶ fibredInSetoidsToFibredInSets.obj Y) :=
  Equiv.ofBijective
    (fibredInSetoidsHomIsoClassesToFibredInSetsHom X Y)
    (fibredInSetoidsHomIsoClassesToFibredInSetsHom_bijective X Y)

/-- Passing to `2`-isomorphism classes of `1`-morphisms identifies
them canonically with morphisms of the associated presheaves of isomorphism classes. -/
noncomputable def hom_isoClasses_equiv_presheafHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) ≃
      (X.p.fiberIsoClassPresheaf ⟶ Y.p.fiberIsoClassPresheaf) :=
  Equiv.ofBijective
    (fibredInSetoidsHomIsoClassesToPresheafHom X Y)
    (fibredInSetoidsHomIsoClassesToPresheafHom_bijective X Y)

end FibredInSetoidsOver

end CategoryTheory
