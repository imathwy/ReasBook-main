import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap12.Lemma_12_19_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped CategoryTheory ZeroObject

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜]

/- Domain-style sampling for Definition 13.13.1:
- primary domain: filtered objects in a category with zero object and the full subcategory cut out
  by the finiteness predicate on filtrations;
- sampled owner declarations:
  `FilteredObject`,
  `FilteredObject.IsFinite`,
  `FilteredObject.forget`,
  `FilteredObject.associatedGradedFunctor`,
  `FullSubcategory`,
  `ι`;
- owner abstraction: the source-facing owner for this item is the full subcategory
  `finiteFilteredObjectCat 𝒜`, built canonically as
  `(FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))).FullSubcategory`;
- source/core/bridge triage:
  `source-facing`: the category `Fil^f(𝒜)` of finite filtered objects;
  `core/canonical`: `FilteredObject 𝒜` together with the generic owner
    `(FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))).FullSubcategory`;
  `bridge/view`: the notation `Fil^f(𝒜)` for that full subcategory.

Primitive data versus derived API:
- primitive data: the ambient filtered-object owner `FilteredObject 𝒜` and the finiteness
  predicate `FilteredObject.IsFinite`;
-- derived API: the full subcategory owner `finiteFilteredObjectCat 𝒜` and the textbook notation
  `Fil^f(𝒜)`, together with the canonical forgetful and associated-graded functors obtained by
  restricting `FilteredObject.forget` and `FilteredObject.associatedGradedFunctor` along the
  full-subcategory inclusion;
-- no parallel inclusion wrapper is kept: the canonical inclusion is used directly as
  `ι : Fil^f(𝒜) ⥤ Fil(𝒜)`.

This item is therefore `source-facing`, not a recall-only bridge: Definition `13.13.1` is the
right owner file for the finite filtered category itself, while later files should reuse this owner
rather than re-declare it. -/

/-- Definition 13.13.1: for a category `𝒜` with zero object, the category of finite filtered
objects is the full subcategory of `FilteredObject 𝒜` on objects whose filtration is finite. -/
abbrev finiteFilteredObjectCat (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroObject 𝒜] :=
  ObjectProperty.FullSubcategory (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))

/- The Stacks Project writes the category of finite filtered objects as `Fil^f(𝒜)`. This is
notation for the source-facing owner `finiteFilteredObjectCat 𝒜`. -/
scoped notation "Fil" "^f" "(" C ")" => finiteFilteredObjectCat C

/- Companion recall: no separate `finiteFilteredObjectInclusion` wrapper is introduced here; the
canonical inclusion `Fil^f(𝒜) ⥤ Fil(𝒜)` is used directly as the object-property inclusion
`ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))`. -/
#check
  (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) :
    Fil^f(𝒜) ⥤ Fil(𝒜))

/- Companion check: the Stacks notation `Fil^f(𝒜)` is this recalled owner. -/
#check (Fil^f(𝒜))

instance : ObjectProperty.ContainsZero (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) where
  exists_zero := by
    letI : HasZeroMorphisms 𝒜 := by
      exact HasZeroObject.zeroMorphismsOfZeroObject (C := 𝒜)
    letI : Subsingleton (Subobject ((0 : Fil(𝒜)).obj)) :=
      Subobject.subsingleton_of_isZero
        ((FilteredObject.forget : Fil(𝒜) ⥤ 𝒜).map_isZero (isZero_zero _))
    refine ⟨0, isZero_zero _, ?_⟩
    exact ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

instance : HasZeroObject (Fil^f(𝒜)) :=
  inferInstance

section RestrictionFunctors

variable (C : Type u) [Category.{v} C] [HasZeroObject C]

/-- The canonical forgetful functor from finite filtered objects to the ambient category. -/
abbrev finiteFilteredObjectForgetFunctor : Fil^f(C) ⥤ C :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(C))) ⋙ FilteredObject.forget

/-- The canonical associated-graded functor on finite filtered objects. -/
abbrev finiteFilteredObjectAssociatedGradedFunctor [HasZeroMorphisms C] [HasCokernels C] :
    Fil^f(C) ⥤ GradedObject ℤ C :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(C))) ⋙
    FilteredObject.associatedGradedFunctor

/-- The termwise associated-graded functor on cochain complexes of finite filtered objects. -/
abbrev finiteFilteredObjectAssociatedGradedCochainFunctor [HasZeroMorphisms C] [HasCokernels C] :
    CochainComplex (finiteFilteredObjectCat C) ℤ ⥤ CochainComplex (GradedObject ℤ C) ℤ :=
  (finiteFilteredObjectAssociatedGradedFunctor C).mapHomologicalComplex (ComplexShape.up ℤ)

end RestrictionFunctors

end CategoryTheory
