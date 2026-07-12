import Mathlib
import StacksProject_2024.Chap04.Lemma_4_34_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open FibredCategoryMor

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryOver

/- Domain-style sampling for `4.34.2.1`:
- primary domain: categories fibred over a fixed base `C` and the relative/absolute inertia
  attached to a morphism of fibred categories.
- inspected owner declarations:
  `FibredCategoryOver`,
  `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.toFunctor`,
  `CategoryTheory.relativeInertiaProjection`,
  `CategoryTheory.relativeInertiaProjection_isFibered`.
- best owner abstraction: `FibredCategoryOver C`; the underlying `CategoryOver C` object is a
  derived view, not the main owner.
- primitive-vs-derived split: the source-facing owners are the fibred categories
  `relativeInertiaOver F` and `absoluteInertiaOver X`; the underlying `Cat/C` objects and the
  structure map to `X` are bridge/view data.

Source/core/bridge triage:
- `source-facing`: `FibredCategoryOver.relativeInertiaOver`,
  `FibredCategoryOver.absoluteInertiaOver`;
- `core/canonical`: `FibredCategoryOver.ofFunctor`, `FibredCategoryMor.toFunctor`,
  `relativeInertiaProjection`, and `relativeInertiaProjection_isFibered`;
- `bridge/view`: the `CategoryOver` views of those owners and
  `CategoryOver.relativeInertiaStructureMap`. -/

-- Proof sketch: unpack the identity functor over `C`; the chosen lift of `f` is just `f`,
-- and the universal property is the ordinary categorical uniqueness for identities.
/-- The identity functor of `C` sends every arrow to a strongly cartesian lift of itself. -/
private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f := sorry

/-- The identity functor of the base category is fibered. -/
private instance idFunctor_isFibered : (𝟭 C).IsFibered := sorry

-- Proof sketch: a fibred category projection preserves its own strongly cartesian arrows by
-- definition, so the structure morphism to the base fibred category is cartesian-preserving.
/-- The projection of a fibred category over `C` preserves strongly cartesian morphisms. -/
private theorem toBase_preservesStronglyCartesian
    (X : FibredCategoryOver C) :
    PreservesStronglyCartesian (X.toBasedCategory.toBase) := sorry

/-- The canonical morphism from a fibred category over `C` to the base fibred category
`(C, 𝟭 C)`. -/
abbrev toBase (X : FibredCategoryOver C) :
    X ⟶ FibredCategoryOver.ofFunctor (𝟭 C) :=
  ofBasedFunctor X.toBasedCategory.toBase
    (toBase_preservesStronglyCartesian X)

variable {X Y : FibredCategoryOver C}

/-- The relative inertia over `C` attached to a morphism of fibred categories
`F : X ⟶ Y`. -/
abbrev relativeInertiaOver (F : X ⟶ Y) :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor
    (relativeInertiaProjection (toFunctor F) X.p)

/-- The absolute inertia over `C` is the specialization of the relative inertia of the structure
morphism `X ⟶ (C, 𝟭 C)`. -/
abbrev absoluteInertiaOver (X : FibredCategoryOver C) :
    FibredCategoryOver C :=
  relativeInertiaOver (toBase X)

end FibredCategoryOver

namespace CategoryOver

variable {X Y : CategoryOver C}

/-- The relative inertia over `C`, packaged directly in `Cat/C`. -/
abbrev relativeInertiaOver (F : X ⥤ᵇ Y) :
    CategoryOver C :=
  BasedCategory.ofFunctor (relativeInertiaProjection F.toFunctor X.p)

/-- The absolute inertia over `C`, packaged directly in `Cat/C`. -/
abbrev absoluteInertiaOver (X : CategoryOver C) :
    CategoryOver C :=
  relativeInertiaOver X.toBase

/-- 4.34.2.1: the relative inertia `\mathcal I_{\mathcal X / \mathcal Y}` has its canonical
`Cat/\mathcal C` bridge to `\mathcal X`, obtained by packaging
`relativeInertiaStructureFunctor F.toFunctor` over `C`. -/
abbrev relativeInertiaStructureMap (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ X :=
  { toFunctor := relativeInertiaStructureFunctor F.toFunctor
    w := rfl }

-- Proof sketch: unfold the bundled based functor defining the relative inertia structure map.
/-- The relative inertia structure map has the expected underlying forgetful functor. -/
theorem relativeInertiaStructureMap_toFunctor (F : X ⥤ᵇ Y) :
    (relativeInertiaStructureMap F).toFunctor =
      relativeInertiaStructureFunctor F.toFunctor := sorry

end CategoryOver

end CategoryTheory
