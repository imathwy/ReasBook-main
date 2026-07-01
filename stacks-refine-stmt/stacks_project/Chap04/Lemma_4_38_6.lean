import Mathlib
import stacks_project.Chap04.Definition_4_3_3
import stacks_project.Chap04.Definition_4_38_3
import stacks_project.Chap04.Example_4_38_5
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap04.Lemma_4_35_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS vS

namespace CategoryTheory

open Opposite Functor
open FibredInSetsOver

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 4.38.6:
- primary domain: categories fibred in sets over a fixed base and their comparison with
  `Type`-valued presheaves via the category-of-elements construction.
- inspected owner-level declarations:
  `Presheaf`,
  `FibredInSetsOver.ofFunctor`,
  `canonicalPullbackChoice`,
  `FibredInGroupoidsMor.fiberFunctor`.
- best owner abstraction: the source-facing equivalence is between the bundled owner
  `FibredInSetsOver C` and the chapter owner `Presheaf C`; the pullback action on fibers should be
  derived from the chapter owner `canonicalPullbackChoice`, and morphisms over the base should be
  read through the inherited ambient hom API rather than by re-packaging subcategory data.
- primitive data: the bundled fibred-in-sets object `X : FibredInSetsOver C` and its projection
  `X.p`.
- derived API: the functor `presheafToFibredInSetsOver`, the inverse object-presheaf
  `Functor.fiberObjectPresheaf`, and the equivalence statement.

Source/core/bridge triage:
- `source-facing`: `presheafToFibredInSetsOver`,
  `Functor.fiberObjectPresheaf`,
  `presheafToFibredInSetsOver_isEquivalence`;
- `core/canonical`: `FibredInSetsOver`, `Functor.Fiber`, `PullbackChoice.pullbackFunctor`,
  `FibredInGroupoidsMor.fiberFunctor`;
- `bridge/view`: the presheaf of fiber objects attached to a bundled fibred-in-sets object, with
  pullback action read through the owner bridge `canonicalPullbackChoice`. -/

/-- The textbook construction `F ↦ 𝒮_F` defines a functor from presheaves of sets on `C` to
categories fibred in sets over `C`. -/
def presheafToFibredInSetsOver :
    Presheaf.{max u v} C ⥤ FibredInSetsOver C where
  obj F := ofFunctor ((CategoryOfElements.π F).leftOp)
  map {X} {Y} α := by
    let G :
        BasedCategory.ofFunctor ((CategoryOfElements.π X).leftOp) ⥤ᵇ
          BasedCategory.ofFunctor ((CategoryOfElements.π Y).leftOp) :=
      { toFunctor := (CategoryOfElements.map α).op
        w := rfl }
    exact
      show ofFunctor ((CategoryOfElements.π X).leftOp) ⟶
          ofFunctor ((CategoryOfElements.π Y).leftOp) from
        ofAmbientHom (FibredInGroupoidsMor.ofBasedFunctor G)
  map_id := by
    intro F
    rfl
  map_comp := by
    intro F G H α β
    rfl

namespace Functor

variable {S : Type uS} [Category.{vS} S]

-- Proof sketch: this is the object function of the canonical pullback functor attached to
-- `canonicalPullbackChoice p`; discreteness of the fibers makes the resulting presheaf choice
-- invariant.
/-- Pullback along an identity morphism acts trivially on the fiber-object presheaf. -/
private noncomputable def fiberObjectPresheafMap
    (p : S ⥤ C) [IsFibredInSets p] {U V : Cᵒᵖ} (f : U ⟶ V) :
    p.Fiber (unop U) → p.Fiber (unop V) :=
  ((canonicalPullbackChoice p).pullbackFunctor f.unop).obj

private theorem fiberObjectPresheafMap_id
    (p : S ⥤ C) [IsFibredInSets p] (U : Cᵒᵖ) :
    fiberObjectPresheafMap p (𝟙 U) = id := sorry

-- Proof sketch: apply the composition comparison `mapComp` of the owner pseudofunctor and use
-- discreteness of the target fiber to identify the comparison isomorphism with equality on
-- underlying objects.
/-- Pullback of fiber objects is contravariantly functorial in the base morphism. -/
private theorem fiberObjectPresheafMap_comp
    (p : S ⥤ C) [IsFibredInSets p] {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    fiberObjectPresheafMap p (f ≫ g) =
      fiberObjectPresheafMap p g ∘ fiberObjectPresheafMap p f := sorry

/-- The presheaf sending `U` to the set of objects of the fiber `p.Fiber U`, obtained from the
object functions of the owner pullback system `canonicalPullbackChoice p`; discreteness makes the
result independent of the choice of pullback system. -/
noncomputable def fiberObjectPresheaf
    (p : S ⥤ C) [IsFibredInSets p] : Presheaf.{uS} C where
  obj U := p.Fiber (unop U)
  map f := fiberObjectPresheafMap p f
  map_id := fiberObjectPresheafMap_id p
  map_comp := fiberObjectPresheafMap_comp p

end Functor

private noncomputable def fibredInSetsOverToPresheafApp
    {X Y : FibredInSetsOver C} (F : X ⟶ Y) (U : Cᵒᵖ) :
    (X.p.fiberObjectPresheaf).obj U →
      (Y.p.fiberObjectPresheaf).obj U :=
  (fiberFunctor F (unop U)).obj

-- Proof sketch: both composites are objects of the discrete fiber `Y_{U}` equipped with the same
-- vertical comparison morphism to the image of `x`, so they are equal.
private theorem fibredInSetsOverToPresheafApp_naturality
    {X Y : FibredInSetsOver C} (F : X ⟶ Y) {U V : Cᵒᵖ} (f : U ⟶ V) :
    fibredInSetsOverToPresheafApp F V ∘
        (X.p.fiberObjectPresheaf).map f =
      (Y.p.fiberObjectPresheaf).map f ∘
        fibredInSetsOverToPresheafApp F U :=
  sorry

/-- A morphism of categories fibred in sets over `C` induces a morphism between the presheaves of
objects in its fibers. -/
private noncomputable def fibredInSetsOverToPresheafMap
    {X Y : FibredInSetsOver C} (F : X ⟶ Y) :
    X.p.fiberObjectPresheaf ⟶ Y.p.fiberObjectPresheaf where
  app U := fibredInSetsOverToPresheafApp F U
  naturality := fun {_ _} f ↦ by
    ext x
    exact congrFun (fibredInSetsOverToPresheafApp_naturality F f) x

-- Proof sketch: the identity morphism of `X` induces the identity functor on each fiber, hence
-- also the identity natural transformation on the presheaf of fiber objects.
private theorem fibredInSetsOverToPresheafMap_id
    (X : FibredInSetsOver C) :
    fibredInSetsOverToPresheafMap (𝟙 X) =
      𝟙 X.p.fiberObjectPresheaf := sorry

-- Proof sketch: the presheaf map attached to a composite is computed fiberwise from the composite
-- of the induced fiber functors, so functoriality reduces to functoriality of those fiberwise
-- maps on fiber objects.
private theorem fibredInSetsOverToPresheafMap_comp
    {X Y Z : FibredInSetsOver C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    fibredInSetsOverToPresheafMap (F ≫ G) =
      fibredInSetsOverToPresheafMap F ≫ fibredInSetsOverToPresheafMap G := sorry

/-- The inverse functor in Lemma 4.38.6 sends a category fibred in sets over `C` to the presheaf
of objects in its fibers, obtained from the owner construction
`X.p.fiberObjectPresheaf`. -/
noncomputable def fibredInSetsOverToPresheaf :
    FibredInSetsOver C ⥤ Presheaf.{max u v} C where
  obj X := X.p.fiberObjectPresheaf
  map {_} {_} F := fibredInSetsOverToPresheafMap F
  map_id X := fibredInSetsOverToPresheafMap_id X
  map_comp F G := fibredInSetsOverToPresheafMap_comp F G

-- Proof sketch: for each object `a` of the source fibred category, both components of any two
-- vertical natural transformations `G ⟶ H` lie in the discrete fiber of `Y` over `X.1.p.obj a`.
-- Hence there is at most one possible component at `a`, and componentwise uniqueness gives
-- equality of the natural transformations.
/-- Any two `2`-morphisms between `1`-morphisms of categories fibred in sets over `C` are equal;
hence the ambient `2`-category is actually an ordinary category. -/
theorem fibredInSetsOverTwoHom_subsingleton
    {X Y : FibredInSetsOver C} (G H : X ⟶ Y) :
    Subsingleton (G ⟶ H) := sorry

/-- Lemma 4.38.6: the category-of-elements construction sends a presheaf of sets on `C` to a
category fibred in sets over `C`, and this functor is an equivalence of categories. Its inverse
recovers from `p : S ⥤ C` the presheaf `U ↦ Ob (p.Fiber U)`. -/
theorem presheafToFibredInSetsOver_isEquivalence :
    Functor.IsEquivalence
      (presheafToFibredInSetsOver :
        Presheaf.{max u v} C ⥤ FibredInSetsOver C) := by
  refine Functor.IsEquivalence.mk' fibredInSetsOverToPresheaf ?_ ?_
  · sorry
  · sorry

end CategoryTheory
