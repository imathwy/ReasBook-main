import Mathlib
import StacksProject_2024.Chap04.Definition_4_29_2
import StacksProject_2024.Chap04.Definition_4_32_1
import StacksProject_2024.Chap04.Definition_4_33_6
import StacksProject_2024.Chap04.Lemma_4_33_7
import StacksProject_2024.Chap04.Lemma_4_33_8

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ vS u₁ u₂ u₃ w

namespace CategoryTheory

open Bicategory
open BasedFunctor
open Functor
open Fiber
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/- Domain-style sampling for Lemma 4.36.4:
- primary domain: fibred categories over a fixed base and equivalences in `Cat/C` to split
  fibred categories.
- sampled owner declarations:
  `FibredCategoryOver`,
  `Bicategory.Equivalence`,
  `Functor.IsSplitFibredCategory`.
- best owner abstraction: a split model should be exposed as an object `Y : FibredCategoryOver C`;
  the additional source-facing datum is then only the split predicate
  `Y.p.IsSplitFibredCategory`, while the comparison to `p` should use the ambient owner
  equivalence `FibredCategoryOver.ofFunctor p ≌ Y`.
- primitive data: the fibred functor `p : S ⥤ C`.
- derived API: the chosen pullback system `canonicalPullbackChoice p`, the strictification object,
  and the equivalence from `p` to that strictification.

Source/core/bridge triage:
- `source-facing`: the existence of a split fibred category over `C` equivalent over the base to
  `p`.
- `core/canonical`: `FibredCategoryOver C`, `Bicategory.Equivalence`, and
  `Functor.IsSplitFibredCategory`.
- `bridge/view`: the explicit strictification built from a chosen pullback system. -/

namespace BasedFunctor

/-- Helper for Lemma 4.36.4: a based functor over `C` preserves strongly cartesian morphisms if
it sends every strongly cartesian arrow in the source to a strongly cartesian arrow in the target.
This local owner surface is copied here so the item file does not depend on the broken module
`Definition_4_33_9`. -/
def PreservesStronglyCartesian
    {X Y : CategoryOver C} (G : X ⥤ᵇ Y) : Prop :=
  ∀ ⦃a b : X.obj⦄ (φ : a ⟶ b),
    X.p.IsStronglyCartesian (X.p.map φ) φ →
      Y.p.IsStronglyCartesian (Y.p.map (G.map φ)) (G.map φ)

end BasedFunctor

namespace Functor

open Pseudofunctor

variable {T : Type u₃} [Category.{v₃} T]

/-- Helper for Lemma 4.36.4: a functor `p : S ⥤ C` is split if it is isomorphic over `C` to the
co-Grothendieck construction of a contravariant `Cat`-valued functor. This local copy matches the
statement surface from Definition 4.36.2, but avoids importing upstream modules that currently do
not compile. -/
class IsSplitFibredCategory (p : T ⥤ C) : Prop where
  existsCoGrothendieckModel :
    ∃ (F : Cᵒᵖ ⥤ Cat.{v₃, u₃})
      (e : BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))
      (eInv : BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')) ⥤ᵇ
        BasedCategory.ofFunctor p),
      e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
        eInv ⋙ e = 𝟙 (BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))

end Functor

/-- Helper for Lemma 4.36.4: identity functors over the base preserve strongly cartesian arrows. -/
theorem fibredCategoryOver_id_preserves_strongly_cartesian
    (X : CategoryOver C) :
    BasedFunctor.PreservesStronglyCartesian (𝟙 X) := by
  -- The identity functor does not change the lifting problem, so strong cartesianness is
  -- preserved tautologically.
  intro a b φ hφ
  simpa using hφ

/-- Helper for Lemma 4.36.4: composites of strongly-cartesian-preserving functors again preserve
strongly cartesian arrows. -/
theorem fibredCategoryOver_comp_preserves_strongly_cartesian
    {X Y Z : CategoryOver C}
    {F : X ⥤ᵇ Y} {G : Y ⥤ᵇ Z}
    (hF : BasedFunctor.PreservesStronglyCartesian F)
    (hG : BasedFunctor.PreservesStronglyCartesian G) :
    BasedFunctor.PreservesStronglyCartesian (F ⋙ G) := by
  -- Apply the source preservation first, then the target preservation.
  intro a b φ hφ
  exact hG (F.map φ) (hF φ hφ)

/-- Helper for Lemma 4.36.4: fibred categories over `C` form the sub-`2`-category of `Cat/C`
cut out by fibred objects and strongly-cartesian-preserving `1`-morphisms. This is the exact
owner layer used by the target statement. -/
abbrev fibredCategoryOverSubTwoCategory (C : Type u₁) [Category.{v₁} C] :
    SubTwoCategory (CategoryOver C) where
  obj := fun X ↦ X.p.IsFibered
  hom _ _ := {
    obj := BasedFunctor.PreservesStronglyCartesian
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem X := fibredCategoryOver_id_preserves_strongly_cartesian X.obj
  comp_mem hF hG := fibredCategoryOver_comp_preserves_strongly_cartesian hF hG
  whiskerLeft_mem _ _ _ _ := by
    trivial
  whiskerRight_mem _ _ _ _ := by
    trivial

/-- Helper for Lemma 4.36.4: `FibredCategoryOver C` is the owner type of fibred categories over
`C`. This local copy matches the chapter owner used downstream, but avoids the broken import of
`Definition_4_33_9`. -/
abbrev FibredCategoryOver (C : Type u₁) [Category.{v₁} C] :=
  (fibredCategoryOverSubTwoCategory C).Obj

instance : Bicategory (FibredCategoryOver C) :=
  SubTwoCategory.bicategoryObj (fibredCategoryOverSubTwoCategory C)

instance : Bicategory.Strict (FibredCategoryOver C) :=
  SubTwoCategory.strictObj (fibredCategoryOverSubTwoCategory C)

instance fibredCategoryOverCategory : Category (FibredCategoryOver C) :=
  StrictBicategory.category (FibredCategoryOver C)

namespace FibredCategoryOver

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredCategoryOver C) :
    CategoryOver C :=
  X.obj

/-- The total category of a fibred category over `C`. -/
abbrev totalCat (X : FibredCategoryOver C) :=
  X.toCategoryOver.obj

/-- The projection functor to the base category. -/
abbrev p (X : FibredCategoryOver C) :=
  X.toCategoryOver.p

/-- Forget a fibred category over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredCategoryOver C) :
    BasedCategory.{max v₁ v₂, max u₁ u₂} C :=
  X.toCategoryOver

instance : CoeOut (FibredCategoryOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

instance : CoeOut (FibredCategoryOver C) (BasedCategory.{max v₁ v₂, max u₁ u₂} C) where
  coe X := X.toBasedCategory

instance isFibred (X : FibredCategoryOver C) : X.p.IsFibered := by
  -- The owner object property is exactly fibredness of the underlying projection.
  simpa [FibredCategoryOver.p, fibredCategoryOverSubTwoCategory] using X.property

/-- Build a fibred category over `C` from a fibred functor to `C`. -/
abbrev ofFunctor {T : Type w} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered] :
    FibredCategoryOver C :=
  ⟨BasedCategory.ofFunctor p, by
    simpa [fibredCategoryOverSubTwoCategory, BasedCategory.ofFunctor] using
      (inferInstance : p.IsFibered)⟩

end FibredCategoryOver

namespace BasedFunctor

variable {X Y : FibredCategoryOver C}

/-- Helper for Lemma 4.36.4: the strong-cartesian transport theorem from Lemma 4.33.8 applies
directly to based categories that already live in the same ambient universe. This bridge lets the
local owner-level copy specialize the imported result without redoing the transport proof. -/
theorem based_preserves_strongly_cartesian_of_equivalence_over_base
    {X' Y' : BasedCategory.{max v₁ v₂, max u₁ u₂} C}
    {F : X' ⥤ᵇ Y'} (hF : F.IsEquivalenceOverBase) :
    CategoryTheory.BasedFunctor.PreservesStronglyCartesian F := by
  -- This is exactly the imported strong-cartesian transport theorem, restated at the based
  -- category level used by the local owner wrapper.
  intro a b φ hφ
  exact CategoryTheory.BasedFunctor.isStronglyCartesian_map_of_isEquivalenceOverBase F hF φ hφ

/-- Helper for Lemma 4.36.4: the imported pull-push comparison from Lemma 4.33.8 applies
directly to same-universe based categories. This isolates the exact bridge that the owner-local
wrapper still has to transport through `FibredCategoryOver.toBasedCategory`. -/
theorem based_pushforward_pullback_eq
    {X' Y' : BasedCategory.{max v₁ v₂, max u₁ u₂} C}
    {F : X' ⥤ᵇ Y'} (e : EquivalenceOverBase F)
    {x : X'.obj} {z : Y'.obj} (θ : z ⟶ F.obj x) :
    e.toEquivalence.counit.inv.app z ≫ F.map (e.inverse.map θ ≫ e.unitIso.inv.app x) = θ := by
  -- This is exactly the imported based-category pull-push comparison in the same-universe case.
  exact CategoryTheory.BasedFunctor.pushforward_pullback_eq F e θ

/-- Helper for Lemma 4.36.4: after forgetting the owner-local fibred-category data, the
adjointified left triangle evaluates to the ordinary comparison between the left zigzag and the
unitors at each object. -/
theorem forgotten_left_triangle_component_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    (leftZigzag e.toEquivalence.unit.hom e.toEquivalence.counit.hom).app x =
      ((BasedNatTrans.forgetful X.toBasedCategory Y.toBasedCategory).mapIso
        (λ_ e.toEquivalence.hom ≪≫ (ρ_ e.toEquivalence.hom).symm)).hom.app x := by
  -- Forget the based left-triangle isomorphism to the ordinary functor category and evaluate it
  -- at `x`.
  let Φ := congrArg
    (Functor.mapIso (BasedNatTrans.forgetful X.toBasedCategory Y.toBasedCategory))
    e.toEquivalence.left_triangle
  exact congrArg (fun η ↦ η.hom.app x) Φ

/-- Helper for Lemma 4.36.4: the forgotten left-zigzag component is the ordinary composite of
the unit component followed by the counit component. -/
theorem forgotten_left_zigzag_hom_app_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
        e.toEquivalence.counit.hom).app x =
      F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) := by
  -- Expand the bicategorical coherence into the strict associator and the whiskered identity.
  change F.map (e.unitIso.hom.app x) ≫
      ((CategoryTheory.BicategoricalCoherence.iso.hom :
        ((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ e.toEquivalence.hom) ⟶
          e.toEquivalence.hom ≫ (e.toEquivalence.inv ≫ e.toEquivalence.hom)).app x) ≫
      e.toEquivalence.counit.hom.app (F.obj x) = _
  dsimp [CategoryTheory.BicategoricalCoherence.iso, CategoryTheory.BicategoricalCoherence.assoc]
  change F.map (e.unitIso.hom.app x) ≫
      ((α_ e.toEquivalence.hom e.toEquivalence.inv e.toEquivalence.hom).hom.app x ≫
        (CategoryTheory.BasedCategory.whiskerRight
          (CategoryTheory.BasedNatTrans.id F) (e.inverse ⋙ F)).app x) ≫
      e.toEquivalence.counit.hom.app (F.obj x) = _
  have hassoc :
      (α_ e.toEquivalence.hom e.toEquivalence.inv e.toEquivalence.hom).hom.app x =
        𝟙 (((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ e.toEquivalence.hom).obj x) := by
    -- In the strict bicategory `BasedCategory`, the associator contributes only the identity.
    simp [CategoryTheory.Bicategory.Strict.associator_eqToIso]
    rfl
  rw [hassoc]
  -- The remaining whiskered identity component is definitionally trivial.
  simp [CategoryTheory.BasedCategory.whiskerRight, CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.36.4: the forgotten right-hand comparison in the left triangle is the
identity map on each object. -/
theorem forgotten_left_triangle_rhs_hom_app_eq_id_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x = 𝟙 (F.obj x) := by
  -- Both unitors are strict identities in `BasedCategory`, so the component stays the identity.
  change (CategoryTheory.BasedNatTrans.comp (CategoryTheory.BasedNatTrans.id F)
      (CategoryTheory.BasedNatTrans.id F)).app x = _
  rw [CategoryTheory.BasedNatTrans.comp]
  simp [CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.36.4: the owner-local adjointified left triangle reduces to the ordinary
unit-counit cancellation formula on each target object. -/
theorem adjointified_triangle_component_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) = 𝟙 (F.obj x) := by
  -- Route correction: evaluate the bicategorical left triangle at `x` before simplifying its two
  -- sides into the ordinary unit-counit composite and the identity component.
  have htriangle :=
    congrArg (fun η ↦ η.app x)
      (CategoryTheory.Bicategory.Equivalence.left_triangle_hom e.toEquivalence)
  have htriangle' :
      (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
          e.toEquivalence.counit.hom).app x =
        ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x := by
    simpa using htriangle
  exact (forgotten_left_zigzag_hom_app_same_owner (e := e) x).symm.trans <|
    htriangle'.trans (forgotten_left_triangle_rhs_hom_app_eq_id_same_owner (e := e) x)

/-- Helper for Lemma 4.36.4: forgetting an owner-local equivalence over the base produces the
corresponding ordinary equivalence of the underlying total categories. -/
noncomputable def forgotten_equivalence_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) :
    X.toBasedCategory.obj ≌ Y.toBasedCategory.obj :=
  CategoryTheory.Equivalence.mk
    F.toFunctor
    e.inverse.toFunctor
    ((BasedNatTrans.forgetful X.toBasedCategory X.toBasedCategory).mapIso e.unitIso)
    ((BasedNatTrans.forgetful Y.toBasedCategory Y.toBasedCategory).mapIso e.counitIso)

/-- Helper for Lemma 4.36.4: after forgetting the owner-level base data, the counit of the
comparison equivalence cancels the image of the inverse unit component on each object. This is
the ordinary triangle identity that the owner-local strong-cartesian transport proof must reuse. -/
theorem forgotten_equivalence_same_owner_counitIso_functor_comp
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).counitIso.inv.app (F.obj x) ≫
        F.map ((forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).unitIso.inv.app x) =
      𝟙 (F.obj x) := by
  exact
    (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).counitIso_functor_comp x

/-- Helper for Lemma 4.36.4: after forgetting to the ordinary total categories, the counit
component of the forgotten equivalence is literally the counit component from the original
equivalence-over-base datum. -/
theorem forgotten_equivalence_same_owner_counit_inv_app_eq
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : Y.toBasedCategory.obj) :
    (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).counitIso.inv.app x =
      e.counitIso.inv.app x := by
  -- Forgetting only removes the base-lift witness, so the underlying counit component is
  -- definitionally unchanged.
  rfl

/-- Helper for Lemma 4.36.4: after forgetting to the ordinary total categories, the inverse unit
component of `forgotten_equivalence_same_owner e` is literally the inverse component of the
adjointified ordinary unit used by `CategoryTheory.Equivalence.mk`. This exposes the exact shape
that must be compared with `e.unitIso.inv.app` in any repaired transport proof. -/
theorem forgotten_equivalence_same_owner_unit_inv_app_eq_adjointified
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).unitIso.inv.app x =
      (CategoryTheory.Equivalence.adjointifyη
        ((BasedNatTrans.forgetful X.toBasedCategory X.toBasedCategory).mapIso e.unitIso)
        ((BasedNatTrans.forgetful Y.toBasedCategory Y.toBasedCategory).mapIso e.counitIso)).inv.app x := by
  -- `forgotten_equivalence_same_owner` is defined with `CategoryTheory.Equivalence.mk`, whose
  -- unit is by definition `Equivalence.adjointifyη` applied to the forgotten unit and counit.
  rfl

/-- Helper for Lemma 4.36.4: after forgetting to the ordinary total categories, the inverse unit
component of the forgotten equivalence is literally the inverse component of the adjointified
ordinary unit used by `CategoryTheory.Equivalence.mk`. -/
theorem forgotten_equivalence_same_owner_unit_inv_app_eq
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).unitIso.inv.app x =
      (CategoryTheory.Equivalence.adjointifyη
        ((BasedNatTrans.forgetful X.toBasedCategory X.toBasedCategory).mapIso e.unitIso)
        ((BasedNatTrans.forgetful Y.toBasedCategory Y.toBasedCategory).mapIso e.counitIso)).inv.app x := by
  -- `forgotten_equivalence_same_owner` is defined with `CategoryTheory.Equivalence.mk`, so its
  -- unit is definitionally the adjointified unit of the forgotten data.
  exact forgotten_equivalence_same_owner_unit_inv_app_eq_adjointified (X := X) (Y := Y) (e := e) x

/-- Helper for Lemma 4.36.4: after forgetting to the ordinary total categories, the inverse and
hom of the unit comparison still cancel on each source object. This is the ordinary unit-side
triangle identity that survives forgetting the owner-level base data. -/
theorem forgotten_equivalence_same_owner_unit_inv_hom_id_app
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).unitIso.inv.app x ≫
        (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).unitIso.hom.app x =
      𝟙
        ((forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).inverse.obj
          ((forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).functor.obj x)) := by
  -- The forgotten equivalence is an ordinary equivalence, so its unit still satisfies the
  -- standard inverse-then-hom cancellation formula objectwise.
  exact
    (forgotten_equivalence_same_owner (X := X) (Y := Y) (e := e)).unitIso.inv_hom_id_app x

/-- Helper for Lemma 4.36.4: appending the canonical base-change isomorphism from `F.w_obj`
does not change whether a target morphism is a lift. This is the same-owner version needed by the
local `FibredCategoryOver` copy in this file. -/
theorem isHomLift_over_target_eq_iff_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory}
    {z : Y.toBasedCategory.obj} {x : X.toBasedCategory.obj}
    (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The extra `eqToHom` only rewrites the codomain to the source-side base coordinates.
  simpa using IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)

/-- Helper for Lemma 4.36.4: pulling a lifting problem back across the inverse in an explicit
equivalence over the base preserves the same base morphism in the local owner copy. -/
theorem inverse_transport_lift_over_base_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    {x y : X.toBasedCategory.obj} (φ : x ⟶ y)
    {z : Y.toBasedCategory.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ)
      (e.inverse.map ψ ≫ e.unitIso.inv.app y) := by
  -- Rewrite the target lifting problem into the source base coordinates using the over-base
  -- equation attached to `F`.
  have hψY : Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ := by
    refine IsHomLift.of_fac Y.p _ ψ rfl (F.w_obj y) ?_
    have hbase :
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
      calc
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ
            = g ≫ Y.p.map (F.map φ) ≫ eqToHom (F.w_obj y) := by
                simpa [Category.assoc] using
                  (congrArg (fun k ↦ g ≫ k ≫ eqToHom (F.w_obj y))
                    (Functor.congr_hom F.w φ)).symm
        _ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ eqToHom (F.w_obj y))
                  (IsHomLift.eq_of_isHomLift Y.p (g ≫ Y.p.map (F.map φ)) ψ)
    simpa [Category.assoc] using hbase
  -- Pull the given lifted arrow back across the quasi-inverse.
  have hψX :
      X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ).2 hψY
  -- The unit component is vertical, so composing with it keeps the same base map.
  have hη : X.p.IsHomLift (𝟙 (X.p.obj y)) (e.unitIso.inv.app y) := by
    simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj y = X.p.obj y)
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (e.unitIso.inv.app y) hη

/-- Helper for Lemma 4.36.4: pushing a lifted morphism forward across the chosen equivalence over
the base preserves the same base morphism in the local owner copy. -/
noncomputable def owner_local_adjointified_counit
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (e : BasedFunctor.EquivalenceOverBase (X := X.toBasedCategory) (Y := Y.toBasedCategory) F) :
    e.inverse ⋙ F ≅ 𝟭 Y.toBasedCategory :=
  Bicategory.adjointifyCounit
    (a := X.toBasedCategory) (b := Y.toBasedCategory) (f := F) (g := e.inverse)
    e.unitIso e.counitIso

/-- Helper for Lemma 4.36.4: pushing a lifted morphism forward across the chosen equivalence over
the base preserves the same base morphism in the local owner copy. -/
theorem forward_transport_lift_over_base_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    {x : X.toBasedCategory.obj} {z : Y.toBasedCategory.obj}
    (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : e.inverse.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
      Y.p.IsHomLift g
      ((owner_local_adjointified_counit
          (F := F)
          (e := (show BasedFunctor.EquivalenceOverBase
            (X := X.toBasedCategory) (Y := Y.toBasedCategory) F from e))).inv.app z ≫
        F.map ξ) := by
  let eps : e.inverse ⋙ F ≅ 𝟭 Y.toBasedCategory :=
    show e.inverse ⋙ F ≅ 𝟭 Y.toBasedCategory from
      owner_local_adjointified_counit
        (F := F) (e := e)
  -- Push the source lift forward along `F`, then precompose with the vertical adjointified
  -- counit inverse so the later push-pull identity can use the same comparison.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (eps.inv.app z) := by
    simpa [eps] using BasedNatTrans.isHomLift eps.inv
      (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (eps.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Lemma 4.36.4: a target-side factorization pulls back along the inverse together
with the unit inverse to the corresponding source-side factorization in the local owner copy. -/
theorem pullback_factorization_of_map_factorization_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    {x y : X.toBasedCategory.obj} (φ : x ⟶ y)
    {z : Y.toBasedCategory.obj} {τ' : z ⟶ F.obj x} {ψ' : z ⟶ F.obj y}
    (hτ' : τ' ≫ F.map φ = ψ') :
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ =
      e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
  -- Rewrite the pulled-back `F.map φ` term using naturality of the unit inverse.
  calc
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ
        = e.inverse.map τ' ≫ (e.unitIso.inv.app x ≫ φ) := by
            simp [Category.assoc]
    _ = e.inverse.map τ' ≫ (e.inverse.map (F.map φ) ≫ e.unitIso.inv.app y) := by
          simpa [Category.assoc] using
            (congrArg (fun k ↦ e.inverse.map τ' ≫ k) (e.unitIso.inv.naturality φ)).symm
    _ = e.inverse.map (τ' ≫ F.map φ) ≫ e.unitIso.inv.app y := by
          simp [Functor.map_comp, Category.assoc]
    _ = e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
          rw [hτ']

/-- Helper for Lemma 4.36.4: the inverse counit component cancels the inverse unit component on
each target object after forgetting to the underlying total categories. -/
theorem adjointified_triangle_inverse_component_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    (x : X.toBasedCategory.obj) :
    e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = 𝟙 (F.obj x) := by
  -- Package the based equivalence as an ordinary equivalence and use its standard inverse
  -- triangle identity instead of normalizing the copied bicategorical coherence again.
  let E : X.toBasedCategory.obj ≌ Y.toBasedCategory.obj :=
    CategoryTheory.Equivalence.mk'
      F.toFunctor e.inverse.toFunctor
      ((BasedNatTrans.forgetful X.toBasedCategory X.toBasedCategory).mapIso e.unitIso)
      ((BasedNatTrans.forgetful Y.toBasedCategory Y.toBasedCategory).mapIso e.toEquivalence.counit)
      (fun x ↦ by
        simpa using adjointified_triangle_component_same_owner (X := X) (Y := Y) (e := e) x)
  simpa [E] using E.counitIso_functor_comp x

/-- Helper for Lemma 4.36.4: pushing the pulled-back source lift back across the counit inverse
recovers the original target morphism in the local owner copy. -/
theorem pushforward_pullback_eq_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F)
    {x : X.toBasedCategory.obj} {z : Y.toBasedCategory.obj} (θ : z ⟶ F.obj x) :
    (owner_local_adjointified_counit
        (F := F)
        (e := (show BasedFunctor.EquivalenceOverBase
          (X := X.toBasedCategory) (Y := Y.toBasedCategory) F from e))).inv.app z ≫
        F.map (e.inverse.map θ ≫ e.unitIso.inv.app x) = θ := by
  let eps :=
    owner_local_adjointified_counit
      (X := X) (Y := Y) (F := F)
      (e := (show BasedFunctor.EquivalenceOverBase
        (X := X.toBasedCategory) (Y := Y.toBasedCategory) F from e))
  -- Move `θ` across the counit inverse, then collapse the remaining counit-unit tail.
  rw [Functor.map_comp]
  have hnat :
      eps.inv.app z ≫ F.map (e.inverse.map θ) ≫
          F.map (e.unitIso.inv.app x) =
        θ ≫ eps.inv.app (F.obj x) ≫
          F.map (e.unitIso.inv.app x) := by
    simpa [Functor.comp_map, Category.assoc] using
      (congrArg (fun k ↦ k ≫ F.map (e.unitIso.inv.app x))
        (eps.inv.naturality θ)).symm
  have htail :
      θ ≫ eps.inv.app (F.obj x) ≫
          F.map (e.unitIso.inv.app x) = θ := by
    have htail' :
        θ ≫ eps.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) =
          θ ≫ 𝟙 (F.obj x) := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ θ ≫ k)
          (adjointified_triangle_inverse_component_same_owner
            (X := X) (Y := Y) (e := e) x)
    simpa using htail'
  exact hnat.trans htail

/-- Helper for Lemma 4.36.4: swapping the original inverse, unit, and counit packages the
inverse functor as explicit equivalence-over-base data. This isolates the exact datum needed by
the remaining inverse strong-cartesian transport proof. -/
noncomputable def inverse_equivalence_over_base_data
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) :
    BasedFunctor.EquivalenceOverBase
      (X := Y.toBasedCategory) (Y := X.toBasedCategory) e.inverse :=
  { inverse := F
    unitIso := e.counitIso.symm
    counitIso := e.unitIso.symm }

/-- Helper for Lemma 4.36.4: the swapped inverse-equivalence datum really uses the original
functor as quasi-inverse and swaps the unit/counit isomorphisms. This packages the stabilized
frontier before the remaining adjointified-counit transport blocker. -/
theorem inverse_equivalence_over_base_data_spec
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) :
    (inverse_equivalence_over_base_data e).inverse = F ∧
      (inverse_equivalence_over_base_data e).unitIso = e.counitIso.symm ∧
      (inverse_equivalence_over_base_data e).counitIso = e.unitIso.symm := by
  -- All three fields are exactly the swapped pieces from the original equivalence data.
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Helper for Lemma 4.36.4: the swapped inverse-equivalence datum is concretely available as an
explicit witness, so later repairs can refer to it without unfolding the swapped fields again. -/
theorem inverse_equivalence_over_base_data_nonempty
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) :
    Nonempty
      (BasedFunctor.EquivalenceOverBase
        (X := Y.toBasedCategory) (Y := X.toBasedCategory) e.inverse) := by
  -- The swapped inverse package was already constructed explicitly above.
  exact ⟨inverse_equivalence_over_base_data e⟩

/-- Helper for Lemma 4.36.4: the swapped explicit inverse datum already packages `e.inverse` as
an equivalence over the base. This isolates the universe-stable part of the inverse packaging from
the remaining strong-cartesian transport blocker. -/
theorem inverse_equivalence_over_base_data_isEquivalenceOverBase
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) :
    e.inverse.IsEquivalenceOverBase := by
  -- The swapped quasi-inverse, unit, and counit from `inverse_equivalence_over_base_data e` are
  -- already exactly the data required for `IsEquivalenceOverBase`.
  exact ⟨⟨inverse_equivalence_over_base_data e⟩⟩

/-- Helper for Lemma 4.36.4: explicit equivalence-over-base data on the forward functor already
package the owner-level `IsEquivalenceOverBase` predicate without any further transport. -/
theorem equivalence_over_base_data_isEquivalenceOverBase_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) :
    F.IsEquivalenceOverBase := by
  -- This is the canonical owner-level wrapper around the explicit quasi-inverse, unit, and
  -- counit data carried by `e`.
  exact BasedFunctor.IsEquivalenceOverBase.mkPrime (F := F) e.inverse e.unitIso e.counitIso

/-- Helper for Lemma 4.36.4: the same-owner explicit equivalence-over-base data induce an
equivalence on every standard fiber. This is the fiberwise comparison package needed later for
the strict-side counit construction. -/
theorem fiber_functor_isEquivalence_of_equivalence_data_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) (U : C) :
    (F.fiberFunctor U).IsEquivalence := by
  -- Repackage the explicit same-owner data as the owner-level equivalence predicate and then
  -- invoke the imported fiberwise equivalence theorem.
  let hF : F.IsEquivalenceOverBase :=
    equivalence_over_base_data_isEquivalenceOverBase_same_owner
      (X := X) (Y := Y) (F := F) e
  exact CategoryTheory.BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U

/-- Helper for Lemma 4.36.4: the swapped explicit inverse datum also induces an equivalence on
every standard fiber. This packages the inverse-side fiber comparison that the strict-side counit
construction is expected to use later. -/
theorem inverse_fiber_functor_isEquivalence_of_equivalence_data_same_owner
    {F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory} (e : EquivalenceOverBase F) (U : C) :
    (e.inverse.fiberFunctor U).IsEquivalence := by
  -- Repackage the swapped explicit inverse datum directly as an owner-level equivalence over the
  -- base, avoiding the swapped-owner specialization that reintroduces the old universe issue.
  let hInv : e.inverse.IsEquivalenceOverBase :=
    inverse_equivalence_over_base_data_isEquivalenceOverBase
      (X := X) (Y := Y) (F := F) e
  exact CategoryTheory.BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
    e.inverse hInv U

end BasedFunctor

namespace FibredCategoryMor

variable {X Y : FibredCategoryOver C}

/-- Helper for Lemma 4.36.4: forget an owner-level morphism to its underlying based functor
over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  F.obj.obj

/-- Helper for Lemma 4.36.4: an owner-level morphism of fibred categories is an equivalence over
the base exactly when its underlying based functor is. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  BasedFunctor.IsEquivalenceOverBase (toBasedFunctor F)

/-- Helper for Lemma 4.36.4: package a based functor preserving strongly cartesian morphisms as
an owner-level morphism in the local fibred-category owner. -/
abbrev ofBasedFunctor (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hG : G.PreservesStronglyCartesian) : X ⟶ Y :=
  ⟨⟨G, by
      simpa [fibredCategoryOverSubTwoCategory] using hG⟩⟩

/-- Helper for Lemma 4.36.4: a based natural isomorphism between underlying comparison functors
induces the corresponding owner-level isomorphism. -/
noncomputable def ownerIsoOfBasedFunctorIso
    {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Helper for Lemma 4.36.4: explicit based equivalence data on an owner-level morphism produce
the corresponding bicategorical equivalence of local fibred-category owners. -/
noncomputable def ofEquivalenceOverBase
    (F : X ⟶ Y)
    (e : BasedFunctor.EquivalenceOverBase (toBasedFunctor F)) :
    Bicategory.Equivalence X Y :=
  let G : Y ⟶ X :=
    ofBasedFunctor e.inverse
      (based_preserves_strongly_cartesian_of_equivalence_over_base
        (X' := Y.toBasedCategory) (Y' := X.toBasedCategory)
        (F := e.inverse)
        (inverse_equivalence_over_base_data_isEquivalenceOverBase
          (X := X) (Y := Y)
          (F := toBasedFunctor F) e))
  let etaBased : toBasedFunctor (𝟙 X : X ⟶ X) ≅ toBasedFunctor (F ≫ G) := by
    -- Forgetting the owner-level data leaves the original based unit isomorphism unchanged.
    exact e.unitIso
  let eta : (𝟙 X : X ⟶ X) ≅ F ≫ G :=
    ownerIsoOfBasedFunctorIso etaBased
  let epsBased : toBasedFunctor (G ≫ F) ≅ toBasedFunctor (𝟙 Y : Y ⟶ Y) := by
    -- The counit behaves identically after forgetting the owner-level object property.
    exact e.counitIso
  let eps : G ≫ F ≅ (𝟙 Y : Y ⟶ Y) :=
    ownerIsoOfBasedFunctorIso epsBased
  Bicategory.Equivalence.mkOfAdjointifyCounit eta eps

end FibredCategoryMor

end CategoryTheory
