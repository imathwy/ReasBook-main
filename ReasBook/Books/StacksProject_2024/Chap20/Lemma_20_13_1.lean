import Mathlib
import StacksProject_2024.Chap13.Lemma_13_14_16
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap20.«20_3_0_4»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ u u₁ u₂ u₃

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The underlying morphism of presheafed spaces attached to a morphism of ringed spaces. -/
abbrev toPresheafedSpaceHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    X.toPresheafedSpace ⟶ Y.toPresheafedSpace :=
  f.hom

/-- The underlying continuous map of a morphism of ringed spaces. -/
abbrev baseMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  (toPresheafedSpaceHom f).base

/-- The morphism of structure sheaves attached to a morphism of ringed spaces. -/
abbrev structureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :=
  (toPresheafedSpaceHom f).c

/-- The open subset `f^{-1}(V)` of `X` attached to an open subset `V ⊆ Y`. -/
abbrev preimageOpen {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    Opens X.carrier :=
  Opens.comap (baseMap f).hom V

/-- The ring of sections `Γ(U, \mathcal O_X)` on an open subset `U ⊆ X`. -/
abbrev sectionsRingOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op U)

/-- Modules over the section ring of an open subset carry the standard derived category. -/
instance sectionsRingOnOpen_hasDerivedCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  HasDerivedCategory.standard _

/-- The sections functor `\Gamma(U, -)` on `\mathcal O_X`-modules. -/
abbrev moduleSectionsFunctorAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    SheafOfModules ((RingedSpace.ringCatSheaf X)) ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation ((RingedSpace.ringCatSheaf X)) (op U)

/-- The induced functor `K^+(X) ⥤ D^+(\Gamma(U, \mathcal O_X)\text{-Mod})` on bounded-below
homotopy and derived categories of section modules. -/
abbrev moduleSectionsHomotopyToDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ObjectProperty.FullSubcategory
        (CategoryTheory.boundedBelowHomotopyProperty
          (SheafOfModules ((RingedSpace.ringCatSheaf X)))) ⥤
      boundedBelowDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
    (moduleSectionsFunctorAtOpen X U)

/-- The sections functor on an open subset is additive. -/
instance moduleSectionsFunctorAtOpen_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsFunctorAtOpen X U).Additive := sorry

/-- Direct image on `\mathcal O`-modules is additive. -/
instance ringedSpaceModulePushforward_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Hom.pushforward f).Additive := sorry

/-- The map on section rings over `V` induced by a morphism of ringed spaces. -/
abbrev sectionsMapOnOpen {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    sectionsRingOnOpen Y V ⟶ sectionsRingOnOpen X (preimageOpen f V) :=
  (structureSheafHom f).app (op V)

/-- Restriction of scalars along the map on sections `Γ(V, \mathcal O_Y) → Γ(f^{-1}(V),
\mathcal O_X)`. -/
abbrev moduleSectionsRestrictionFunctor {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤
      ModuleCat (sectionsRingOnOpen Y V) :=
  ModuleCat.restrictScalars (sectionsMapOnOpen f V).hom

/-- Restriction of scalars on section modules is additive. -/
instance moduleSectionsRestrictionFunctor_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (moduleSectionsRestrictionFunctor f V).Additive := by
  infer_instance

-- Proof sketch: both composites evaluate an `\mathcal O_X`-module on `f^{-1}(V)` and then
-- regard the resulting module as a `\Gamma(V, \mathcal O_Y)`-module via the map `f^\sharp(V)`.
/-- The underived identity `restriction ∘ \Gamma(f^{-1}(V), -) = \Gamma(V, -) ∘ f_*`. -/
theorem moduleSectionsFunctorAtPreimage_comp_restriction_eq_pushforward_comp_sections
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    moduleSectionsFunctorAtOpen X (preimageOpen f V) ⋙ moduleSectionsRestrictionFunctor f V =
      RingedSpace.Hom.pushforward f ⋙ moduleSectionsFunctorAtOpen Y V := sorry

/-- The composite `\Gamma(V, -) ∘ f_*` admits a bounded-below right derived functor. -/
instance modulePushforward_sectionsAtOpen_composite_hasRightDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
          (moduleSectionsFunctorAtOpen Y V))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf X)))) := sorry

/-- The composite `f_*` followed by the localization functor on `D^+(Y)` admits the required
bounded-below right derived functor. -/
instance modulePushforward_identity_composite_hasRightDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
          (𝟭 (SheafOfModules ((RingedSpace.ringCatSheaf Y)))))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf X)))) := sorry

local instance modulePushforward_Q_composite_hasRightDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
        (CategoryTheory.boundedBelowHomotopyQuasiIso
          (SheafOfModules ((RingedSpace.ringCatSheaf Y)))).Q)
      (CategoryTheory.boundedBelowHomotopyQuasiIso
        (SheafOfModules ((RingedSpace.ringCatSheaf X)))) := by
  sorry

/-- The functor `\Gamma(V, -)` admits a bounded-below right derived functor. -/
instance moduleSectionsFunctorAtOpen_hasRightDerivedFunctor
    (Y : RingedSpace.{u}) (V : Opens Y.carrier) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
        (moduleSectionsFunctorAtOpen Y V))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf Y)))) := sorry

-- Proof sketch: use the previous underived identity to rewrite the source composite as
-- `restriction ∘ Γ(f^{-1}(V), -)`. Since restriction of scalars is exact, the Grothendieck
-- comparison criterion applies, and Lemma `20.11.10` supplies the required acyclicity of
-- `Γ(V, -)` on pushforwards of injective `\mathcal O_X`-modules.
/-- Lemma 20.13.1: for an open subset `V ⊆ Y` and `U = f^{-1}(V)`, the canonical bounded-below
Grothendieck comparison morphism for the composite `\Gamma(V, -) \circ f_*`, equivalently for
`restriction \circ \Gamma(U, -)`, is an isomorphism. This is the commutativity of the diagram
with `R\Gamma(U, -)`, `Rf_*`, `R\Gamma(V, -)`, and restriction on `D^+`. -/
theorem modulePushforward_sectionsAtOpen_boundedBelowRightDerivedCompComparison_isIso
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIso
      (CategoryTheory.Functor.rightDerivedCompComparison
        (CategoryTheory.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))
        (CategoryTheory.boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))
        (CategoryTheory.mapBoundedBelowHomotopyCategory
          (RingedSpace.Hom.pushforward f))
        (moduleSectionsHomotopyToDerived Y V)) := sorry

end AlgebraicGeometry.RingedSpace
