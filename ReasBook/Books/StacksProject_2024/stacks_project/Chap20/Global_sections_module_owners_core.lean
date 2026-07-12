import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap18.Lemma_18_14_2
import StacksProject_2024.Chap19.AdditiveFunctorTotalRightDerived

open CategoryTheory
open CategoryTheory.DerivedCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The category of `\mathcal O_X`-modules on a ringed space has filtered colimits in the
Grothendieck-owner universe used by the derived-functor API below. -/
instance sheafModules_hasFilteredColimitsOfSize (X : RingedSpace.{u}) :
    Limits.HasFilteredColimitsOfSize.{u, u} (RingedSpace.Modules X) := by
  let _ : Limits.HasColimitsOfSize.{u, u} (RingedSpace.Modules X) := by
    infer_instance
  exact Limits.hasFilteredColimitsOfSize_of_hasColimitsOfSize

/-- Helper for 20.14.1.1: sheafification sends a separator in presheaf modules on a ringed space
to a separator in sheaf modules. -/
lemma sheafification_obj_isSeparator (X : RingedSpace.{u})
    {G : PresheafOfModules (RingedSpace.ringCatSheaf X).obj} (hG : IsSeparator G) :
    IsSeparator ((PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj G) := by
  let R := RingedSpace.ringCatSheaf X
  let F := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  rw [CategoryTheory.isSeparator_def] at hG ⊢
  intro A B f g hfg
  have hmap : F.map f = F.map g := by
    apply hG
    intro h
    let k : (PresheafOfModules.sheafification (𝟙 R.obj)).obj G ⟶ A :=
      (adj.homEquiv G A).symm h
    have hkfg : k ≫ f = k ≫ g := hfg k
    have hk : (adj.homEquiv G A) k = h := by
      simpa [k] using (Equiv.apply_symm_apply (adj.homEquiv G A) h)
    have hkf : (adj.homEquiv G B) (k ≫ f) = h ≫ F.map f := by
      calc
        (adj.homEquiv G B) (k ≫ f) = (adj.homEquiv G A) k ≫ F.map f := by
          simpa [F] using (adj.homEquiv_naturality_right k f)
        _ = h ≫ F.map f := by
          simpa using congrArg (fun t ↦ t ≫ F.map f) hk
    have hkg : (adj.homEquiv G B) (k ≫ g) = h ≫ F.map g := by
      calc
        (adj.homEquiv G B) (k ≫ g) = (adj.homEquiv G A) k ≫ F.map g := by
          simpa [F] using (adj.homEquiv_naturality_right k g)
        _ = h ≫ F.map g := by
          simpa using congrArg (fun t ↦ t ≫ F.map g) hk
    calc
      h ≫ F.map f = (adj.homEquiv G B) (k ≫ f) := hkf.symm
      _ = (adj.homEquiv G B) (k ≫ g) := by
        simpa using congrArg (fun t ↦ (adj.homEquiv G B) t) hkfg
      _ = h ≫ F.map g := hkg
  exact CategoryTheory.Functor.map_injective F hmap

/-- Helper for 20.14.1.1: sheaves of modules on a ringed space admit a separator obtained by
sheafifying the coproduct of the free-Yoneda presheaf-module family. -/
lemma sheaf_modules_has_separator (X : RingedSpace.{u}) :
    HasSeparator (RingedSpace.Modules X) := by
  let R := RingedSpace.ringCatSheaf X
  let F : Opens X.carrier → PresheafOfModules R.obj :=
    fun U ↦ (yoneda ⋙ PresheafOfModules.free R.obj).obj U
  have hF : (CategoryTheory.ObjectProperty.ofObj F).IsSeparating := by
    simpa [F, PresheafOfModules.freeYoneda] using
      (PresheafOfModules.freeYoneda.isSeparating (R := R.obj))
  have hSepPresheaf : IsSeparator (∐ F) := by
    exact CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct (f := F) hF
  refine ⟨⟨(PresheafOfModules.sheafification (𝟙 R.obj)).obj (∐ F), ?_⟩⟩
  exact sheafification_obj_isSeparator X hSepPresheaf

/-- Helper for 20.14.1.1: morphism sets in `\mathcal O_X`-modules are small in the universe
required by the Grothendieck-abelian owner. -/
instance sheafModules_locallySmall (X : RingedSpace.{u}) :
    LocallySmall.{u} (RingedSpace.Modules X) := by
  infer_instance

/-- The category of `\mathcal O_X`-modules on a ringed space has a separator. -/
instance sheafModules_hasSeparator (X : RingedSpace.{u}) :
    HasSeparator (RingedSpace.Modules X) := by
  exact sheaf_modules_has_separator X

private noncomputable instance sheafModules_ab5 (X : RingedSpace.{u}) :
    AB5 (RingedSpace.Modules X) :=
  (mod_forgetful_has_limits_colimits_and_ab5 (𝒪 := RingedSpace.ringCatSheaf X)).2.2

/-- The category of `\mathcal O_X`-modules on a ringed space is Grothendieck abelian. -/
instance sheafModules_isGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian.{u} (RingedSpace.Modules X) := by
  refine
    { locallySmall := sheafModules_locallySmall X
      hasFilteredColimitsOfSize := sheafModules_hasFilteredColimitsOfSize X
      ab5OfSize := by
        let _ : AB5 (RingedSpace.Modules X) := sheafModules_ab5 X
        exact AB5OfSize_shrink (C := RingedSpace.Modules X)
      hasSeparator := sheafModules_hasSeparator X }

/-- The standard derived-category structure on `𝒪_X`-modules. -/
instance modules_hasDerivedCategory (X : RingedSpace.{u}) :
    HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

/-- The unbounded derived category `D(𝒪_X)` of module sheaves on a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The ring of global sections `Γ(X, \mathcal O_X)` of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{u}) : CommRingCat :=
  SheafedSpace.Γ.obj (op X)

/-- The standard derived-category structure on `Γ(X, 𝒪_X)`-modules. -/
instance globalSectionsModuleCat_hasDerivedCategory (X : RingedSpace.{u}) :
    HasDerivedCategory (ModuleCat (globalSectionsRing X)) :=
  HasDerivedCategory.standard (ModuleCat (globalSectionsRing X))

/-- The global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSpace.{u}) :
    RingedSpace.Modules X ⥤ ModuleCat (globalSectionsRing X) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op (⊤ : Opens X.carrier))

/-- The global-sections functor on `\mathcal O_X`-modules is additive. -/
instance moduleGlobalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).Additive := by
  refine ⟨fun {_ _} f g ↦ ?_⟩
  rfl

/-- The total right derived global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleDerivedGlobalSections (X : RingedSpace.{u}) :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  let _ : IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
    sheafModules_isGrothendieckAbelian X
  let F : RingedSpace.Modules X ⥤ ModuleCat (globalSectionsRing X) :=
    moduleGlobalSectionsFunctor X
  letI : F.Additive := moduleGlobalSectionsFunctor_additive X
  letI :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The cochain-level pushforward functor followed by localization to the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(f _*).Additive] :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (f _*).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(f _*).Additive]

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ
local notation "DX" => DerivedCategory (RingedSpace.Modules X)
local notation "QX" => (DerivedCategory.Q : CpxX ⥤ DX)
local notation "QisX" =>
  HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)

/-- The cochain-level pushforward owner admits an everywhere defined total right derived functor.
-/
theorem modulePushforwardToDerived_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) QisX := by
  let _ : IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
    sheafModules_isGrothendieckAbelian X
  simpa [modulePushforwardToDerived] using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor (f _*))

/-- The canonical right-derived-functor instance for cochain-level pushforward. -/
instance instHasRightDerivedFunctorModulePushforwardToDerived :
    Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) QisX :=
  modulePushforwardToDerived_hasRightDerivedFunctor f

end

/-- The total right derived pushforward functor on derived categories of `\mathcal O_X`-modules.
-/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(f _*).Additive] :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (RingedSpace.Modules Y) :=
  let QhX :
      HomotopyCategory (RingedSpace.Modules X) (ComplexShape.up ℤ) ⥤
        DerivedCategory (RingedSpace.Modules X) :=
    DerivedCategory.Qh
  let QisH :=
    HomotopyCategory.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)
  ((f _*).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (ComplexShape.up ℤ) ⥤
          DerivedCategory (RingedSpace.Modules Y))).totalRightDerived QhX QisH

/-- The canonical unit from cochain-level pushforward followed by localization to the derived
pushforward functor `R(f)_*`. -/
noncomputable abbrev moduleDerivedPushforwardUnit
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(f _*).Additive] :
    modulePushforwardToDerived f ⟶
      (DerivedCategory.Q :
        CochainComplex (RingedSpace.Modules X) ℤ ⥤
          DerivedCategory (RingedSpace.Modules X)) ⋙ moduleDerivedPushforward f := by
  let _ : IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
    sheafModules_isGrothendieckAbelian X
  let η :=
    Functor.totalRightDerivedUnit
      ((f _*).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSpace.Modules Y) (ComplexShape.up ℤ) ⥤
            DerivedCategory (RingedSpace.Modules Y)))
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules X) (ComplexShape.up ℤ) ⥤
          DerivedCategory (RingedSpace.Modules X))
      (HomotopyCategory.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ))
  have hη :
      (f _*).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh :
            HomotopyCategory (RingedSpace.Modules Y) (ComplexShape.up ℤ) ⥤
              DerivedCategory (RingedSpace.Modules Y)) ⟶
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSpace.Modules X) (ComplexShape.up ℤ) ⥤
            DerivedCategory (RingedSpace.Modules X)) ⋙
          moduleDerivedPushforward f := by
    simpa [moduleDerivedPushforward, additiveFunctorTotalRightDerived] using η
  let eSource :
      HomotopyCategory.quotient (RingedSpace.Modules X) (ComplexShape.up ℤ) ⋙
          ((f _*).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh :
              HomotopyCategory (RingedSpace.Modules Y) (ComplexShape.up ℤ) ⥤
                DerivedCategory (RingedSpace.Modules Y))) ≅
        modulePushforwardToDerived f :=
    (Functor.associator
        (HomotopyCategory.quotient (RingedSpace.Modules X) (ComplexShape.up ℤ))
        ((f _*).mapHomotopyCategory (ComplexShape.up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSpace.Modules Y) (ComplexShape.up ℤ) ⥤
            DerivedCategory (RingedSpace.Modules Y))).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryFactors (f _*) (ComplexShape.up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSpace.Modules Y) (ComplexShape.up ℤ) ⥤
            DerivedCategory (RingedSpace.Modules Y)) ≪≫
      Functor.associator
        ((f _*).mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient (RingedSpace.Modules Y) (ComplexShape.up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSpace.Modules Y) (ComplexShape.up ℤ) ⥤
            DerivedCategory (RingedSpace.Modules Y)) ≪≫
      Functor.isoWhiskerLeft
        ((f _*).mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso (RingedSpace.Modules Y))
  exact eSource.inv ≫
    Functor.whiskerLeft
      (HomotopyCategory.quotient (RingedSpace.Modules X) (ComplexShape.up ℤ))
      hη ≫
    (Functor.associator
      (HomotopyCategory.quotient (RingedSpace.Modules X) (ComplexShape.up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules X) (ComplexShape.up ℤ) ⥤
          DerivedCategory (RingedSpace.Modules X))
      (moduleDerivedPushforward f)).hom ≫
    (Functor.isoWhiskerRight
      (DerivedCategory.quotientCompQhIso (RingedSpace.Modules X))
      (moduleDerivedPushforward f)).hom

/-- The canonical morphism `\mathcal G[0] ⟶ Rf_*(\mathcal F[0])` induced by a morphism
`\varphi : \mathcal G ⟶ f_*\mathcal F`. -/
  noncomputable abbrev moduleDerivedPushforwardComparison
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (𝒢 : RingedSpace.Modules Y) (ℱ : RingedSpace.Modules X)
    (φ : 𝒢 ⟶ (f _*).obj ℱ) :
    (DerivedCategory.singleFunctor (RingedSpace.Modules Y) 0).obj 𝒢 ⟶
      (moduleDerivedPushforward f).obj
        ((DerivedCategory.singleFunctor (RingedSpace.Modules X) 0).obj ℱ) :=
  (DerivedCategory.Q.map ((CochainComplex.singleFunctor (RingedSpace.Modules Y) 0).map φ)) ≫
    DerivedCategory.Q.map (((f _*).mapCochainComplexSingleFunctor 0).inv.app ℱ) ≫
    (moduleDerivedPushforwardUnit f).app
      ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ)

/-- Applying derived global sections to `moduleDerivedPushforwardComparison f 𝒢 ℱ φ`. -/
noncomputable abbrev moduleDerivedGlobalSectionsMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (𝒢 : RingedSpace.Modules Y) (ℱ : RingedSpace.Modules X)
    (φ : 𝒢 ⟶ (f _*).obj ℱ) :
    (moduleDerivedGlobalSections Y).obj
        ((DerivedCategory.singleFunctor (RingedSpace.Modules Y) 0).obj 𝒢) ⟶
      (moduleDerivedGlobalSections Y).obj
        ((moduleDerivedPushforward f).obj
          ((DerivedCategory.singleFunctor (RingedSpace.Modules X) 0).obj ℱ)) :=
  (moduleDerivedGlobalSections Y).map
    (moduleDerivedPushforwardComparison f 𝒢 ℱ φ)

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceDerivedGlobalSections

/- Textbook surface notation for the derived global-sections functor `RΓ(X,-)` on a ringed
space. -/
@[inherit_doc AlgebraicGeometry.RingedSpace.moduleDerivedGlobalSections]
scoped notation3:max "RΓ(" X ")" =>
  AlgebraicGeometry.RingedSpace.moduleDerivedGlobalSections X

end RingedSpaceDerivedGlobalSections

namespace RingedSpaceDerivedPushforward

scoped notation:max "R(" f:max ")_*" =>
  AlgebraicGeometry.RingedSpace.moduleDerivedPushforward f

end RingedSpaceDerivedPushforward
