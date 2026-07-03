import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap19.Lemma_19_13_6
import stacks_project.Chap20.Lemma_20_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.DerivedCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The category of `\mathcal O_X`-modules on a ringed space is Grothendieck abelian. -/
instance sheafModules_isGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian (RingedSpace.Modules X) := sorry

/-- The ring of global sections `Γ(X, \mathcal O_X)` of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{u}) : CommRingCat :=
  SheafedSpace.Γ.obj (op X)

/-- The global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ ModuleCat (globalSectionsRing X) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op (⊤ : Opens X.carrier))

/-- The global-sections functor on `\mathcal O_X`-modules is additive. -/
instance moduleGlobalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).Additive := sorry

/-- The total right derived global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleDerivedGlobalSections (X : RingedSpace.{u}) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (moduleGlobalSectionsFunctor X)

/-- Direct image on sheaves of modules is additive. -/
instance modulePushforward_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (f _*).Additive := sorry

/-- The total right derived pushforward functor on derived categories of `\mathcal O_X`-modules.
-/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  CategoryTheory.additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (f _*)

/-- The canonical morphism `\mathcal G ⟶ Rf_* \mathcal F` attached to an `f`-map. -/
abbrev moduleSingleToDerivedPushforward {X Y : RingedSpace.{u}}
    (f : X ⟶ Y) (𝒢 : (RingedSpace.Modules Y)) (ℱ : (RingedSpace.Modules X))
    (φ : 𝒢 ⟶ (f _*).obj ℱ) :
    (DerivedCategory.singleFunctor (RingedSpace.Modules Y) 0).obj 𝒢 ⟶
      (moduleDerivedPushforward f).obj ((DerivedCategory.singleFunctor (RingedSpace.Modules X) 0).obj ℱ) :=
  let pushforwardToDerived :
      CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y) :=
    (f _*).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y))
  (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y)).map
      (((CochainComplex.singleFunctor (RingedSpace.Modules Y) 0).map φ) ≫
        (((f _*).mapCochainComplexSingleFunctor 0).inv.app ℱ)) ≫
    ((pushforwardToDerived.totalRightDerivedUnit
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
        (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ))).app
      ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ))

/-- 20.14.1.1: an `f`-map `φ : \mathcal G ⟶ f_* \mathcal F` induces the canonical morphism
`φ : RΓ(Y, \mathcal G) ⟶ RΓ(X, \mathcal F)` in `D(Γ(Y, \mathcal O_Y(Y)))`, where the target is
viewed via the identification `RΓ(X, \mathcal F) = RΓ(Y, Rf_* \mathcal F)`. -/
abbrev moduleDerivedGlobalSectionsMap {X Y : RingedSpace.{u}}
    (f : X ⟶ Y) (𝒢 : (RingedSpace.Modules Y)) (ℱ : (RingedSpace.Modules X))
    (φ : 𝒢 ⟶ (f _*).obj ℱ) :
    (moduleDerivedGlobalSections Y).obj ((DerivedCategory.singleFunctor (RingedSpace.Modules Y) 0).obj 𝒢) ⟶
      (moduleDerivedGlobalSections Y).obj
        ((moduleDerivedPushforward f).obj ((DerivedCategory.singleFunctor (RingedSpace.Modules X) 0).obj ℱ)) :=
  (moduleDerivedGlobalSections Y).map (moduleSingleToDerivedPushforward f 𝒢 ℱ φ)

/-- The canonical morphism on derived global sections is obtained by applying `RΓ(Y, -)` to the
canonical derived pushforward morphism attached to `φ`. -/
theorem moduleDerivedGlobalSectionsMap_def {X Y : RingedSpace.{u}}
    (f : X ⟶ Y) (𝒢 : (RingedSpace.Modules Y)) (ℱ : (RingedSpace.Modules X))
    (φ : 𝒢 ⟶ (f _*).obj ℱ) :
    moduleDerivedGlobalSectionsMap f 𝒢 ℱ φ =
      (moduleDerivedGlobalSections Y).map (moduleSingleToDerivedPushforward f 𝒢 ℱ φ) :=
  rfl

end AlgebraicGeometry.RingedSpace
