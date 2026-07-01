import Mathlib
import stacks_project.Chap19.Lemma_19_13_6
import stacks_project.Chap20.Lemma_20_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of modules on a ringed space. -/
/-- The category of `\mathcal O_X`-modules on a ringed space is Grothendieck abelian. -/
instance sheafModules_isGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian (Modules X) := sorry

/-- The ring of global sections `Γ(X, \mathcal O_X)` of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{u}) : CommRingCat :=
  X.presheaf.obj (op (⊤ : Opens X.carrier))

/-- The global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSpace.{u}) :
    Modules X ⥤ ModuleCat (globalSectionsRing X) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op (⊤ : Opens X.carrier))

/-- The global-sections functor on module sheaves is additive. -/
instance moduleGlobalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).Additive := sorry

/-- The total right derived global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleDerivedGlobalSections (X : RingedSpace.{u}) :
    DerivedCategory (Modules X) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (moduleGlobalSectionsFunctor X)

/-- The underived functor of global sections with support in the closed subset `Z`, valued in
`Γ(X, \mathcal O_X)`-modules. It is formalized as global sections on `X` after pushing the
sections-with-support sheaf on `Z` back to `X`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    Modules X ⥤ ModuleCat (globalSectionsRing X) :=
  closedSubsetModuleSectionsWithSupportFunctor X hZ ⋙
    closedSubsetModulePushforward X Z ⋙
      moduleGlobalSectionsFunctor X

/-- The underived global-sections-with-support functor is additive. -/
instance closedSubsetModuleGlobalSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetModuleGlobalSectionsWithSupportFunctor X hZ).Additive := sorry

/-- The total right derived functor computing global sections with support in `Z`, viewed in
`D(Γ(X, \mathcal O_X(X)))`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    DerivedCategory (Modules X) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (closedSubsetModuleGlobalSectionsWithSupportFunctor X hZ)

-- Proof sketch: the underived functor of sections with support in `Z` and values in
-- `Γ(X,\mathcal O_X(X))` is the composite
-- `\mathcal H_Z ⋙ i_* ⋙ \Gamma(X,-)`, where `i : Z ↪ X` is the closed-subset inclusion.
-- Choose K-injective resolutions on `X`, use Lemma `20.34.3` to see that `\mathcal H_Z`
-- preserves K-injectives, and use exactness of `i_*` to compare the total right derived functor
-- of the composite with the composite of the derived functors.
/-- Lemma 20.34.4: for a ringed space `(X, \mathcal O_X)` and the inclusion of a closed subset
`i : Z \to X`, the derived global-sections functor on `Z` composed with the derived
sections-with-support functor agrees with the derived global-sections-with-support functor on `X`.
In this file the codomain `D(\mathcal O_X(X))` is modeled by first pushing the supported sheaf on
`Z` forward to `X` and then applying `RΓ(X,-)`. -/
theorem closedSubsetModuleGlobalSectionsWithSupportDerived_iso_comp
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    IsIsomorphic
      (closedSubsetModuleSectionsWithSupportDerived X hZ ⋙
        closedSubsetModulePushforwardDerived X Z ⋙
        moduleDerivedGlobalSections X)
      (closedSubsetModuleGlobalSectionsWithSupportDerived X hZ) := sorry

end AlgebraicGeometry.RingedSpace
