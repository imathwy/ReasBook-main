import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_6
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Sections_on_open

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling:
- primary domain: bounded-below derived sections on an open subset of a ringed space;
- sampled owner declarations:
  `SheafOfModules.evaluation`,
  `moduleSectionsEvaluation_additive`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `Functor.totalRightDerived`;
- best owner abstraction:
  `source-facing`: the bounded-below derived sections functor `RΓ(U,-)` on `D⁺(𝒪_X)`;
  `core/canonical`: the additive evaluation functor on `U` and the bounded-below total right
    derived owner;
  `bridge/view`: none in this core file.
- primitive data: a ringed space `X` and an open subset `U`;
- derived API: the bounded-below derived sections functor valued in
  the bounded-below derived category of `Γ(U, 𝒪_X)`-modules.

This file isolates the owner `boundedBelowDerivedSectionsAtOpen` from the heavier Čech-to-
cohomology comparison file so downstream users can depend on the canonical derived-sections owner
without importing the later delta-functor comparison layer. -/

/-- The bounded-below derived sections functor `RΓ(U,-)` on `D⁺(𝒪_X)`, valued in the bounded-
below derived category of `Γ(U, 𝒪_X)`-modules. -/
abbrev boundedBelowDerivedSectionsAtOpen
    (U : Opens X.carrier)
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow
        (SheafOfModules.evaluation X.ringCatSheaf (op U)))
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))] :
    boundedBelowDerivedCategory (RingedSpace.Modules X) ⥤
      boundedBelowDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  let F : RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : F.Additive := moduleSectionsEvaluation_additive X U
  let _ :
      Functor.HasRightDerivedFunctor
        (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
        (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X)) := by
    simpa [F] using
      (inferInstance :
        Functor.HasRightDerivedFunctor
          (mapBoundedBelowHomotopyCategoryToDerivedBelow
            (SheafOfModules.evaluation X.ringCatSheaf (op U)))
          (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X)))
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
    mapBoundedBelowHomotopyToDerivedBelow
    (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))

/-- The bounded-below derived global-sections functor `RΓ(X,-)` on `D⁺(𝒪_X)`, valued in the
bounded-below derived category of `Γ(X, 𝒪_X)`-modules. This is the top-open specialization of
`boundedBelowDerivedSectionsAtOpen`, recorded as a stable owner because it recurs throughout
Chapter 20 without any additional choice data. -/
abbrev boundedBelowDerivedGlobalSections (X : RingedSpace.{u})
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (moduleGlobalSectionsFunctor X))
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))] :
    boundedBelowDerivedCategory (RingedSpace.Modules X) ⥤
      boundedBelowDerivedCategory (ModuleCat (globalSectionsRing X)) :=
  let F : RingedSpace.Modules X ⥤ ModuleCat (globalSectionsRing X) := moduleGlobalSectionsFunctor X
  let _ : F.Additive := moduleGlobalSectionsFunctor_additive X
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
    mapBoundedBelowHomotopyToDerivedBelow
    (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))

end AlgebraicGeometry.RingedSpace
