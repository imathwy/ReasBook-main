import Mathlib
import stacks_project.Chap06.Definition_6_31_2
import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import stacks_project.Chap20.Lemma_20_11_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open CategoryTheory.DerivedCategory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The ring `Γ(U, \mathcal O_X)` of sections of the structure sheaf over an open subset `U`. -/
abbrev sectionsRingOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op U)

/-- Modules over `Γ(U, \mathcal O_X)` have their standard derived category. -/
instance sectionsRingOnOpen_hasDerivedCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  HasDerivedCategory.standard (ModuleCat (sectionsRingOnOpen X U))

/-- The sections functor `\Gamma(U, -)` on `\mathcal O_X`-modules. -/
abbrev moduleSectionsFunctorAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)

/-- The sections functor on an open subset is additive. -/
instance moduleSectionsFunctorAtOpen_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsFunctorAtOpen X U).Additive := sorry

/-- The category of `\mathcal O_U`-modules obtained by pulling the structure sheaf of `X` back to
the open subspace `U`. -/
abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))

/-- The category of modules over the pulled-back structure sheaf on the open subspace has its
standard derived category. -/
instance openSubspaceModuleCategory_hasDerivedCategory
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (openSubspaceModuleCategory X U) :=
  HasDerivedCategory.standard (openSubspaceModuleCategory X U)

/-- The ring of global sections of the pulled-back structure sheaf on the open subspace `U`. -/
abbrev openSubspaceGlobalSectionsRing (X : RingedSpace.{u}) (U : Opens X.carrier) : RingCat :=
  ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X)).1.obj
    (op (⊤ : Opens U))

/-- Modules over the global-sections ring of the open subspace carry the standard derived
category. -/
instance openSubspaceGlobalSectionsRing_hasDerivedCategory
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
  HasDerivedCategory.standard (ModuleCat (openSubspaceGlobalSectionsRing X U))

/-- The global-sections functor on `\mathcal O_U`-modules over the open subspace `U`. -/
abbrev openSubspaceGlobalSectionsFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ ModuleCat (openSubspaceGlobalSectionsRing X U) :=
  SheafOfModules.evaluation
    ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))
    (op (⊤ : Opens U))

/-- The global-sections functor on the open subspace is additive. -/
instance openSubspaceGlobalSectionsFunctor_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (openSubspaceGlobalSectionsFunctor X U).Additive := sorry

/-- Restriction of `\mathcal O_X`-modules from `X` to the open subspace `U`. -/
abbrev moduleRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ openSubspaceModuleCategory X U :=
  moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)

/-- Restriction to an open subspace is additive on sheaves of modules. -/
instance moduleRestrictionToOpen_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).Additive := sorry

-- Proof sketch: restriction to the open subspace is exact on the underlying abelian sheaves, and
-- the forgetful functor from module sheaves to abelian sheaves reflects finite limits and finite
-- colimits. Hence restriction is exact on sheaves of `\mathcal O_X`-modules.
/-- Restriction to an open subspace is exact on sheaves of modules. -/
theorem moduleRestrictionToOpen_exact (X : RingedSpace.{u}) (U : Opens X.carrier) :
    exactFunctor (RingedSpace.Modules X) (openSubspaceModuleCategory X U)
      (moduleRestrictionToOpen X U) := sorry

/-- The exact-functor package attached to restricting module sheaves to the open subspace `U`. -/
abbrev moduleRestrictionToOpenExactFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ₑ openSubspaceModuleCategory X U :=
  let _ : PreservesFiniteLimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact X U)).1
  let _ : PreservesFiniteColimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact X U)).2
  ExactFunctor.of (moduleRestrictionToOpen X U)

/-- The complex-level sections functor on an open subset, followed by localization to the derived
category of modules over `Γ(U, \mathcal O_X)`. -/
abbrev moduleSectionsToDerivedAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  let _ : (moduleSectionsFunctorAtOpen X U).Additive := moduleSectionsFunctorAtOpen_additive X U
  let _ : (moduleSectionsFunctorAtOpen X U).PreservesZeroMorphisms := inferInstance
  (moduleSectionsFunctorAtOpen X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Q :
      CochainComplex (ModuleCat (sectionsRingOnOpen X U)) ℤ ⥤
        DerivedCategory (ModuleCat (sectionsRingOnOpen X U)))

-- Proof sketch: compute the derived functor of `Γ(U, -)` by resolving a complex of
-- `\mathcal O_X`-modules by a K-injective complex and applying the sections functor degreewise.
/-- The complex-level sections functor on an open subset admits a total right derived functor. -/
theorem moduleSectionsToDerivedAtOpen_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsToDerivedAtOpen X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) := sorry

/-- The canonical right-derived-functor instance for sections on an open subset. -/
instance moduleSectionsToDerivedAtOpen_instHasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsToDerivedAtOpen X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
  moduleSectionsToDerivedAtOpen_hasRightDerivedFunctor X U

/-- The total right derived functor `RΓ(U, -)` on the ambient derived category
`D(\mathcal O_X)`. -/
abbrev moduleDerivedSectionsAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  (moduleSectionsToDerivedAtOpen X U).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ))

/-- The restriction functor on derived categories induced by exact restriction to the open
subspace `U`. -/
abbrev moduleRestrictionToOpenDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (openSubspaceModuleCategory X U) :=
  let _ : (moduleRestrictionToOpenExactFunctor X U).obj.Additive :=
    moduleRestrictionToOpen_additive X U
  (moduleRestrictionToOpenExactFunctor X U).obj.mapDerivedCategory

/-- The complex-level global-sections functor on the open subspace, followed by localization to
its derived category. -/
abbrev openSubspaceGlobalSectionsToDerived
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
      DerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
  let _ : (openSubspaceGlobalSectionsFunctor X U).Additive :=
    openSubspaceGlobalSectionsFunctor_additive X U
  let _ : (openSubspaceGlobalSectionsFunctor X U).PreservesZeroMorphisms := inferInstance
  (openSubspaceGlobalSectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Q :
      CochainComplex (ModuleCat (openSubspaceGlobalSectionsRing X U)) ℤ ⥤
        DerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)))

-- Proof sketch: compute the derived functor of global sections on the open subspace by a
-- K-injective resolution in the category of `\mathcal O_U`-modules and apply the sections
-- functor degreewise.
/-- The complex-level global-sections functor on the open subspace admits a total right derived
functor. -/
theorem openSubspaceGlobalSectionsToDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (openSubspaceGlobalSectionsToDerived X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ)) := sorry

/-- The canonical right-derived-functor instance for global sections on the open subspace. -/
instance openSubspaceGlobalSectionsToDerived_instHasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (openSubspaceGlobalSectionsToDerived X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ)) :=
  openSubspaceGlobalSectionsToDerived_hasRightDerivedFunctor X U

/-- The total right derived functor of global sections on the open subspace `U`. -/
abbrev openSubspaceDerivedGlobalSections
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤
      DerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
  (openSubspaceGlobalSectionsToDerived X U).totalRightDerived
    (DerivedCategory.Q :
      CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
        DerivedCategory (openSubspaceModuleCategory X U))
    (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ))

/-- The ambient hypercohomology group `H^p(U, K)` of a derived `\mathcal O_X`-module, viewed as
an object of `AddCommGrpCat`. -/
abbrev moduleOpenHypercohomology
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) : AddCommGrpCat.{u} :=
  let _ : HasDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
    sectionsRingOnOpen_hasDerivedCategory X U
  (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
    ((DerivedCategory.homologyFunctor (ModuleCat (sectionsRingOnOpen X U)) p).obj
      ((moduleDerivedSectionsAtOpen X U).obj K))

/-- The hypercohomology group of the restricted derived object on the open subspace `X|_U`,
viewed as an object of `AddCommGrpCat`. -/
abbrev restrictedModuleOpenHypercohomology
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) : AddCommGrpCat.{u} :=
  let _ : HasDerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
    openSubspaceGlobalSectionsRing_hasDerivedCategory X U
  (forget₂ (ModuleCat (openSubspaceGlobalSectionsRing X U)) AddCommGrpCat.{u}).obj
    ((DerivedCategory.homologyFunctor (ModuleCat (openSubspaceGlobalSectionsRing X U)) p).obj
      ((openSubspaceDerivedGlobalSections X U).obj
        ((moduleRestrictionToOpenDerived X U).obj K)))

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

-- Proof sketch: represent `K` by a K-injective complex `I`. The ambient functor `RΓ(U, -)` is
-- computed by the sections complex `Γ(U, I)`. By Lemma `20.32.1`, the restricted complex `I|_U`
-- is K-injective on the open subspace `X|_U`, so `RΓ(X|_U, K|_U)` is computed by the same
-- sections complex `Γ(U, I|_U) = Γ(U, I)`. Taking degree-`p` cohomology yields the comparison.
/-- Lemma 20.32.2: for a ringed space `X`, an open subset `U ⊆ X`, an object `K` of
`D(\mathcal O_X)`, and an integer `p`, the hypercohomology group `H^p(U, K)` is canonically
isomorphic to the hypercohomology group of the restricted object `K|_U` on the open subspace
`X|_U`. -/
theorem openHypercohomology_isomorphic_restricted
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) :
    IsIsomorphic
      (moduleOpenHypercohomology X U K p)
      (restrictedModuleOpenHypercohomology X U K p) := sorry

end

end AlgebraicGeometry.RingedSpace
