import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.stacks_project.Chap17.Lemma_17_28_6
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_extension_abelian
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core
import StacksProject_2024.stacks_project.Chap20.RingedSpaceModuleHasDerivedCategory

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

private abbrev pullbackModuleCategory :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X))

private instance pullbackModuleCategory_abelian :
    Abelian (pullbackModuleCategory (X := X) U) := by
  simpa [pullbackModuleCategory] using
    (pullbackRingSheafModules_abelian (X := X) U)

private noncomputable abbrev openSubspaceRingSheafIso :
    RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding) ≅
      (TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X) := by
  let eComm :
      (X.restrict U.isOpenEmbedding).sheaf ≅
        (TopCat.Sheaf.pullback CommRingCat U.inclusion').obj X.sheaf :=
    ((U.isOpenEmbedding.sheafPullbackIso CommRingCat).symm.app X.sheaf)
  let _ :
      (Opens.grothendieckTopology ↑((Opens.toTopCat ↑X.toPresheafedSpace).obj U)).PreservesSheafification
        (forget₂ CommRingCat RingCat.{u}) := by
    simpa using
      (inferInstance :
        (Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
          (forget₂ CommRingCat RingCat.{u}))
  simpa [RingedSpace.ringCatSheaf] using
    (sheafCompose (Opens.grothendieckTopology (TopCat.of U)) (forget₂ CommRingCat RingCat)).mapIso
        eComm ≪≫
      TopCat.Sheaf.pullbackRingSheafIso U.inclusion' X.sheaf

private noncomputable abbrev moduleRestrictionAlongOpenSubspaceRingSheafIso :
    openSubspaceModuleCategory X U ⥤ pullbackModuleCategory (X := X) U :=
  SheafOfModules.restrictScalars (openSubspaceRingSheafIso U).inv

private instance moduleRestrictionAlongOpenSubspaceRingSheafIso_additive :
    (moduleRestrictionAlongOpenSubspaceRingSheafIso U).Additive := by
  sorry

private instance moduleRestrictionAlongOpenSubspaceRingSheafIso_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestrictionAlongOpenSubspaceRingSheafIso U) := by
  sorry

private instance moduleRestrictionAlongOpenSubspaceRingSheafIso_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestrictionAlongOpenSubspaceRingSheafIso U) := by
  sorry

private instance moduleSheafExtensionByZeroFromOpen_additive :
    (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).Additive := by
  sorry

private instance moduleSheafExtensionByZeroFromOpen_preservesFiniteLimits :
    PreservesFiniteLimits
      (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := by
  sorry

private instance moduleSheafExtensionByZeroFromOpen_preservesFiniteColimits :
    PreservesFiniteColimits
      (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := by
  let adj := moduleSheafExtensionByZeroAdjunction U (RingedSpace.ringCatSheaf X)
  let _ : PreservesColimits
      (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) :=
    adj.leftAdjoint_preservesColimits
  infer_instance

private abbrev pulledBackModuleSheafExtensionByZeroFromOpen :
    pullbackModuleCategory (X := X) U ⥤ RingedSpace.Modules X :=
  moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)

private instance pulledBackModuleSheafExtensionByZeroFromOpen_additive :
    (pulledBackModuleSheafExtensionByZeroFromOpen (X := X) U).Additive := by
  sorry

private instance pulledBackModuleSheafExtensionByZeroFromOpen_preservesFiniteLimits :
    PreservesFiniteLimits (pulledBackModuleSheafExtensionByZeroFromOpen (X := X) U) := by
  sorry

private instance pulledBackModuleSheafExtensionByZeroFromOpen_preservesFiniteColimits :
    PreservesFiniteColimits (pulledBackModuleSheafExtensionByZeroFromOpen (X := X) U) := by
  sorry

/-- The intrinsic extension-by-zero functor `j_! : Mod(\mathcal O_U) ⥤ Mod(\mathcal O_X)` for the
open immersion `j : U ↪ X`, obtained by composing the canonical change-of-rings bridge from the
restricted ringed space with the Chapter 6 extension-by-zero owner. -/
abbrev moduleExtensionByZeroFromOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    openSubspaceModuleCategory X U ⥤ RingedSpace.Modules X :=
  moduleRestrictionAlongOpenSubspaceRingSheafIso (X := X) U ⋙
    pulledBackModuleSheafExtensionByZeroFromOpen (X := X) U

instance moduleExtensionByZeroFromOpen_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpen X U).Additive := by
  sorry

instance moduleExtensionByZeroFromOpen_preservesFiniteLimits
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteLimits (moduleExtensionByZeroFromOpen X U) := by
  sorry

instance moduleExtensionByZeroFromOpen_preservesFiniteColimits
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteColimits (moduleExtensionByZeroFromOpen X U) := by
  sorry

/-- The intrinsic extension-by-zero functor on `\mathcal O_U`-modules is left adjoint to
restriction to the open subspace `U`. -/
noncomputable def moduleExtensionByZeroFromOpenAdjunction
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    moduleExtensionByZeroFromOpen X U ⊣ moduleRestrictionToOpen X U := by
  sorry

/-- The derived extension-by-zero functor `j_! : D(\mathcal O_U) ⥤ D(\mathcal O_X)` for the
open immersion `j : U ↪ X`. -/
abbrev moduleExtensionByZeroFromOpenDerived
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  letI : CategoryWithHomology (RingedSpace.Modules X) :=
    ringedSpaceModules_categoryWithHomology X
  letI : HasDerivedCategory (RingedSpace.Modules X) := HasDerivedCategory.standard _
  letI :
      Functor.IsLocalization
        (DerivedCategory.Q :
          CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
            DerivedCategory (openSubspaceModuleCategory X U))
        (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ)) :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  letI :
      Functor.IsLocalization
        (DerivedCategory.Q :
          CochainComplex (RingedSpace.Modules X) ℤ ⥤
            DerivedCategory (RingedSpace.Modules X))
        (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  let F : openSubspaceModuleCategory X U ⥤ RingedSpace.Modules X :=
    moduleExtensionByZeroFromOpen X U
  let hFadd : F.Additive := moduleExtensionByZeroFromOpen_additive X U
  let hFlim : PreservesFiniteLimits F :=
    moduleExtensionByZeroFromOpen_preservesFiniteLimits X U
  let hFcolim : PreservesFiniteColimits F :=
    moduleExtensionByZeroFromOpen_preservesFiniteColimits X U
  @Functor.mapDerivedCategory
    (openSubspaceModuleCategory X U) _ _ _
    (RingedSpace.Modules X) _ _ _
    F hFadd hFlim hFcolim

end

end AlgebraicGeometry.RingedSpace
