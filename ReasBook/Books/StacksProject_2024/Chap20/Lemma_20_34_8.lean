import Mathlib
import StacksProject_2024.Chap20.Lemma_20_21_1
import StacksProject_2024.Chap20.Lemma_20_25_1
import StacksProject_2024.Chap20.Lemma_20_32_7
import StacksProject_2024.Chap20.Lemma_20_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The inclusion of a closed subset into the underlying topological space of a ringed space. -/
abbrev closedSubsetInclusion
    (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inverse-image map on opens induced by the closed-subset inclusion is continuous for the
canonical Grothendieck topologies. -/
instance closedSubsetInclusion_opensMap_isContinuous
    (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
abbrev ClosedSubsetSheafModules (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules
    ((TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X))

/-- The abelian category of sheaves on the closed subset `Z` of a ringed space `X`. -/
abbrev ClosedSubsetAbelianSheafCat (X : RingedSpace.{u}) (Z : Set X) :=
  TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)

/-- The underived global-sections functor on abelian sheaves over the underlying space of a
ringed space. -/
abbrev abelianGlobalSectionsFunctor (X : RingedSpace.{u}) :
    AbelianSheafCat X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X.carrier))

/-- Global sections on abelian sheaves are additive. -/
instance abelianGlobalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (abelianGlobalSectionsFunctor X).Additive := sorry

/-- The forgetful functor from `\mathcal O_X|_Z`-modules to their underlying abelian sheaves on
the closed subset `Z`. -/
abbrev closedSubsetUnderlyingAbelianSheafFunctor
    (X : RingedSpace.{u}) (Z : Set X) :
    ClosedSubsetSheafModules X Z ⥤ ClosedSubsetAbelianSheafCat X Z :=
  SheafOfModules.toSheaf
    ((TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X))

/-- The derived forgetful functor from `D(\mathcal O_X|_Z)` to the derived category of abelian
sheaves on `Z`. -/
instance closedSubsetUnderlyingAbelianSheafFunctor_additive
    (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetUnderlyingAbelianSheafFunctor X Z).Additive := sorry

/-- The derived forgetful functor from `D(\mathcal O_X|_Z)` to the derived category of abelian
sheaves on `Z`. -/
abbrev closedSubsetUnderlyingAbelianSheafDerived
    (X : RingedSpace.{u}) (Z : Set X)
    [IsGrothendieckAbelian.{u} (ClosedSubsetSheafModules X Z)] :
    closedSubsetModuleDerived X Z ⥤
      DerivedCategory (ClosedSubsetAbelianSheafCat X Z) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetUnderlyingAbelianSheafFunctor X Z)

/-- The functor of sections with support in `Z` on underlying abelian sheaves. -/
abbrev closedSubsetAbelianSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    AbelianSheafCat X ⥤ ClosedSubsetAbelianSheafCat X Z :=
  𝓗[hZ]

/-- The sections-with-support functor on abelian sheaves is additive. -/
instance closedSubsetAbelianSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetAbelianSectionsWithSupportFunctor X hZ).Additive := sorry

/-- The derived sections-with-support functor on underlying abelian sheaves. -/
abbrev closedSubsetAbelianSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤
      DerivedCategory (ClosedSubsetAbelianSheafCat X Z) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetAbelianSectionsWithSupportFunctor X hZ)

/-- The underived global-sections-with-support functor on `\mathcal O_X`-modules, viewed in
abelian groups after forgetting the module structure on global sections. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportAsAbelianFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  closedSubsetModuleSectionsWithSupportFunctor X hZ ⋙
    closedSubsetModulePushforward X Z ⋙
      moduleGlobalSectionsAdditiveFunctor X

/-- The total right derived functor computing `RΓ_Z(X, -)` in `D(\operatorname{Ab})`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportAsAbelianDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetModuleGlobalSectionsWithSupportAsAbelianFunctor X hZ)

/-- The underived global-sections-with-support functor on abelian sheaves over the underlying
space of `X`. -/
abbrev closedSubsetAbelianGlobalSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    AbelianSheafCat X ⥤ AddCommGrpCat.{u} :=
  closedSubsetAbelianSectionsWithSupportFunctor X hZ ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubsetInclusion X Z) ⋙
      abelianGlobalSectionsFunctor X

/-- The underived abelian global-sections-with-support functor is additive. -/
instance closedSubsetAbelianGlobalSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetAbelianGlobalSectionsWithSupportFunctor X hZ).Additive := sorry

/-- The total right derived functor computing `RΓ_Z(X, -)` on underlying abelian sheaves. -/
abbrev closedSubsetAbelianGlobalSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetAbelianGlobalSectionsWithSupportFunctor X hZ)

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [IsGrothendieckAbelian.{u} (AbelianSheafCat X)]
variable [IsGrothendieckAbelian.{u} (ClosedSubsetSheafModules X Z)]
variable [IsGrothendieckAbelian.{u} (ClosedSubsetAbelianSheafCat X Z)]

local notation "DModX" => ringedSpaceModuleDerived X
local notation "Kab" => underlyingAbelianSheafDerived X
local notation "KabZ" => closedSubsetUnderlyingAbelianSheafDerived X Z
local notation "RGammaSupportMod" =>
  closedSubsetModuleGlobalSectionsWithSupportAsAbelianDerived X hZ
local notation "RGammaSupportAb" =>
  closedSubsetAbelianGlobalSectionsWithSupportDerived X hZ
local notation "RHSupportMod" =>
  closedSubsetModuleSectionsWithSupportDerived X hZ
local notation "RHSupportAb" =>
  closedSubsetAbelianSectionsWithSupportDerived X hZ

-- Proof sketch: for `RΓ_Z(X,-)`, compare the distinguished triangles of Lemmas `20.34.5` for
-- module sheaves and for underlying abelian sheaves, and use Lemma `20.32.7` on the two ordinary
-- derived-sections terms together with the two-out-of-three principle from Derived Categories,
-- Lemma `13.4.3`. For `R\mathcal H_Z`, repeat the same argument with the distinguished triangles
-- of Lemma `20.34.6`.
/-- Lemma 20.34.8: after forgetting `\mathcal O_X`-module structure to underlying abelian
sheaves, both derived global sections with support and derived sections with support agree with
their abelian local-cohomology counterparts. In other words, for `K_{ab}` the image of
`K ∈ D(\mathcal O_X)` in the derived category of abelian sheaves on `X`, the canonical
comparisons `RΓ_Z(X, K) → RΓ_Z(X, K_{ab})` in `D(\operatorname{Ab})` and
`R\mathcal H_Z(K) → R\mathcal H_Z(K_{ab})` in `D(\underline{\mathbf Z}_Z)` are isomorphisms. -/
theorem localCohomologyWithSupport_underlyingAbelian_isomorphic
    (K : DModX) :
    IsIsomorphic
        ((RGammaSupportMod).obj K)
        ((RGammaSupportAb).obj ((Kab).obj K)) ∧
      IsIsomorphic
        ((KabZ).obj ((RHSupportMod).obj K))
        ((RHSupportAb).obj ((Kab).obj K)) := sorry

end

end AlgebraicGeometry.RingedSpace
