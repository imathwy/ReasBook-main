import Mathlib
import StacksProject_2024.Chap20.«20_14_1_1»

open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of modules on a ringed space. -/
abbrev ringedSpaceModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The inclusion of a closed subset into the ambient ringed space. -/
abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction `\mathcal O_X|_Z` of the structure sheaf to a closed subset `Z ⊆ X`. -/
abbrev closedSubsetRestrictedRingCatSheaf
    (X : RingedSpace.{u}) (Z : Set X) : TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X)

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
abbrev closedSubsetModuleCategory (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRestrictedRingCatSheaf X Z)

/-- The unbounded derived category `D(\mathcal O_X|_Z)` on the closed subset `Z`. -/
abbrev closedSubsetModuleDerived (X : RingedSpace.{u}) (Z : Set X) :=
  DerivedCategory (closedSubsetModuleCategory X Z)

/-- The unbounded derived category of abelian groups used for derived global sections. -/
abbrev abelianDerived :=
  DerivedCategory AddCommGrpCat.{u}

/-- The derived global-sections functor `RΓ(X, -)` after forgetting the module structure on
`Γ(X, \mathcal O_X)`. -/
abbrev derivedGlobalSectionsToAbelian (X : RingedSpace.{u}) :
    ringedSpaceModuleDerived X ⥤ abelianDerived :=
  moduleDerivedGlobalSections X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

-- Proof sketch: this is just the definition of `derivedGlobalSectionsToAbelian`; it is the usual
-- derived global-sections functor with the module structure on `Γ(X, \mathcal O_X)` forgotten.
/-- The abelian-valued derived global-sections functor is obtained by forgetting the ambient
module structure on `RΓ(X, -)`. -/
theorem derivedGlobalSectionsToAbelian_def (X : RingedSpace.{u}) :
    derivedGlobalSectionsToAbelian X =
      moduleDerivedGlobalSections X ⋙
        (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory := sorry

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

local notation "DModX" => ringedSpaceModuleDerived X
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "DAb" => abelianDerived

variable (restrictionToClosedSubset : DModX ⥤ DModZ)
variable (sectionsWithSupportDerived : DModX ⥤ DModZ)
variable (derivedGlobalSectionsOnClosedSubset : DModZ ⥤ DAb)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
variable (derivedTensorAb : DAb ⥤ DAb ⥤ DAb)
variable
    (closedSubsetDerivedCupProduct :
      ∀ (A B : DModZ),
        ((derivedTensorAb.obj (derivedGlobalSectionsOnClosedSubset.obj B)).obj
          (derivedGlobalSectionsOnClosedSubset.obj A)) ⟶
          derivedGlobalSectionsOnClosedSubset.obj ((derivedTensorZ.obj B).obj A))
variable
    (sectionsWithSupportTensorMap :
      ∀ (K M : DModX),
        ((derivedTensorZ.obj (sectionsWithSupportDerived.obj M)).obj
          (restrictionToClosedSubset.obj K)) ⟶
          sectionsWithSupportDerived.obj ((derivedTensorX.obj M).obj K))

/-- Remark 20.34.10: with the notation of Remark 20.34.9, restriction of `K` to the closed
subset `Z`, the cup product on `Z`, and the canonical map
`K|_Z \otimes_{\mathcal O_X|_Z}^{\mathbf L} R\mathcal H_Z(M) \to
R\mathcal H_Z(K \otimes_{\mathcal O_X}^{\mathbf L} M)` determine a canonical morphism in
`D(\mathrm{Ab})`. Its degree-`a + b` homology is the cup product
`H^a(X, K) × H^b_Z(X, M) \to H^{a + b}_Z(X, K \otimes_{\mathcal O_X}^{\mathbf L} M)`, where the
equalities in the textbook are the comparison isomorphisms of Lemma 20.34.4. -/
noncomputable def closedSubsetRestriction_sectionsWithSupportDerived_cupProduct
    (restrictionToClosedSubsetGlobalSections :
      derivedGlobalSectionsToAbelian X ⟶
        restrictionToClosedSubset ⋙ derivedGlobalSectionsOnClosedSubset)
    (K M : DModX) :
    ((derivedTensorAb.obj
        (derivedGlobalSectionsOnClosedSubset.obj (sectionsWithSupportDerived.obj M))).obj
      ((derivedGlobalSectionsToAbelian X).obj K)) ⟶
      derivedGlobalSectionsOnClosedSubset.obj
        (sectionsWithSupportDerived.obj ((derivedTensorX.obj M).obj K)) :=
  match restrictionToClosedSubsetGlobalSections with
  | η =>
      ((derivedTensorAb.obj
          (derivedGlobalSectionsOnClosedSubset.obj (sectionsWithSupportDerived.obj M))).map
        (η.app K)) ≫
        closedSubsetDerivedCupProduct
          (restrictionToClosedSubset.obj K) (sectionsWithSupportDerived.obj M) ≫
        derivedGlobalSectionsOnClosedSubset.map (sectionsWithSupportTensorMap K M)

-- Proof sketch: unfold the definition. The morphism is defined as the composite of the map on
-- derived global sections induced by restricting `K` to `Z`, the closed-subset cup product on
-- `Z`, and the map obtained by applying derived global sections on `Z` to the sections-with-
-- support tensor comparison.
/-- The closed-subset cup-product morphism is the composite of restriction on derived global
sections, the cup product on the closed subset, and the map induced by the sections-with-support
tensor comparison. -/
theorem closedSubsetRestriction_sectionsWithSupportDerived_cupProduct_def
    (restrictionToClosedSubsetGlobalSections :
      derivedGlobalSectionsToAbelian X ⟶
        restrictionToClosedSubset ⋙ derivedGlobalSectionsOnClosedSubset)
    (K M : DModX) :
    closedSubsetRestriction_sectionsWithSupportDerived_cupProduct
        hZ restrictionToClosedSubset sectionsWithSupportDerived
        derivedGlobalSectionsOnClosedSubset derivedTensorX derivedTensorZ derivedTensorAb
        closedSubsetDerivedCupProduct sectionsWithSupportTensorMap
        restrictionToClosedSubsetGlobalSections K M =
      ((derivedTensorAb.obj
          (derivedGlobalSectionsOnClosedSubset.obj (sectionsWithSupportDerived.obj M))).map
        (restrictionToClosedSubsetGlobalSections.app K)) ≫
        closedSubsetDerivedCupProduct
          (restrictionToClosedSubset.obj K) (sectionsWithSupportDerived.obj M) ≫
        derivedGlobalSectionsOnClosedSubset.map (sectionsWithSupportTensorMap K M) := sorry

end

end AlgebraicGeometry.RingedSpace
