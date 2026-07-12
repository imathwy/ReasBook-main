import StacksProject_2024.Chap21.Aux_21_43_1

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v uA uB vA vB

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{v} C]
variable {DGModA : Type uA} [Category.{vA} DGModA]
variable [Abelian DGModA]
variable [CategoryWithHomology DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB]
variable [Abelian DGModB]
variable [CategoryWithHomology DGModB]
variable (𝒜 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (𝒝 : Cᵒᵖ ⥤ CommRingCat.{u})
variable
  (RGammaA : ∀ U : C, DerivedCategory DGModA ⥤ DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (RGammaB : ∀ U : C, DerivedCategory DGModB ⥤ DerivedCategory (ModuleCat (𝒝.obj (op U))))
variable
  (derivedRestrictA :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒜.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (derivedRestrictB :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒝.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒝.obj (op U))))
variable
  (comparisonA :
    ∀ {U V : C} (f : U ⟶ V),
      RGammaA V ⋙ derivedRestrictA f ⟶ RGammaA U)
variable
  (comparisonB :
    ∀ {U V : C} (f : U ⟶ V),
      RGammaB V ⋙ derivedRestrictB f ⟶ RGammaB U)

local notation "SrcQCP" => isQuasiCoherent 𝒜 RGammaA derivedRestrictA comparisonA
local notation "TgtQCP" => isQuasiCoherent 𝒝 RGammaB derivedRestrictB comparisonB
local notation "SrcQC" => QC 𝒜 RGammaA derivedRestrictA comparisonA
local notation "TgtQC" => QC 𝒝 RGammaB derivedRestrictB comparisonB

/-- The canonical restriction of a chosen derived tensor extension functor to the quasi-coherent
full subcategory `QC(\mathcal A, d) ⥤ QC(\mathcal B, d)`. -/
abbrev derivedTensorExtensionToQC
    (derivedTensorExtension : DerivedCategory DGModA ⥤ DerivedCategory DGModB)
    (hforward_mem :
      ∀ K : SrcQC,
        TgtQCP ((ObjectProperty.ι SrcQCP ⋙ derivedTensorExtension).obj K)) :
    SrcQC ⥤ TgtQC :=
  ObjectProperty.lift TgtQCP (ObjectProperty.ι SrcQCP ⋙ derivedTensorExtension) hforward_mem

/-- The canonical restriction of the derived restriction functor back to
`QC(\mathcal B, d) ⥤ QC(\mathcal A, d)`. -/
abbrev derivedRestrictionToQC
    (derivedRestriction : DerivedCategory DGModB ⥤ DerivedCategory DGModA)
    (hbackward_mem :
      ∀ K : TgtQC,
        SrcQCP ((ObjectProperty.ι TgtQCP ⋙ derivedRestriction).obj K)) :
    TgtQC ⥤ SrcQC :=
  ObjectProperty.lift SrcQCP (ObjectProperty.ι TgtQCP ⋙ derivedRestriction) hbackward_mem

end

end CategoryTheory.ModulesOnCategory
