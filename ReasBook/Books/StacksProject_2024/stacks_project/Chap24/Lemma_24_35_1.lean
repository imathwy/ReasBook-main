import StacksProject_2024.stacks_project.Chap24.Definition_24_33_1

-- Declarations for this item will be appended below by the statement pipeline.

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

/-
Domain-style sampling for Lemma 24.35.1:
- primary domain: quasi-coherent module categories attached to inverse systems of differential
  graded algebras and the comparison functors between them;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ObjectProperty.lift`,
  `CategoryTheory.ObjectProperty.ι`,
  `CategoryTheory.Functor.IsEquivalence`;
- source/core/bridge triage:
  `source-facing`: the Chapter 24 comparison functor `QC(\mathcal A, d) ⥤ QC(\mathcal B, d)`
    together with its chosen quasi-inverse coming from the inverse-system comparison data;
  `core/canonical`: `Functor.IsEquivalence`;
  `bridge/view`: the canonical full-subcategory restrictions built directly with
    `ObjectProperty.lift`, together with `Functor.IsEquivalence.mk'`.

This file therefore keeps the Chapter 24 quasi-coherent comparison surface visible and reuses the
canonical restricted-functor bridge `ObjectProperty.lift` together with the canonical equivalence
owner.
-/

section

variable
  (derivedTensorExtension : DerivedCategory DGModA ⥤ DerivedCategory DGModB)
  (derivedRestriction : DerivedCategory DGModB ⥤ DerivedCategory DGModA)
  (hforward_mem :
    ∀ K : SrcQC,
      TgtQCP ((ι SrcQCP ⋙ derivedTensorExtension).obj K))
  (hbackward_mem :
    ∀ K : TgtQC,
      SrcQCP ((ι TgtQCP ⋙ derivedRestriction).obj K))

local notation "forwardQC" =>
  lift TgtQCP (ι SrcQCP ⋙ derivedTensorExtension) hforward_mem

local notation "backwardQC" =>
  lift SrcQCP (ι TgtQCP ⋙ derivedRestriction) hbackward_mem

/-- Lemma 24.35.1: in the Chapter 24 inverse-system setting, if the chosen quasi-coherent
comparison functor `QC(\mathcal A, d) ⥤ QC(\mathcal B, d)` and the chosen restricted functor back
to `QC(\mathcal A, d)` are equipped with the canonical unit and counit isomorphisms coming from
the preceding pro-object comparison, then the quasi-coherent comparison functor is an
equivalence. -/
@[stacks 0GZH]
theorem derivedTensorExtensionToQC_isEquivalence_of_unitIso_counitIso
    (unitIso :
      𝟭 SrcQC ≅ forwardQC ⋙ backwardQC)
    (counitIso :
      backwardQC ⋙ forwardQC ≅ 𝟭 TgtQC) :
    Functor.IsEquivalence forwardQC := by
  exact Functor.IsEquivalence.mk' backwardQC unitIso counitIso

end

end CategoryTheory.ModulesOnCategory
