import StacksProject_2024.Chap24.Aux_24_34_2
import StacksProject_2024.Chap24.Lemma_24_30_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v uA uB vA vB

namespace CategoryTheory.ModulesOnCategory

-- Semantic recall note: `lean_leansearch` returned the existing Chapter 21/24 owner-level APIs
-- `CategoryTheory.ModulesOnCategory.QC` and `CategoryTheory.ObjectProperty.lift`; this file
-- follows the restricted-equivalence pattern of `Chap21/Lemma_21_43_4.lean`.

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "ModO" => SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪
variable [CategoryWithHomology ModO]
variable {A B : CochainComplex ModO ℤ}
variable {DGModA : Type uA} [Category.{vA} DGModA]
variable [Abelian DGModA] [CategoryWithHomology DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB]
variable [Abelian DGModB] [CategoryWithHomology DGModB]
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

/-- Lemma 24.34.2: let `\mathcal C, \mathcal O` be as in Section `24.33`, and let
`\varphi : \mathcal A \to \mathcal B` be a homomorphism of differential graded
`\mathcal O`-algebras inducing an isomorphism on cohomology sheaves. Formalized with the chosen
Section `24.33` comparison data defining `QC(\mathcal A, d)` and `QC(\mathcal B, d)`, if the
derived extension-of-scalars / restriction adjunction is the equivalence of Lemma `24.30.1` and
both functors preserve quasi-coherent objects, then the induced restricted functor
`QC(\mathcal A, d) ⥤ QC(\mathcal B, d)` is an equivalence. -/
theorem derivedTensorExtensionToQC_isEquivalence_of_inducesIsoOnCohomologySheaves
    (φ : A ⟶ B)
    (hφ : ∀ n : ℤ, IsIso ((HomologicalComplex.homologyFunctor ModO (up ℤ) n).map φ))
    (derivedTensorExtension : DerivedCategory DGModA ⥤ DerivedCategory DGModB)
    (derivedRestriction : DerivedCategory DGModB ⥤ DerivedCategory DGModA)
    (adj : derivedTensorExtension ⊣ derivedRestriction)
    (hunit :
      (∀ n : ℤ, IsIso ((HomologicalComplex.homologyFunctor ModO (up ℤ) n).map φ)) →
        ∀ M : DerivedCategory DGModA, IsIso (adj.unit.app M))
    (hkernel : derivedRestriction.kernel ≤ IsZero)
    (hforward_mem :
      ∀ K : SrcQC,
        TgtQCP ((ObjectProperty.ι SrcQCP ⋙ derivedTensorExtension).obj K))
    (hbackward_mem :
      ∀ K : TgtQC,
        SrcQCP ((ObjectProperty.ι TgtQCP ⋙ derivedRestriction).obj K)) :
    Functor.IsEquivalence
      (derivedTensorExtensionToQC
        𝒜 𝒝 RGammaA RGammaB derivedRestrictA derivedRestrictB comparisonA comparisonB
        derivedTensorExtension hforward_mem) := sorry

end

end CategoryTheory.ModulesOnCategory
