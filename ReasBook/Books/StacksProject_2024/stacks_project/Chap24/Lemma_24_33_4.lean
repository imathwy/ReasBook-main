import StacksProject_2024.stacks_project.Chap24.Definition_24_33_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe uC vC uC' vC' uA vA uA' vA'

namespace CategoryTheory.ModulesOnCategory

-- Semantic recall note: `lean_leansearch` returned the canonical full-subcategory restriction API
-- `CategoryTheory.ObjectProperty.lift`; the owner-level landing statement below follows the local
-- Chapter 21 precedent `Lemma_21_43_10`, specialized to the Section `24.33` DG-module data.

section

variable {C : Type uC} [Category.{vC} C]
variable {C' : Type uC'} [Category.{vC'} C']
variable {DGModA : Type uA} [Category.{vA} DGModA] [Abelian DGModA]
variable [CategoryWithHomology DGModA]
variable {DGModA' : Type uA'} [Category.{vA'} DGModA'] [Abelian DGModA']
variable [CategoryWithHomology DGModA']
variable (𝒜 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable (𝒜' : C'ᵒᵖ ⥤ CommRingCat.{uC'})
variable (u : C' ⥤ C)
variable
  (RGamma :
    ∀ U : C,
      DerivedCategory DGModA ⥤ DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (RGamma' :
    ∀ U' : C',
      DerivedCategory DGModA' ⥤ DerivedCategory (ModuleCat (𝒜'.obj (op U'))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒜.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (derivedRestrict' :
    ∀ {U' V' : C'}, (U' ⟶ V') →
      DerivedCategory (ModuleCat (𝒜'.obj (op V'))) ⥤
        DerivedCategory (ModuleCat (𝒜'.obj (op U'))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable
  (comparison' :
    ∀ {U' V' : C'} (f' : U' ⟶ V'),
      RGamma' V' ⋙ derivedRestrict' f' ⟶ RGamma' U')

local notation "SrcQCP" => isQuasiCoherent 𝒜 RGamma derivedRestrict comparison
local notation "TgtQCP" => isQuasiCoherent 𝒜' RGamma' derivedRestrict' comparison'

/-- Lemma 24.33.4: with the Section `24.33` comparison data defining `QC(\mathcal A, d)` and
`QC(\mathcal A', d)`, suppose `Lg^* : D(\mathcal A, d) ⥤ D(\mathcal A', d)` is a derived
pullback functor for a morphism of ringed topoi together with a compatible morphism
`g^*\mathcal A \to \mathcal A'`, and suppose the target comparison morphisms for `Lg^* K` are
obtained from the source comparison morphisms via the sectionwise base-change identification of
Lemma `24.28.4`. Then `Lg^*` maps `QC(\mathcal A, d)` into `QC(\mathcal A', d)`. -/
theorem dgQc_le_inverseImage_leftDerivedPullback
    (leftDerivedPullback : DerivedCategory DGModA ⥤ DerivedCategory DGModA')
    (hLg :
      ∀ {U' V' : C'} (f' : U' ⟶ V') {K : DerivedCategory DGModA},
        IsIso ((comparison (u.map f')).app K) →
          IsIso ((comparison' f').app (leftDerivedPullback.obj K))) :
    SrcQCP ≤ ObjectProperty.inverseImage TgtQCP leftDerivedPullback := sorry

end

end CategoryTheory.ModulesOnCategory
