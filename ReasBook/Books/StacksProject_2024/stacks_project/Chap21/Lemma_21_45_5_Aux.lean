import StacksProject_2024.Chap21.Definition_21_17_13_Core
import StacksProject_2024.Chap21.Definition_21_45_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace RingedSite.Hom
namespace ModuleDerived

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [HasBinaryProducts C]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [CategoryWithHomology (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L
    (curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪))]
variable [∀ U : C,
  CategoryWithHomology (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "DMod" => ModuleDerived X

local instance : Abelian (ModuleCat X) :=
  SheafOfModules.instAbelian (RingedSite.ofCommRingSheaf J 𝒪).structureSheaf

variable {K L : DMod} {n m a b : ℤ}

/-- Lemma 21.45.5 (1): if `K` is `n`-pseudo-coherent and belongs to `D^{≤ a}`, and `L` is
`m`-pseudo-coherent and belongs to `D^{≤ b}`, then `K ⊗^L L` is
`max (m + a) (n + b)`-pseudo-coherent. -/
@[stacks 09J3]
theorem IsMPseudoCoherent.tensor
    (hK : K.IsMPseudoCoherent n)
    (hKLE : K.IsLE a)
    (hL : L.IsMPseudoCoherent m)
    (hLLE : L.IsLE b) :
    ((K ⊗^L L : DMod)).IsMPseudoCoherent (max (m + a) (n + b)) := by
  sorry

/-- Lemma 21.45.5 (2): if `K` and `L` are pseudo-coherent, then `K ⊗^L L` is pseudo-coherent. -/
@[stacks 09J3]
theorem IsPseudoCoherent.tensor
    (hK : K.IsPseudoCoherent)
    (hL : L.IsPseudoCoherent) :
    ((K ⊗^L L : DMod)).IsPseudoCoherent := by
  sorry

end

end ModuleDerived
end RingedSite.Hom
