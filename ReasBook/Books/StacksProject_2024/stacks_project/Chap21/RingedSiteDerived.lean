import StacksProject_2024.Chap21.RingedSiteDerivedBasic
import StacksProject_2024.Chap21.Definition_21_47_1

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section Perfectness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The perfectness predicate on `RingedSiteDerived J 𝒪`, transported from the synonymous owner
`ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)`. This is a bridge, not a second root owner. -/
abbrev RingedSiteDerived.IsPerfect
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasBinaryProducts C]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, (_root_.RingedSite.Hom.localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
    [∀ U : C, PreservesFiniteLimits
      (_root_.RingedSite.Hom.localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
    [∀ U : C, PreservesFiniteColimits
      (_root_.RingedSite.Hom.localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
    [CategoryWithHomology (_root_.RingedSite.Hom.ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
    [∀ U : C, CategoryWithHomology
      (_root_.RingedSite.Hom.ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
    (K : RingedSiteDerived J 𝒪) : Prop :=
  _root_.RingedSite.Hom.ModuleDerived.IsPerfect
    (show _root_.RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪) from K)

end Perfectness

end SheafOfModules.RingedSite
