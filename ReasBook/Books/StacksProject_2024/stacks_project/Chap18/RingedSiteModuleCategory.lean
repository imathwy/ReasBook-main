import Mathlib
import StacksProject_2024.Chap07.Example_7_14_3
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap18.Definition_18_31_1
import StacksProject_2024.Chap18.Lemma_18_15_3
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite
namespace Hom

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : Hom X Y) :
    SheafOfModules.{max u v} X.structureSheaf ⥤ SheafOfModules.{max u v} Y.structureSheaf :=
  pushforward f

/-- The direct-image functor on module sheaves is the canonical right adjoint to pullback along
the underlying morphism of structure sheaves. -/
instance modulePushforward_isRightAdjoint {X Y : RingedSite.{u, v}} (f : Hom X Y)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint] :
    f.modulePushforward.IsRightAdjoint := by
  simpa [modulePushforward, pushforward] using
    (SheafOfModules.instIsRightAdjointPushforward (φ := f.structureSheafMap))

/-- The direct-image functor on module sheaves is additive, via the canonical pullback-pushforward
adjunction. -/
instance modulePushforward_additive {X Y : RingedSite.{u, v}} (f : Hom X Y)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint] :
    f.modulePushforward.Additive := by
  let _ : f.modulePushforward.IsRightAdjoint := modulePushforward_isRightAdjoint f
  exact Functor.additive_of_preservesBinaryBiproducts f.modulePushforward

end Hom
end RingedSite

namespace SheafOfModules.RingedSite

/- Basic Chapter 18 owners for sheaves of modules on a commutative ringed site. -/

/-- The same-site morphism of commutative ringed sites induced by a morphism of structure sheaves
on a fixed site. -/
abbrev sameSiteHom {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    RingedSite.ofCommRingSheaf J 𝒪' ⟶ RingedSite.ofCommRingSheaf J 𝒪 where
  base := 𝟭 C
  isMorphismOfSites := by
    change IsMorphismOfSites J J (𝟭 C)
    simpa using CategoryTheory.id_isMorphismOfSites_of_le le_rfl
  structureSheafMap := ringedSiteStructureMap α

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

/-- The same-site coextension functor `Hom_𝒪(𝒪', -)`,
realized as the canonical right adjoint of restriction of scalars along `α`. -/
abbrev coextendAlong
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    [(restrictionAlong α).IsLeftAdjoint] :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪' :=
  (restrictionAlong α).rightAdjoint

/-- Same-site restriction of scalars is exact on sheaves of modules. -/
theorem restrictionAlong_exact
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪')
      (ringedSiteModuleCategory J 𝒪)
      (restrictionAlong α) := by
  sorry

end

end SheafOfModules.RingedSite

export SheafOfModules.RingedSite
  (ringSheaf ringSheafMap ringedSiteStructureMap restrictionAlong coextendAlong
    restrictionAlong_exact ringedSiteModuleCategory unitModule IsFlat IsFlatHom isFlatHom_iff)
