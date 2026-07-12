import Mathlib
import StacksProject_2024.Chap07.Example_7_14_3
import StacksProject_2024.Chap18.Lemma_18_15_3
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite
namespace Hom

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : Hom X Y) :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf :=
  SheafOfModules.pushforward f.structureSheafMap

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

/-- The same-site coextension functor `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', -)`,
realized as the canonical right adjoint of restriction of scalars along `α`. -/
abbrev coextendAlong
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    [(restrictionAlong α).IsLeftAdjoint] :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪' :=
  (restrictionAlong α).rightAdjoint

omit [HasWeakSheafify J AddCommGrpCat] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Same-site restriction of scalars is exact on sheaves of modules. -/
theorem restrictionAlong_exact
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪')
      (ringedSiteModuleCategory J 𝒪)
      (restrictionAlong α) := by
  let _ : (𝟭 C).IsAlmostCocontinuous J J := by
    infer_instance
  simpa [restrictionAlong, ringSheafMap, ringedSiteStructureMap] using
    CategoryTheory.Functor.sheafOfModules_pushforward_exact_of_isAlmostCocontinuous
      (u := 𝟭 C)
      (JC := J)
      (JD := J)
      (𝒪C := ringSheaf J 𝒪)
      (𝒪D := ringSheaf J 𝒪')
      (φ := ringedSiteStructureMap α)

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- A sheaf of modules on a commutative ringed site is flat when tensoring on the right with it
is an exact endofunctor of `Mod(\mathcal O)`. -/
class IsFlat
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (Mod(𝒪))]
    (ℱ : Mod(𝒪)) : Prop where
  /-- Tensoring on the right by `ℱ` is exact on sheaves of `\mathcal O`-modules. -/
  exact_tensor :
    exactFunctor
      (Mod(𝒪))
      (Mod(𝒪))
      (CategoryTheory.MonoidalCategory.tensorRight ℱ)

/-- A morphism of sheaves of commutative rings is flat when the target, viewed by restriction of
scalars, is flat as a module over the source. -/
def IsFlatHom
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (α : 𝒪 ⟶ 𝒪') : Prop :=
  IsFlat 𝒪 ((restrictionAlong α).obj (unitModule J 𝒪'))

/-- Unfolding the flatness of a ring-map on a ringed site gives the flatness of the target unit
module after restriction of scalars. -/
theorem isFlatHom_iff
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (α : 𝒪 ⟶ 𝒪') :
    IsFlatHom α ↔ IsFlat 𝒪 ((restrictionAlong α).obj (unitModule J 𝒪')) := by
  rfl

end

end SheafOfModules.RingedSite

export SheafOfModules.RingedSite
  (ringSheaf ringSheafMap ringedSiteStructureMap restrictionAlong coextendAlong
    restrictionAlong_exact ringedSiteModuleCategory unitModule IsFlat IsFlatHom isFlatHom_iff)
