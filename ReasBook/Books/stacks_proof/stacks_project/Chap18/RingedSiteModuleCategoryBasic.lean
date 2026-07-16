import stacks_proof.stacks_project.Chap18.Definition_18_6_1

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/- Basic owners for sheaves of modules on a commutative ringed site. -/

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on a ringed
site. -/
abbrev ringedSiteModuleCategory {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- A sheaf of commutative rings viewed as a sheaf with values in `RingCat`. -/
abbrev ringSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The underlying `RingCat`-valued morphism of a morphism of sheaves of commutative rings. -/
abbrev ringSheafMap {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    ringSheaf J 𝒪 ⟶ ringSheaf J 𝒪' :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map α

/-- The same-site structure map written in identity-pushforward form. -/
abbrev ringedSiteStructureMap {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    ringSheaf J 𝒪 ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj (ringSheaf J 𝒪') :=
  ringSheafMap α ≫
    (Functor.sheafPushforwardContinuousId RingCat.{max u v} J).inv.app (ringSheaf J 𝒪')

/-- Same-site restriction of scalars along a morphism of sheaves of commutative rings. -/
abbrev restrictionAlong {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    ringedSiteModuleCategory J 𝒪' ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.restrictScalars (ringSheafMap α)

/-- The structure sheaf viewed as the unit `\mathcal O`-module in `\mathrm{Mod}(\mathcal O)`. -/
abbrev unitModule {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.unit (ringSheaf J 𝒪)

end SheafOfModules.RingedSite

