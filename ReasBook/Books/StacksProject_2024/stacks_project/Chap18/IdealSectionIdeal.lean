import Mathlib
import StacksProject_2024.Chap18.RingedSiteModuleCategory

open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- The ideal of sections over `U` cut out by an ideal sheaf
`I : \operatorname{Sub}(\mathcal O)`. -/
noncomputable def idealSectionIdeal
    (I : Subobject (unitModule J 𝒪))
    (U : Cᵒᵖ) : Ideal (𝒪.obj.obj U) :=
  Ideal.span <| Set.range fun s : (I : Mod(𝒪)).val.obj U ↦
    (Hom.val I.arrow).app U s

end SheafOfModules.RingedSite
