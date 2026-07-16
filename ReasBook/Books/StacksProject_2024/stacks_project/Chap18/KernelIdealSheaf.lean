import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O₂ A : Sheaf J CommRingCat.{max u v}} (π : A ⟶ O₂)

private abbrev structureSheafQuotient (π : A ⟶ O₂) :
    SheafOfModules.unit (ringSheaf J A) ⟶
      (SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
        (SheafOfModules.unit (ringSheaf J O₂)) :=
  SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap π)

/-- The intrinsic kernel ideal sheaf of `π`, viewed as an `A`-module sheaf. -/
abbrev kernelIdealSheaf (π : A ⟶ O₂) : SheafOfModules (ringSheaf J A) :=
  kernel (structureSheafQuotient π)

/-- The intrinsic kernel ideal sheaf includes canonically into the unit `A`-module. -/
abbrev kernelIdealSheafInclusion (π : A ⟶ O₂) :
    kernelIdealSheaf π ⟶ unitModule J A :=
  kernel.ι (structureSheafQuotient π)

end
