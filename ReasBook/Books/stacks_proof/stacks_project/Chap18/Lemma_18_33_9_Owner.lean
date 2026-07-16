import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {O₂ A : Sheaf J CommRingCat.{u}} (π : A ⟶ O₂)

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

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

/-- The intrinsic kernel ideal of `π` has square zero when products of local kernel sections vanish
in `A`. -/
abbrev KernelSquareZero (π : A ⟶ O₂) : Prop :=
  ∀ U : Cᵒᵖ, ∀ x y : (kernelIdealSheaf π).val.obj U,
    (show A.obj.obj U from (kernelIdealSheafInclusion π).val.app U x) *
      (show A.obj.obj U from (kernelIdealSheafInclusion π).val.app U y) = 0

/-- The kernel ideal sheaf of `π`, viewed as an `O₂`-module by restricting scalars along a fixed
section `s : O₂ ⟶ A`. -/
abbrev kernelIdealSheafModule
    (π : A ⟶ O₂) (s : O₂ ⟶ A) :
    SheafOfModules (ringSheaf J O₂) :=
  (restrictionAlong s).obj (kernelIdealSheaf π)

end
