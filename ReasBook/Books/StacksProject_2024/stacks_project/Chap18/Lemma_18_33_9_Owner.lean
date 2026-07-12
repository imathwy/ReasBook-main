import StacksProject_2024.Chap18.KernelIdealSheaf

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

/-- The restricted kernel row
`0 ⟶ kernelIdealSheafModule π s ⟶ A|_O₂ ⟶ O₂`
obtained by restricting scalars along a section `s : O₂ ⟶ A`. -/
abbrev kernelIdealSheafModuleShortComplex
    (π : A ⟶ O₂) (s : O₂ ⟶ A) :
    ShortComplex (ringedSiteModuleCategory J O₂) :=
  (ShortComplex.kernelSequence (structureSheafQuotient π)).map (restrictionAlong s)

/-- If `s` is a section of `π`, then the rightmost term of the restricted kernel row is canonically
the unit `O₂`-module. -/
private abbrev kernelIdealSheafModuleShortComplexRightIso
    (s : O₂ ⟶ A) (hs : s ≫ π = 𝟙 O₂) :
    (kernelIdealSheafModuleShortComplex π s).X₃ ≅ unitModule J O₂ :=
  eqToIso (by
    change (restrictionAlong (s ≫ π)).obj (unitModule J O₂) = unitModule J O₂
    simpa [restrictionAlong, unitModule] using
      congrArg (fun α ↦ (restrictionAlong α).obj (unitModule J O₂)) hs)

/-- The chosen section `s` induces the canonical section of the right-hand map in the restricted
kernel row. -/
abbrev kernelIdealSheafModuleShortComplexSection
    (s : O₂ ⟶ A) (hs : s ≫ π = 𝟙 O₂) :
    (kernelIdealSheafModuleShortComplex π s).X₃ ⟶ (kernelIdealSheafModuleShortComplex π s).X₂ :=
  (kernelIdealSheafModuleShortComplexRightIso π s hs).hom ≫
    SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap s)

/-- If `s` is a section of `π`, then it is a section of the right-hand map in the restricted
kernel row. -/
theorem kernelIdealSheafModuleShortComplexSection_comp_g
    (s : O₂ ⟶ A) (hs : s ≫ π = 𝟙 O₂) :
    kernelIdealSheafModuleShortComplexSection π s hs ≫
      (kernelIdealSheafModuleShortComplex π s).g = 𝟙 _ := by
  sorry

/-- If `s` is a section of `π`, then the restricted kernel row is short exact. -/
theorem kernelIdealSheafModuleShortComplex_shortExact
    (s : O₂ ⟶ A) (hs : s ≫ π = 𝟙 O₂) :
    (kernelIdealSheafModuleShortComplex π s).ShortExact := by
  sorry

end
