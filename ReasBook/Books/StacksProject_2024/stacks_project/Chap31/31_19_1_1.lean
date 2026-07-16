import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Lemma_18_33_9_Owner
import StacksProject_2024.stacks_project.Chap18.IdealQuotientSheaf

open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable (I : Subobject (unitModule J 𝒪))
variable (n : ℕ)

private noncomputable def idealPowerQuotientCommRingPresheafTransition :
    idealPowerQuotientCommRingPresheaf I (n + 1) ⟶
      idealPowerQuotientCommRingPresheaf I n where
  app U :=
    CommRingCat.ofHom
      (Ideal.Quotient.factorₐ (𝒪.obj.obj U)
        (Ideal.pow_le_pow_right (Nat.le_succ n))).toRingHom
  naturality := by
    intro U V f
    ext x
    refine Quotient.inductionOn x ?_
    intro x
    rfl

private noncomputable def idealPowerQuotientCommRingSheafTransition :
    idealPowerQuotientCommRingSheaf I (n + 1) ⟶
      idealPowerQuotientCommRingSheaf I n :=
  ⟨CategoryTheory.sheafifyLift J
      (idealPowerQuotientCommRingPresheafTransition I n)
      (idealPowerQuotientCommRingSheaf I n).property⟩

/- 31.19.1.1: the pushforward degree-`n` piece `i_* \mathcal C_{Z/X,n}` of the normal cone of an
immersion with ideal sheaf `\mathcal I` is the kernel of the canonical transition
`\mathcal O / \mathcal I^{n + 1} \to \mathcal O / \mathcal I^n`. -/
abbrev normalConeDegreePiece :
    SheafOfModules
      (ringSheaf J (idealPowerQuotientCommRingSheaf I (n + 1))) :=
  kernelIdealSheaf (idealPowerQuotientCommRingSheafTransition I n)

/-- The degree-`n` piece of the normal cone is exactly the intrinsic kernel ideal sheaf of the
one-step ideal-power quotient transition. -/
abbrev normalConeDegreePiece_eq_kernelIdealSheaf :
    normalConeDegreePiece I n =
      kernelIdealSheaf (idealPowerQuotientCommRingSheafTransition I n) :=
  rfl

/- Companion recall: the ambient owner for this source-facing kernel description is the intrinsic
kernel ideal sheaf of a morphism of commutative-ring sheaves. -/
recall kernelIdealSheaf

end SheafOfModules.RingedSite
