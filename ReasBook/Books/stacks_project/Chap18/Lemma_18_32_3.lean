import Mathlib
import stacks_project.Chap18.Lemma_18_19_2
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {E : Type u} [Category.{u} E] {J : GrothendieckTopology E}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {C : Type u} [SmallCategory C]
variable {D : Type u} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : D ⥤ C)
variable [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪C : Sheaf JC CommRingCat.{u}} {𝒪D : Sheaf JD CommRingCat.{u}}
variable
  (φ :
    ringSheaf JD 𝒪D ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JD JC).obj
        (ringSheaf JC 𝒪C))
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]
variable [MonoidalCategory (ringedSiteModuleCategory JC 𝒪C)]
variable [MonoidalCategory (ringedSiteModuleCategory JD 𝒪D)]

-- Proof sketch: choose a tensor inverse of `ℒ` using Lemma `18.32.2`, pull back the tensor
-- trivialization, use the tensor-pullback comparison from Lemma `18.26.2` together with the
-- canonical identification of pullback of the structure module, and apply Lemma `18.32.2` again
-- on the source ringed site.
/-- Lemma 18.32.3: for a site-presentation of a morphism of ringed topoi, the pullback of an
invertible `\mathcal O_\mathcal D`-module is invertible. -/
theorem pullback_isInvertible
    (ℒ : ringedSiteModuleCategory JD 𝒪D)
    [@IsInvertible _ _ JD 𝒪D _ _ ℒ] :
    @IsInvertible _ _ JC 𝒪C _ _
      (((SheafOfModules.pullback φ).obj ℒ) : ringedSiteModuleCategory JC 𝒪C) := sorry

end SheafOfModules.RingedSite
