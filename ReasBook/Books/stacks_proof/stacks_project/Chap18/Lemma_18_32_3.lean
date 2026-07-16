import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_43_3
import stacks_proof.stacks_project.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
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

local notation "ModC" => ringedSiteModuleCategory JC 𝒪C
local notation "ModD" => ringedSiteModuleCategory JD 𝒪D
local notation "fStar" => SheafOfModules.pullback φ

/-- Lemma 18.32.3: for a site-presentation of a morphism of ringed topoi, the pullback of an
invertible `\mathcal O_\mathcal D`-module is invertible. -/
@[stacks 0B8P]
theorem pullback_isInvertible
    (ℒ : ModD)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Functor.IsEquivalence (tensorRight ((fStar).obj ℒ : ModC)) := by
  let _ : (fStar).Monoidal := inferInstance
  rcases (tensorRight_isEquivalence_iff_exists_tensor_inverse ℒ).1 inferInstance with
    ⟨N, ⟨⟨eLeft⟩, ⟨eRight⟩⟩⟩
  -- Route correction: use the pullback functor's existing monoidal owner API, rather than a
  -- separate Chapter 18 invertibility wrapper, to transport a chosen tensor inverse of `ℒ`.
  have hLeft :
      (((fStar).obj ℒ : ModC) ⊗ (fStar).obj N) ≅ (𝟙_ ModC) := by
    -- Proof comment: pullback carries the left trivialization `ℒ ⊗ N ≅ 𝟙` to the target tensor
    -- unit after rebracketing with the monoidal comparison isomorphisms.
    exact
      (Functor.Monoidal.μIso (fStar) ℒ N) ≪≫
        (fStar).mapIso eLeft ≪≫
        (Functor.Monoidal.εIso (fStar)).symm
  have hRight :
      (((fStar).obj N : ModC) ⊗ (fStar).obj ℒ) ≅ (𝟙_ ModC) := by
    -- Proof comment: the same monoidal transport sends the right trivialization `N ⊗ ℒ ≅ 𝟙`
    -- to a right tensor inverse for the pulled-back module.
    exact
      (Functor.Monoidal.μIso (fStar) N ℒ) ≪≫
        (fStar).mapIso eRight ≪≫
        (Functor.Monoidal.εIso (fStar)).symm
  -- Proof comment: the pulled-back witness `f^*N` now satisfies the two-sided tensor-inverse
  -- criterion, so the pullback of `ℒ` is invertible.
  exact
    (tensorRight_isEquivalence_iff_exists_tensor_inverse (((fStar).obj ℒ : ModC))).2
      ⟨(fStar).obj N, ⟨⟨hLeft⟩, ⟨hRight⟩⟩⟩

instance instPullbackIsInvertible
    (ℒ : ModD)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Functor.IsEquivalence (tensorRight ((fStar).obj ℒ : ModC)) :=
  pullback_isInvertible (F := F) (φ := φ) ℒ

end SheafOfModules.RingedSite
