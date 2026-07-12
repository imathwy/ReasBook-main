import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪')
variable (ℱ : SheafOfModules (ringSheaf JC 𝒪))

/-- The underlying `RingCat`-valued structure map attached to a morphism of sheaves of
commutative rings over a continuous functor of sites. -/
abbrev ringedSiteUnderlyingStructureMap :
    ringSheaf JC 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj (ringSheaf JD 𝒪') :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

-- Proof sketch: reduce to the site-presented case of the textbook proof. The inverse-image
-- module is computed by `SheafOfModules.pullback`; locally it is
-- `\mathcal O_{\mathcal C} \otimes_{f^{-1}\mathcal O_{\mathcal D}} f^{-1}\mathcal F`.
-- First show `f^{-1}\mathcal F` is flat over `f^{-1}\mathcal O_{\mathcal D}` by the local
-- factorization criterion for flatness, then apply the flat base-change statement for extension of
-- scalars along `f^{-1}\mathcal O_{\mathcal D} \to \mathcal O_{\mathcal C}`.
/-- Lemma 18.39.1: in the site-presented formalization of a morphism of ringed topoi or ringed
sites, the pullback `f^*\mathcal F` of a flat `\mathcal O_{\mathcal D}`-module `\mathcal F` is a
flat `\mathcal O_{\mathcal C}`-module. Here `f^*\mathcal F` is the canonical module pullback
`(SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj ℱ`. -/
@[stacks 05VD]
theorem pullback_isFlat_of_isFlat
    [MonoidalCategory (ringedSiteModuleCategory JC 𝒪)]
    [MonoidalCategory (ringedSiteModuleCategory JD 𝒪')]
    [IsFlat 𝒪 ℱ] :
    IsFlat 𝒪'
      ((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj ℱ) := by
  -- Proof comment: first test whether the existing pullback and flatness owners already expose
  -- this preservation result directly through typeclass inference.
  infer_instance

end
