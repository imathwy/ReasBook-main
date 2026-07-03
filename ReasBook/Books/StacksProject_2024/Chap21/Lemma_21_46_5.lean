import Mathlib
import StacksProject_2024.Chap21.Definition_21_46_1
import StacksProject_2024.Chap21.Lemma_21_18_4

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪C : Sheaf JC CommRingCat.{u}} {𝒪D : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

variable [Abelian (RingedSiteModules JC 𝒪C)]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪C)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪C)]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪C)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules JC 𝒪C))]

variable [Abelian (RingedSiteModules JD 𝒪D)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪D)]
variable [MonoidalCategory (RingedSiteModules JD 𝒪D)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪D)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules JD 𝒪D))]

variable [(pullbackFunctor F φ).Additive]

-- Proof sketch: represent `E` by a flat complex concentrated in degrees `[a, b]` using
-- Lemma `21.46.3`, pull that complex back termwise along `F`, and use Lemma `18.39.1` to keep
-- the terms flat after pullback. The pulled-back complex is still concentrated in `[a, b]`, so
-- Lemma `21.46.3` again identifies `Lf^*E` as having tor-amplitude in `[a, b]`.
/-- Lemma 21.46.5: for the site-presented morphism of ringed sites determined by `F` and `φ`, if
`E` has tor-amplitude in `[a, b]`, then its derived pullback `Lf^*E` also has tor-amplitude in
`[a, b]`. -/
theorem leftDerivedPullback_hasTorAmplitudeIn
    (E : DerivedCategory (RingedSiteModules JC 𝒪C)) (a b : ℤ) (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeIn ((leftDerivedPullback F φ).obj E) a b := sorry

end

end SheafOfModules.RingedSite
