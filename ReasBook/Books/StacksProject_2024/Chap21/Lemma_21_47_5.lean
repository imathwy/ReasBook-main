import Mathlib
import StacksProject_2024.Chap21.Lemma_21_18_4
import StacksProject_2024.Chap21.Definition_21_47_1

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section PerfectObjects

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, ((J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- Restriction of modules to the localized ringed site over `U`. -/
private abbrev localizedPerfectRestriction (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    RingedSiteModules J 𝒪 ⥤ RingedSiteModules (J.over U) (𝒪.over U) :=
  SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝒪).over U))

end PerfectObjects

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [∀ U : C, ((JC.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}))]
variable [∀ U : D, ((JD.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}))]
variable [∀ U : C, HasWeakSheafify (JC.over U) AddCommGrpCat.{u}]
variable [∀ U : D, HasWeakSheafify (JD.over U) AddCommGrpCat.{u}]
variable [∀ U : C, ((JC.over U).WEqualsLocallyBijective AddCommGrpCat.{u})]
variable [∀ U : D, ((JD.over U).WEqualsLocallyBijective AddCommGrpCat.{u})]

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [∀ U : C, (localizedPerfectRestriction JC 𝒪' U).PreservesZeroMorphisms]
variable [∀ U : D, (localizedPerfectRestriction JD 𝒪 U).PreservesZeroMorphisms]

variable [CategoryWithHomology (RingedSiteModules JC 𝒪')]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪')]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪')]
variable [MonoidalCategory (RingedSiteModules JD 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪)]
variable [(pullbackFunctor F φ).Additive]

local notation "DModC" => DerivedCategory (RingedSiteModules JC 𝒪')

-- Proof sketch: choose a perfect representative complex for `E`. Pull that representative back
-- termwise along the morphism of ringed sites; strict perfectness is preserved under pullback, and
-- the induced morphism remains a quasi-isomorphism. The pulled-back representative therefore shows
-- that `Lf^* E` is perfect.
/-- Lemma 21.47.5: for the site-presented morphism of ringed sites determined by `F` and `φ`,
the derived pullback of a perfect object is again perfect. -/
theorem leftDerivedPullback_isPerfect
    (E : DModC) (hE : DerivedCategory.IsPerfect E) :
    DerivedCategory.IsPerfect ((leftDerivedPullback F φ).obj E) := sorry

end

end SheafOfModules.RingedSite
