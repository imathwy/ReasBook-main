import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap24.Definition_24_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪X : Sheaf JC CommRingCat.{max u v}} {𝒪Y : Sheaf JD CommRingCat.{max u v}}

private abbrev commRingSheafSite
    {E : Type u} [Category.{v} E] (J : GrothendieckTopology E)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) : RingedSite.{u, v} :=
  RingedSite.ofCommRingSheaf J 𝒪

variable (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y)

private instance
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y) :
    f.base.IsContinuous JD JC := by
  exact f.isMorphismOfSites.toIsContinuous

private instance
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y) :
    f.base.IsContinuous
      (commRingSheafSite JD 𝒪Y).siteTopology
      (commRingSheafSite JC 𝒪X).siteTopology :=
  f.isMorphismOfSites.toIsContinuous

local notation "ModX" => ringedSiteModuleCategory JC 𝒪X
local notation "ModY" => ringedSiteModuleCategory JD 𝒪Y
local notation "GModX" => GradedObject ℤ ModX
local notation "GModY" => GradedObject ℤ ModY

private abbrev modulePushforward
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y) : ModX ⥤ ModY :=
  SheafOfModules.pushforward f.structureSheafMap

private abbrev modulePullback
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y)
    [hPresheafPushforward :
      (PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint] :
    ModY ⥤ ModX :=
  let _ : (SheafOfModules.pushforward.{max u v} f.structureSheafMap).IsRightAdjoint :=
    RingedSite.Hom.structureSheafMap_pushforward_isRightAdjoint f
  (SheafOfModules.pullback f.structureSheafMap : ModY ⥤ ModX)

private noncomputable abbrev moduleHomEquiv
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y)
    [hPresheafPushforward :
      (PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
    (ℬ : ringedSiteModuleCategory JD 𝒪Y) (𝒜 : ringedSiteModuleCategory JC 𝒪X) :
    (ℬ ⟶ (modulePushforward f).obj 𝒜) ≃
      ((modulePullback f).obj ℬ ⟶ 𝒜) :=
  let _ : (SheafOfModules.pushforward.{max u v} f.structureSheafMap).IsRightAdjoint :=
    RingedSite.Hom.structureSheafMap_pushforward_isRightAdjoint f
  ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv ℬ 𝒜).symm

private abbrev gradedPushforwardHom
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y)
    (ℬ : GradedObject ℤ (ringedSiteModuleCategory JD 𝒪Y))
    (𝒜 : GradedObject ℤ (ringedSiteModuleCategory JC 𝒪X)) :=
  ∀ n : ℤ, ℬ n ⟶ (modulePushforward f).obj (𝒜 n)

private abbrev gradedPullbackHom
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y)
    [hPresheafPushforward :
      (PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
    (ℬ : GradedObject ℤ (ringedSiteModuleCategory JD 𝒪Y))
    (𝒜 : GradedObject ℤ (ringedSiteModuleCategory JC 𝒪X)) :=
  ∀ n : ℤ, (modulePullback f).obj (ℬ n) ⟶ 𝒜 n

/-- The direct image of a graded module sheaf is obtained degreewise from module pushforward. -/
abbrev gradedPushforward
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y) : GModX ⥤ GModY where
  obj 𝒜 n := (modulePushforward f).obj (𝒜 n)
  map g n := (modulePushforward f).map (g n)
  map_id := by
    intro 𝒜
    ext n U x
    simpa using
      congrArg (fun α ↦ (ModuleCat.Hom.hom (α.val.app U)) x)
        ((modulePushforward f).map_id (𝒜 n))
  map_comp := by
    intro 𝒜 ℬ 𝒞 g h
    ext n U x
    simpa using
      congrArg (fun α ↦ (ModuleCat.Hom.hom (α.val.app U)) x)
        ((modulePushforward f).map_comp (g n) (h n))

/-- In degree `n`, the graded direct image is the module pushforward of the degree-`n` piece. -/
@[simp] theorem gradedPushforward_obj_apply (𝒜 : GModX) (n : ℤ) :
    ((gradedPushforward f).obj 𝒜) n = (modulePushforward f).obj (𝒜 n) :=
  rfl

section

variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [hPresheafPushforward :
  (PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]

/- The inverse image of a graded module sheaf is obtained degreewise from module pullback. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
abbrev gradedPullback
    (f : commRingSheafSite JC 𝒪X ⟶ commRingSheafSite JD 𝒪Y)
    [hPresheafPushforward :
      (PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint] :
    GModY ⥤ GModX where
  obj ℬ n := (modulePullback f).obj (ℬ n)
  map g n := (modulePullback f).map (g n)
  map_id := by
    intro ℬ
    ext n U x
    simpa using
      congrArg (fun α ↦ (ModuleCat.Hom.hom (α.val.app U)) x)
        ((modulePullback f).map_id (ℬ n))
  map_comp := by
    intro ℬ₁ ℬ₂ ℬ₃ g h
    ext n U x
    simpa using
      congrArg (fun α ↦ (ModuleCat.Hom.hom (α.val.app U)) x)
        ((modulePullback f).map_comp (g n) (h n))

/- Source/core/bridge triage for Lemma 24.9.1:
- `source-facing`: the graded pullback/pushforward Hom-set bijection
  `Hom(\mathcal B, f_* \mathcal A) ≃ Hom(f^* \mathcal B, \mathcal A)`;
- `core/canonical`: the degreewise module-sheaf adjunction
  `SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap`;
- `bridge/view`: the clean degreewise forward/inverse maps and their evaluation lemmas.

This file therefore keeps the Stacks-oriented graded bijection as the main public declaration and
builds its forward and inverse maps directly from the canonical module-level adjunction. -/

/- Lemma 24.9.1: the degreewise map underlying the graded pullback/pushforward Hom-set
bijection `Hom(\mathcal B, f_* \mathcal A) ≃ Hom(f^* \mathcal B, \mathcal A)`. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
noncomputable def gradedPushforwardPullbackHom
    (ℬ : GradedObject ℤ ModY) (𝒜 : GradedObject ℤ ModX) :
    (ℬ ⟶ (gradedPushforward f).obj 𝒜) →
      ((gradedPullback f).obj ℬ ⟶ 𝒜) :=
  fun g n ↦ moduleHomEquiv f (ℬ n) (𝒜 n) (g n)

/- The inverse map underlying Lemma 24.9.1, in the source orientation
`Hom(f^* \mathcal B, \mathcal A) → Hom(\mathcal B, f_* \mathcal A)`. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
noncomputable def gradedPullbackPushforwardHom
    (ℬ : GradedObject ℤ ModY) (𝒜 : GradedObject ℤ ModX) :
    ((gradedPullback f).obj ℬ ⟶ 𝒜) →
      (ℬ ⟶ (gradedPushforward f).obj 𝒜) :=
  fun g n ↦ (moduleHomEquiv f (ℬ n) (𝒜 n)).symm (g n)

/- In degree `n`, the graded inverse image is the module pullback of the degree-`n` piece. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
@[simp] theorem gradedPullback_obj_apply (ℬ : GModY) (n : ℤ) :
    ((gradedPullback f).obj ℬ) n = (modulePullback f).obj (ℬ n) :=
  rfl

/- Applying `gradedPushforwardPullbackHom` in degree `n` is the inverse of the usual
pullback/pushforward adjunction on the degree-`n` module sheaves. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
@[simp] theorem gradedPushforwardPullbackHom_apply_apply
    (ℬ : GradedObject ℤ ModY) (𝒜 : GradedObject ℤ ModX)
    (g : ℬ ⟶ (gradedPushforward f).obj 𝒜) (n : ℤ) :
    (gradedPushforwardPullbackHom f ℬ 𝒜 g) n =
      moduleHomEquiv f (ℬ n) (𝒜 n) (g n) :=
  rfl

/- Applying `gradedPullbackPushforwardHom` in degree `n` is the usual
pullback/pushforward adjunction on the degree-`n` module sheaves. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
@[simp] theorem gradedPullbackPushforwardHom_apply_apply
    (ℬ : GradedObject ℤ ModY) (𝒜 : GradedObject ℤ ModX)
    (g : (gradedPullback f).obj ℬ ⟶ 𝒜) (n : ℤ) :
    (gradedPullbackPushforwardHom f ℬ 𝒜 g) n =
      (moduleHomEquiv f (ℬ n) (𝒜 n)).symm (g n) :=
  rfl

/- Lemma 24.9.1: `gradedPullbackPushforwardHom` is a left inverse to
`gradedPushforwardPullbackHom`. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
theorem gradedPullbackPushforwardHom_leftInverse
    (ℬ : GradedObject ℤ ModY) (𝒜 : GradedObject ℤ ModX) :
    Function.LeftInverse (gradedPullbackPushforwardHom f ℬ 𝒜)
      (gradedPushforwardPullbackHom f ℬ 𝒜) := by
  intro g
  ext n
  exact (moduleHomEquiv f (ℬ n) (𝒜 n)).left_inv (g n)

/- Lemma 24.9.1: `gradedPushforwardPullbackHom` is a right inverse to
`gradedPullbackPushforwardHom`. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
theorem gradedPushforwardPullbackHom_rightInverse
    (ℬ : GradedObject ℤ ModY) (𝒜 : GradedObject ℤ ModX) :
    Function.RightInverse (gradedPushforwardPullbackHom f ℬ 𝒜)
      (gradedPullbackPushforwardHom f ℬ 𝒜) := by
  intro g
  ext n
  exact (moduleHomEquiv f (ℬ n) (𝒜 n)).right_inv (g n)

/- Lemma 24.9.1: the graded pullback/pushforward Hom-set map is bijective. -/
omit [HasWeakSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
@[stacks 0FR8] theorem gradedPushforwardPullbackHom_bijective
    (ℬ : GradedObject ℤ ModY) (𝒜 : GradedObject ℤ ModX) :
    Function.Bijective (gradedPushforwardPullbackHom f ℬ 𝒜) := by
  refine ⟨?_, ?_⟩
  · exact (gradedPullbackPushforwardHom_leftInverse (f := f) ℬ 𝒜).injective
  · exact (gradedPushforwardPullbackHom_rightInverse (f := f) ℬ 𝒜).surjective

end

end

end RingedSite.Hom
