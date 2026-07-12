import Mathlib
import StacksProject_2024.Chap07.Lemma_7_28_1
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite SheafOfModules

noncomputable section

universe u

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for 18.41.2.1:
- primary domain: representable localization of ringed sites and the comparison between the
  localized lower shriek on abelian sheaves and the localized inverse-image structure sheaf;
- sampled owner declarations:
  `ringSheaf` from `Definition_18_28_1`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `Functor.sheafAdjunctionContinuous`,
  `SheafOfModules.overPushforwardOverAdj`;
- best owner abstraction: the source-facing comparison should be expressed as the transpose under
  `sheafAdjunctionContinuous`, while the underlying localized structure sheaf remains the abelian
  sheaf underlying the canonical unit module on `((ringSheaf J 𝒪).over U)`;
- primitive data: the canonical localized unit module and its right-adjoint comparison map;
- derived API: the left-adjoint transpose `compare_on_localizations` and the adjunction recovery
  lemma below.

Source/core/bridge triage:
- `source-facing`: `compare_on_localizations`;
- `core/canonical`: `Functor.sheafAdjunctionContinuous`;
- `bridge/view`: `compareOnLocalizationsRightAdjointMap`. -/

/-- The localized structure sheaf `\mathcal O_U`, regarded only as its underlying abelian sheaf on
`C/U`. -/
abbrev localizedStructureAbelianSheaf
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    Sheaf (J.over U) AddCommGrpCat.{u} :=
  (toSheaf ((ringSheaf J 𝒪).over U)).obj (unitModule (J.over U) (𝒪.over U))

namespace LocalizedStructureAbelianSheaf

/- Textbook notation for the localized structure sheaf `\mathcal O_U`, viewed here as an abelian
sheaf on the slice site. The ambient topology is inferred from the sheaf `𝒪`. -/
scoped notation:max 𝒪:max "_[" U "]" =>
  CategoryTheory.localizedStructureAbelianSheaf _ 𝒪 U

end LocalizedStructureAbelianSheaf

open scoped LocalizedStructureAbelianSheaf

variable (f : C ⥤ D) [f.IsContinuous JC JD]
variable (𝒪D : Sheaf JD CommRingCat.{u}) (U : C)

private abbrev overPullbackPushforwardIso :
    JD.overPullback RingCat.{u} (f.obj U) ⋙
        (Over.post f).sheafPushforwardContinuous RingCat.{u}
          (JC.over U) (JD.over (f.obj U)) ≅
      f.sheafPushforwardContinuous RingCat.{u} JC JD ⋙
        JC.overPullback RingCat.{u} U :=
  (Over.post f).sheafPushforwardContinuousComp (Over.forget (f.obj U))
      RingCat.{u} (JC.over U) (JD.over (f.obj U)) JD ≪≫
    eqToIso (by rfl) ≪≫
    ((Over.forget U).sheafPushforwardContinuousComp f
      RingCat.{u} (JC.over U) JC JD).symm

/-- The right-adjoint form of the comparison on localized structure sheaves:
`\mathcal O_U \to (g')^{-1}\mathcal O_{f(U)}`. -/
private abbrev compareOnLocalizationsRightAdjointMap_hom :
    SheafOfModules.unit
        ((ringSheaf JC ((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)).over U) ⟶
      (SheafOfModules.pushforward
          (((overPullbackPushforwardIso f U).symm.app (ringSheaf JD 𝒪D)).hom)).obj
        (SheafOfModules.unit ((ringSheaf JD 𝒪D).over (f.obj U))) :=
  unitToPushforwardObjUnit
    (((overPullbackPushforwardIso f U).symm.app (ringSheaf JD 𝒪D)).hom)

/-- The right-adjoint form of the comparison on localized structure sheaves:
`\mathcal O_U \to (g')^{-1}\mathcal O_{f(U)}`. -/
abbrev compareOnLocalizationsRightAdjointMap :
    ((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U] ⟶
      ((Over.post f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (JC.over U) (JD.over (f.obj U))).obj
        ((𝒪D)_[f.obj U]) :=
  (toSheaf ((ringSheaf JC ((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)).over U)).map
    (compareOnLocalizationsRightAdjointMap_hom f 𝒪D U)

variable [HasWeakSheafify (JD.over (f.obj U)) AddCommGrpCat.{u}]
variable [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.post f).op.HasLeftKanExtension F]

/-- 18.41.2.1: the canonical comparison morphism
`(g')^{Ab}_! \mathcal{O}_U \to \mathcal{O}_{f(U)}` on the localized sites, where `g'` is the
morphism induced by `Over.post f : C/U ⥤ D/f(U)` and `\mathcal O_U` is the localized inverse-image
structure sheaf on `C/U`, viewed as an abelian sheaf. -/
abbrev compare_on_localizations :
    ((Over.post f).sheafPullback AddCommGrpCat.{u}
        (JC.over U) (JD.over (f.obj U))).obj
      (((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
    (𝒪D)_[f.obj U] :=
  (((Over.post f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (JC.over U) (JD.over (f.obj U))).homEquiv _ _).symm
    (compareOnLocalizationsRightAdjointMap f 𝒪D U)

-- Proof sketch: `compare_on_localizations` was defined as the transpose of
-- `compareOnLocalizationsRightAdjointMap` under the adjunction
-- `(Over.post f).sheafPullback ⊣ (Over.post f).sheafPushforwardContinuous`, so applying the
-- adjunction hom-set equivalence recovers the right-adjoint comparison map.
/-- Applying the slice-site lower-shriek adjunction to `compare_on_localizations` recovers the
canonical map `\mathcal O_U \to (g')^{-1}\mathcal O_{f(U)}`. -/
theorem compare_on_localizations_homEquiv :
    ((Over.post f).sheafAdjunctionContinuous AddCommGrpCat.{u}
        (JC.over U) (JD.over (f.obj U))).homEquiv _ _
      (compare_on_localizations f 𝒪D U) =
    compareOnLocalizationsRightAdjointMap f 𝒪D U := by
  simpa [compare_on_localizations] using
    (Equiv.apply_symm_apply
      (((Over.post f).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (JC.over U) (JD.over (f.obj U))).homEquiv _ _)
      (compareOnLocalizationsRightAdjointMap f 𝒪D U))

attribute [simp] compare_on_localizations_homEquiv

end

end CategoryTheory
