import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_25_2
import StacksProject_2024.stacks_project.Chap07.Remark_7_25_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [J.Subcanonical] (U : C)
variable (G : Sheaf (J.over U) (Type (max u v)))

/- Domain-style sampling for Lemma 7.27.1:
- primary domain: localization lower shriek on sheaves and its presheaf-level left-Kan-extension
  formula;
- sampled owner API:
  `(Over.forget U).sheafPullback`,
  `localization_lowerShriek_associatedSheafIso`,
  `localization_leftKanExtension_objIsoSigma`,
  `sheafificationIso`;
- source-facing layer: the Stacks Project identification of `j_{U!}(G)` with the presheaf
  `V ↦ ∐_{φ : V ⟶ U} G(V \xrightarrow{φ} U)`;
- core/canonical owner: the sheaf functor `(Over.forget U).sheafPullback (Type (max u v))
  (J.over U) J` and the presheaf functor `(Over.forget U).op.lan`;
- bridge/view: `localization_lowerShriek_associatedSheafIso` identifies `j_{U!}` with the
  sheafification of the left Kan extension, and subcanonicality upgrades that sheafification to the
  presheaf itself.

Primitive data are the site `J`, the localization object `U`, the sheaf `G`, and the standard
sheafification/Kan-extension hypotheses. The sheafified left Kan extension is derived API of the
canonical owners, so no separate wrapper sheaf is kept in the public surface.
-/

private theorem localization_leftKanExtension_isSheaf :
    Presheaf.IsSheaf J ((Over.forget U).op.lan.obj G.obj) := sorry

/-- Lemma 7.27.1: if `J` is subcanonical and `G` is a sheaf on `C/U`, then the underlying
presheaf of `j_{U!}(G)` is canonically isomorphic to the left Kan extension of `G` along
`(Over.forget U).op`. -/
noncomputable def localization_lowerShriek_iso_leftKanExtension :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj ≅
      (Over.forget U).op.lan.obj G.obj :=
  letI : HasWeakSheafify J (Type (max u v)) := inferInstance
  (sheafToPresheaf J (Type (max u v))).mapIso <|
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).mapIso
        (sheafificationIso G)) ≪≫
      localization_lowerShriek_associatedSheafIso J U G.obj ≪≫
        (sheafificationIso
          ⟨(Over.forget U).op.lan.obj G.obj, localization_leftKanExtension_isSheaf J U G⟩).symm

/-- Objectwise `Type`-valued form of Lemma 7.27.1. -/
noncomputable def localization_lowerShriek_objIsoSigma (V : C) :
    ((((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj.obj (op V)) ≅
      Σ φ : V ⟶ U, G.obj.obj (op (Over.mk φ)) :=
  (localization_lowerShriek_iso_leftKanExtension J U G).app (op V) ≪≫
    localization_leftKanExtension_objIsoSigma U G.obj V

-- Proof sketch: unfold `localization_lowerShriek_objIsoSigma`; it is defined by evaluating the main
-- isomorphism of Lemma 7.27.1 at `V` and composing with the standard sigma-description of the left
-- Kan extension.
/-- The objectwise sigma-description is obtained by evaluating the canonical isomorphism of
Lemma 7.27.1 and then applying the standard left-Kan-extension formula. -/
theorem localization_lowerShriek_objIsoSigma_def (V : C) :
    localization_lowerShriek_objIsoSigma J U G V =
      (localization_lowerShriek_iso_leftKanExtension J U G).app (op V) ≪≫
        localization_leftKanExtension_objIsoSigma U G.obj V := sorry

end
