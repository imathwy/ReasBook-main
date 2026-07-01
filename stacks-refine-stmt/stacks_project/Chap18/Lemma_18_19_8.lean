import Mathlib
import stacks_project.Chap07.Lemma_7_27_4

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 18.19.8:
- primary domain: unit and counit isomorphisms for the localization adjunctions on abelian sheaves
  over the slice site `C/U`;
- sampled owner declarations:
  `overForget_full_of_subsingletonHom`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`,
  `counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful`;
- best owner abstraction: the adjunction owners
  `(Over.forget U).sheafAdjunctionContinuous AddCommGrpCat (J.over U) J` and
  `(Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat (J.over U) J`;
- primitive data: the site `J`, the object `U`, and the source hypothesis
  `hU : ∀ X, Subsingleton (X ⟶ U)`;
- derived API: the `IsIso` facts for the unit and counit components of those owners.

Source/core/bridge triage:
- `source-facing`: the two source statements for abelian sheaves on `C/U`;
- `core/canonical`: the unit and counit morphisms of the localization adjunction owners;
- `bridge/view`: the fullness of `Over.forget U` supplied by
  `overForget_full_of_subsingletonHom`.

This file should therefore keep the two specialized source-facing theorem names, but derive them
directly from the canonical owner instances instead of carrying parallel local proof data.
-/

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (U : C)

-- Proof sketch: the hypothesis implies that `Over.forget U` is fully faithful, so Lemma 18.16.4
-- applies to the adjunction `j_{U!} ⊣ j_U⁻¹` coming from the canonical pullback functor on abelian
-- sheaves.
/-- Lemma 18.19.8 (1): if every object of `C` has at most one morphism to `U`, then for every
abelian sheaf `ℱ` on the localized site `C/U` the canonical map
`ℱ ⟶ j_U⁻¹(j_{U!} ℱ)` is an isomorphism. -/
theorem localization_lowerShriek_unit_app_isIso_of_subsingletonHom
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v}, (Over.forget U).op.HasLeftKanExtension F]
    (ℱ : Sheaf (J.over U) AddCommGrpCat.{max u v}) :
    IsIso (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{max u v} (J.over U) J).unit.app
      ℱ) := by
  refine (fun hU ↦ ?_) hU
  letI : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  infer_instance

-- Proof sketch: the same full-faithfulness input reduces the statement to Lemma 18.16.4 for the
-- adjunction `j_U⁻¹ ⊣ j_{U*}`, where `j_{U*}` is the cocontinuous pushforward on abelian sheaves.
/-- Lemma 18.19.8 (2): if every object of `C` has at most one morphism to `U`, then for every
abelian sheaf `ℱ` on the localized site `C/U` the canonical map
`j_U⁻¹(j_{U*} ℱ) ⟶ ℱ` is an isomorphism. -/
theorem localization_inverseImage_pushforward_app_isIso_of_subsingletonHom
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (Over.forget U).op.HasPointwiseRightKanExtension F]
    (ℱ : Sheaf (J.over U) AddCommGrpCat.{max u v}) :
    IsIso (((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{max u v} (J.over U) J).counit.app
      ℱ) := by
  refine (fun hU ↦ ?_) hU
  letI : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  infer_instance

end CategoryTheory
