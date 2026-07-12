import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_27_4

open Opposite

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
- `source-facing`: the two canonical maps for abelian sheaves on `C/U`;
- `core/canonical`: the unit and counit morphisms of the localization adjunction owners;
- `bridge/view`: the fullness of `Over.forget U` supplied by
  `overForget_full_of_subsingletonHom`.

This item is an `AddCommGrpCat` specialization of the localization owner API from
`Chap07/Lemma_7_27_4`, so the refined public surface should be direct recall/reuse of the
canonical owner instances rather than duplicate theorem declarations with the same names.
-/

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (U : C)

section

variable (hU : ∀ X : C, Subsingleton (X ⟶ U))
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v}, (Over.forget U).op.HasLeftKanExtension F]
variable (ℱ : Sheaf (J.over U) AddCommGrpCat.{max u v})

/- Lemma 18.19.8 (1): for an abelian sheaf `ℱ` on the localized site `C/U`, the canonical map
`ℱ ⟶ j_U⁻¹(j_{U!} ℱ)`, i.e. the unit component of
`(Over.forget U).sheafAdjunctionContinuous AddCommGrpCat (J.over U) J`, is an isomorphism. This
is the direct `AddCommGrpCat` specialization of the chapter-level owner instance. -/
recall unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful

example :
    IsIso
      (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{max u v} (J.over U) J).unit.app
        ℱ) := by
  letI : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  exact unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful (J.over U) J (Over.forget U) ℱ

end

section

variable (hU : ∀ X : C, Subsingleton (X ⟶ U))
variable [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.forget U).op.HasPointwiseRightKanExtension F]
variable (ℱ : Sheaf (J.over U) AddCommGrpCat.{max u v})

/- Lemma 18.19.8 (2): for an abelian sheaf `ℱ` on the localized site `C/U`, the canonical map
`j_U⁻¹(j_{U*} ℱ) ⟶ ℱ`, i.e. the counit component of
`(Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat (J.over U) J`, is an isomorphism.
This is the direct `AddCommGrpCat` specialization of the chapter-level owner instance. -/
recall counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful

example :
    IsIso
      (((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{max u v} (J.over U) J).counit.app
        ℱ) := by
  letI : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  exact counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful (J.over U) J (Over.forget U) ℱ

end

end CategoryTheory
