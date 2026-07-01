import Mathlib
import stacks_project.Chap07.Lemma_7_21_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

noncomputable section

/- Domain-style sampling for Lemma 7.27.4:
- primary domain: localization of sites and the induced adjunctions on sheaves over slice sites;
- sampled owner API:
  `Over.forget`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`,
  `counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful`;
- source-facing layer: the two canonical maps
  `ℱ ⟶ j_U⁻¹ j_{U!} ℱ` and `j_U⁻¹ j_{U*} ℱ ⟶ ℱ`;
- core/canonical owner: the adjunction owners
  `(Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J` and
  `(Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J`;
- bridge/view: this file specializes the fully faithful site-functor results of Lemma 7.21.7 to
  the localization functor `Over.forget U`.

Primitive data are the site `J`, the object `U`, and the hypothesis that each hom-set `X ⟶ U` is
subsingleton. The `Full` structure on `Over.forget U` is the only extra primitive API needed in
this specialization; the `IsIso` statements for the unit and counit are derived from the canonical
adjunction owners.
-/

/-- If every object of `C` admits at most one morphism to `U`, then the localization functor
`Over.forget U : Over U ⥤ C` is full. This is the bridge from the source subsingleton-hom
hypothesis to the canonical fully faithful adjunction owners for localization. -/
theorem overForget_full_of_subsingletonHom
    {C : Type u} [Category.{v} C] (U : C)
    (hU : ∀ X : C, Subsingleton (X ⟶ U)) :
    (Over.forget U).Full where
  map_surjective {X Y} f := by
    refine ⟨Over.homMk f ?_, rfl⟩
    haveI : Subsingleton (X.left ⟶ U) := hU X.left
    exact (show (f ≫ Y.hom : X.left ⟶ U) = X.hom from Subsingleton.elim _ _)

-- Proof sketch: the hypothesis makes `Over.forget U` fully faithful, so Lemma `7.21.7` applies to
-- the continuous localization functor `Over.forget U : (C/U, J.over U) ⥤ (C, J)`.
/-- Lemma 7.27.4 (1): if every object of the site `C` has at most one morphism to `U`, then for
every sheaf `ℱ` on the localized site `C/U` the canonical map
`ℱ ⟶ j_U⁻¹ j_{U!} ℱ` is an isomorphism. -/
theorem localization_lowerShriek_unit_app_isIso_of_subsingletonHom
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [HasWeakSheafify J (Type w)]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    (ℱ : Sheaf (J.over U) (Type w)) :
    IsIso (((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J).unit.app ℱ) := by
  have hfull : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  letI : (Over.forget U).Full := hfull
  exact unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful (J.over U) J (Over.forget U) ℱ

-- Proof sketch: the same full-faithfulness bridge lets Lemma `7.21.7` identify the counit of the
-- cocontinuous localization adjunction as an isomorphism.
/-- Lemma 7.27.4 (2): if every object of the site `C` has at most one morphism to `U`, then for
every sheaf `ℱ` on the localized site `C/U` the canonical map
`j_U⁻¹ j_{U*} ℱ ⟶ ℱ` is an isomorphism. -/
theorem localization_inverseImage_pushforward_app_isIso_of_subsingletonHom
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
    (ℱ : Sheaf (J.over U) (Type w)) :
    IsIso (((Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J).counit.app ℱ) := by
  have hfull : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  letI : (Over.forget U).Full := hfull
  exact counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful (J.over U) J (Over.forget U) ℱ
