import Mathlib
import stacks_project.Chap07.Lemma_7_25_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.25.4:
- primary domain: the localized site `(C / U, J.over U)` and its comparison with the slice topos
  `Sh(C, J) / h_U^#`;
- sampled owner API:
  `Functor.toOver`,
  `Functor.toOver_comp_forget`,
  `Functor.isTerminalConst`,
  `continuous_sheafified_representable_iso`;
- source/core/bridge triage:
  `source-facing`: the comparison functor from sheaves on `(C / U, J.over U)` to sheaves over
    `h_U^#`;
  `core/canonical`: the lower-shriek owner `(Over.forget U).sheafPullback ...`, the general
    `Functor.toOver` construction of a functor into a slice category, and the terminal-object
    owners for constant presheaves/sheaves;
  `bridge/view`: the canonical structure morphism
    `representableLocalizationHom`, giving the `toOver` specialization for the localized
    lower-shriek.

Primitive data are the lower-shriek functor and the canonical terminality of the identity object in
`Over U`. The comparison functor is derived from the owner abstraction `Functor.toOver`; the
terminal comparison on the representable side should therefore reuse the canonical terminal-object
owners rather than re-encoding pointwise uniqueness data.
-/

-- Proof sketch: `Over.mk (𝟙 U)` is terminal in `Over U`, so its representable presheaf is
-- canonically the terminal `PUnit`-valued presheaf. Passing to sheaves identifies the
-- sheafified representable with the canonical terminal sheaf on `(C/U, J.over U)`.
/-- The representable presheaf of the identity object in `Over U` is the constant terminal
`PUnit`-valued presheaf. -/
private noncomputable def localized_identity_representable_iso_terminal (U : C) :
    ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max u v)) ≅
        (Functor.const (Over U)ᵒᵖ).obj (PUnit : Type (max u v)) :=
  let yonedaOver : Over U ⥤ (Over U)ᵒᵖ ⥤ Type (max u v) :=
    CategoryTheory.uliftYoneda.{max u v}
  let hRep :
      IsTerminal
        ((yonedaOver.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u v)) :=
    IsTerminal.isTerminalObj yonedaOver (Over.mk (𝟙 U)) Over.mkIdTerminal
  IsTerminal.uniqueUpToIso hRep <|
    Functor.isTerminalConst (Over U)ᵒᵖ Types.isTerminalPUnit

/-- The sheafified representable of the identity object in `Over U` is canonically the terminal
sheaf on the localized site. -/
private noncomputable def localized_identity_sheafifiedRepresentable_iso_terminal
    (U : C) [HasWeakSheafify (J.over U) (Type (max u v))] :
    (J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)) ≅
      Sheaf.terminal (J.over U) Types.isTerminalPUnit := by
  simpa [GrothendieckTopology.sheafifiedRepresentable,
    GrothendieckTopology.uliftSheafifiedRepresentable] using
    (Functor.mapIso (presheafToSheaf (J.over U) (Type (max u v)))
      (localized_identity_representable_iso_terminal U) ≪≫
        (sheafificationIso (Sheaf.terminal (J.over U) Types.isTerminalPUnit)).symm)

/-- The sheafified representable of the identity arrow `U ⟶ U` is terminal on the localized site.
-/
private noncomputable instance localized_identity_sheafifiedRepresentable_isTerminal
    (U : C) [HasWeakSheafify (J.over U) (Type (max u v))] :
    IsTerminal ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) := by
  exact IsTerminal.ofIso
    (Sheaf.isTerminalTerminal (J.over U) Types.isTerminalPUnit)
    (localized_identity_sheafifiedRepresentable_iso_terminal J U).symm

section

variable (U : C)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/-- The canonical map from the lower-shriek image `j_{U!} 𝒢` to the sheafified representable
`h[U]^#[J]`. -/
noncomputable def representableLocalizationHom
    (𝒢 : Sheaf (J.over U) (Type (max u v))) :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj 𝒢 ⟶
      h[U]^#[J] :=
  ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
      ((localized_identity_sheafifiedRepresentable_isTerminal J U).from 𝒢) ≫
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
      (Over.mk (𝟙 U))).symm.hom

-- Proof sketch: functoriality of `j_{U!}` carries any morphism `η : 𝒢 ⟶ 𝒢'` to a commutative
-- triangle with the terminal arrows to the identity representable, so the induced maps to
-- `h[U]^#[J]` are natural.
/-- Naturality of the canonical maps `j_{U!} 𝒢 ⟶ h[U]^#[J]`. -/
private theorem representableLocalizationHom_naturality
    {𝒢 𝒢' : Sheaf (J.over U) (Type (max u v))} (η : 𝒢 ⟶ 𝒢') :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map η ≫
        J.representableLocalizationHom U 𝒢' =
      J.representableLocalizationHom U 𝒢 := sorry

/-- The comparison functor from sheaves on the slice site `(C/U, J.over U)` to sheaves over the
sheafified representable `h[U]^#[J]`. -/
noncomputable def representableLocalizationComparison
    :
    Sheaf (J.over U) (Type (max u v)) ⥤ Over h[U]^#[J] :=
  ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).toOver
    h[U]^#[J]
    (J.representableLocalizationHom U)
    (J.representableLocalizationHom_naturality U)

/-- Forgetting the structure morphism from the representable-localization comparison functor
recovers the canonical lower-shriek `j_{U!}`. -/
@[simp] theorem representableLocalizationComparison_forget
    :
    J.representableLocalizationComparison U ⋙ Over.forget h[U]^#[J] =
      (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J := by
  simpa [representableLocalizationComparison] using
    (Functor.toOver_comp_forget
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J)
      h[U]^#[J]
      (J.representableLocalizationHom U)
      (J.representableLocalizationHom_naturality U))

-- Proof sketch: construct the inverse functor by sending a morphism `φ : ℱ ⟶ h[U]^#[J]` to the
-- sheaf
-- on `C/U` given by the fiber over each section `a : X ⟶ U`; the presheaf-level constructions in
-- the textbook are inverse to one another, and Lemmas 7.25.2 and 7.25.3 identify those
-- constructions with the chosen lower-shriek functor and the sheafified representable
-- `h[U]^#[J]`.
/-- Lemma 7.25.4: the canonical functor from sheaves on the localized site `(C/U, J.over U)` to
sheaves over `h[U]^#[J]`, sending `𝒢` to the canonical morphism
`j_{U!} 𝒢 ⟶ h[U]^#[J]`, is an equivalence. -/
theorem representableLocalizationComparison_isEquivalence
    :
    Functor.IsEquivalence (J.representableLocalizationComparison U) := sorry

end

end CategoryTheory.GrothendieckTopology
