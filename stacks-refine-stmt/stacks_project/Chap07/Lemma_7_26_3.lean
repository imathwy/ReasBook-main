import Mathlib
import stacks_project.Chap07.Lemma_7_12_4
import stacks_project.Chap07.Lemma_7_21_1
import stacks_project.Chap07.Lemma_7_25_7
import stacks_project.Chap07.Lemma_7_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (U : C) (ℱ : Sheaf J (Type (max u v)))

/- Domain-style sampling for Lemma 7.26.3:
- primary domain: internal Hom for sheaves of types and the localization direct image `j_{U*}`;
- sampled owner API:
  `sheaf_prod_sheafHom_equiv`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `GrothendieckTopology.overPullback`/`Sheaf.over`,
  `localization_lowerShriek_overPullback_prodIso`,
  `Functor.sheafAdjunctionCocontinuous`;
- source/core/bridge triage:
  `source-facing`: the canonical identification `sheafHom (h_U^#) ℱ ≅ j_{U*}(ℱ.over U)`;
  `core/canonical`: the localization morphism of topoi
  `(Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J` and its direct image `j_{U*}`;
  `bridge/view`: the product comparison `localization_lowerShriek_overPullback_prodIso U 𝒢`,
  the currying equivalence `sheaf_prod_sheafHom_equiv`, and the adjunction chain induced by
  `Over.forget U`.

Primitive data are only the localized object `U` and the sheaf `ℱ`. The Hom-equivalence for a test
sheaf `𝒢` is derived from these owner-level constructions, so it should remain private proof
machinery rather than a second public owner.
-/

private noncomputable def sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv
    (𝒢 : Sheaf J (Type (max u v))) :
    (𝒢 ⟶ sheafHom h[U]^#[J] ℱ) ≃
      (𝒢 ⟶ ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj
        (ℱ.over U))) := by
  simpa using
    (sheaf_prod_sheafHom_equiv 𝒢 h[U]^#[J] ℱ).symm.trans
      (((localization_lowerShriek_overPullback_prodIso U 𝒢).symm.homCongr
          (Iso.refl ℱ)).trans
        ((((Over.forget U).sheafAdjunctionContinuous
            (Type (max u v)) (J.over U) J).homEquiv _ _).trans
          (((Over.forget U).sheafAdjunctionCocontinuous
            (Type (max u v)) (J.over U) J).homEquiv _ _)))

private theorem sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv_naturality
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢)
    (g : 𝒢 ⟶ sheafHom h[U]^#[J] ℱ) :
    sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢' (f ≫ g) =
      f ≫ sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢 g := by
  sorry

/-- Lemma 7.26.3: for a site `(C, J)`, an object `U : C`, and a sheaf of sets `ℱ`, the sheaf-Hom
from the sheafified representable `h_U^#` to `ℱ` is canonically identified with the pushforward of
the restricted sheaf `ℱ.over U` from the slice site `(C/U, J.over U)` back to `(C, J)`. -/
noncomputable def sheafHom_sheafifiedRepresentable_iso_pushforward_restriction
    :
    sheafHom h[U]^#[J] ℱ ≅
      ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj (ℱ.over U)) :=
  Yoneda.ext _ _
    (fun {𝒢} f ↦
      sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢 f)
    (fun {𝒢} f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢).symm f)
    (fun f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ _).left_inv f)
    (fun f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ _).right_inv f)
    (fun f g ↦
      sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv_naturality U ℱ f g)

-- Proof sketch: the forward comparison morphism here is the `hom` of an explicit isomorphism, so
-- it is an isomorphism by the standard `Iso.hom` instance.
/-- The forward comparison morphism from `sheafHom h_U^# ℱ` to `j_{U*}(ℱ.over U)` is an
isomorphism. -/
theorem sheafHom_sheafifiedRepresentable_iso_pushforward_restriction_hom_isIso :
    IsIso (sheafHom_sheafifiedRepresentable_iso_pushforward_restriction U ℱ).hom := sorry

end
