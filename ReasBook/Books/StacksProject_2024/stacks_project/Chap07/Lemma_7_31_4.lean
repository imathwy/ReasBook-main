import Mathlib
import StacksProject_2024.Chap07.Definition_7_14_1
import StacksProject_2024.Chap07.Lemma_7_13_5
import StacksProject_2024.Chap07.Lemma_7_25_9
import StacksProject_2024.Chap07.Lemma_7_30_7
import StacksProject_2024.Chap07.Lemma_7_31_2
import StacksProject_2024.Chap07.Lemma_7_31_3

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u₁ v₁

noncomputable section

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₁} [Category.{v₁} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 7.31.4:
- primary domain: localized inverse-image comparisons for morphisms of sites at sheafified
  representables, together with the canonical slice pullback induced by `c : U ⟶ u.obj V`;
- sampled owner declarations:
  `continuous_sheafified_representable_iso`,
  `representable_localization_comparison_agrees_with_localized_inverseImage`,
  `localization_inverseImage_pullback_base_change`,
  `Over.pullback`;
- best owner abstraction:
  the owner-level localized inverse image is already
  `LeftExactAdjunction.localization`, specialized in this chapter by
  `representable_localization_comparison_agrees_with_localized_inverseImage` and then base-changed
  by `localization_inverseImage_pullback_base_change`. The map
  `h[U]^# ⟶ u⁻¹(h[V]^#)` induced by `c` is derived data, so this file should use the canonical
  composite
  `JC.sheafifiedRepresentableMap c ≫ (continuous_sheafified_representable_iso u JD JC V).hom`
  directly instead of introducing a parallel local owner;
- primitive data vs derived API:
  primitive data are the site morphism `u`, the objects `U`, `V`, and the arrow `c : U ⟶ u.obj V`;
  the comparison morphism on sheafified representables and the resulting slice pullback functor are
  derived from the canonical owners above;
- source/core/bridge triage:
  `source-facing`: the theorem below, matching the Stacks comparison for `c : U ⟶ u.obj V`;
  `core/canonical`: `LeftExactAdjunction.localization`, `Over.pullback`, and
    `continuous_sheafified_representable_iso`;
  `bridge/view`: the theorem below, combining the representable-localization comparison with the
    canonical localized pullback/base-change comparison from Lemma `7.31.3`.
-/

-- Proof sketch: combine Lemma `7.31.2`, which identifies the representable-localized inverse
-- image for `u`, with the pullback/base-change comparison from Lemma `7.31.3` for the canonical
-- map `h[U]^# ⟶ u⁻¹(h[V]^#)` induced by `c`.
noncomputable def representable_localization_comparison_agrees_with_localized_pullback_iso
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    {V : D} {U : C} (c : U ⟶ u.obj V)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget U).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
    [HasWeakSheafify (JC.over U) (Type (max u₁ v₁))] :
    u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) U ⋙
        JC.representableLocalizationComparison U ≅
      JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
            h[V]^#[JD]).inverseImage ⋙
        Over.pullback
          (JC.sheafifiedRepresentableMap c ≫
            (continuous_sheafified_representable_iso u JD JC V).hom) := by
  let A := Type (max u₁ v₁)
  let f := u.morphismOfTopoiInOfContinuous JD JC
  let 𝒢 : Sheaf JD A := h[V]^#[JD]
  let a : h[U]^#[JC] ⟶ h[u.obj V]^#[JC] :=
    JC.sheafifiedRepresentableMap c
  let e := continuous_sheafified_representable_iso u JD JC V
  let sourceIso :
      u.sheafPullback A JD JC ⋙
          JC.overPullback A U ⋙
          JC.representableLocalizationComparison U ≅
        u.sheafPullback A JD JC ⋙
          JC.overPullback A (u.obj V) ⋙
          JC.representableLocalizationComparison (u.obj V) ⋙
          Over.pullback a :=
    Functor.associator (u.sheafPullback A JD JC) (JC.overPullback A U)
      (JC.representableLocalizationComparison U) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
        ((Functor.sheafPushforwardContinuousComp'
          (Over.mapForget c) A (JC.over U) (JC.over (u.obj V)) JC).symm))
      (JC.representableLocalizationComparison U) ≪≫
    (Functor.associator (u.sheafPullback A JD JC)
      (JC.overPullback A (u.obj V) ⋙ JC.overMapPullback A c)
      (JC.representableLocalizationComparison U)).symm ≪≫
    Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
      ((Functor.associator (JC.overPullback A (u.obj V)) (JC.overMapPullback A c)
        (JC.representableLocalizationComparison U)).symm ≪≫
        Functor.isoWhiskerLeft (JC.overPullback A (u.obj V))
          (JC.relocalization_inverse_image_over_pullback c))
  let targetIso :
      ((f.localization 𝒢).inverseImage ⋙ Over.pullback e.hom ⋙ Over.pullback a) ≅
        (f.localization 𝒢).inverseImage ⋙ Over.pullback (a ≫ e.hom) :=
    (localization_inverseImage_pullback_base_change_iso f (𝟙 𝒢) a e.hom (a ≫ e.hom)
      (by simp)).symm ≪≫
      Functor.isoWhiskerRight Over.pullbackId
        ((f.localization 𝒢).inverseImage ⋙ Over.pullback (a ≫ e.hom)) ≪≫
      Functor.leftUnitor ((f.localization 𝒢).inverseImage ⋙ Over.pullback (a ≫ e.hom))
  exact
    sourceIso ≪≫
      Functor.isoWhiskerRight
        (representable_localization_comparison_inverseImageIso u V)
        (Over.pullback a) ≪≫
      Functor.isoWhiskerLeft
        (JD.overPullback A V ⋙ JD.representableLocalizationComparison V)
        targetIso

/-- Lemma 7.31.4: let `f : (C, JC) ⟶ (D, JD)` be the morphism of sites presented by the continuous
representably flat functor `u : D ⥤ C`, let `V : D`, and let `c : U ⟶ u.obj V`. If
`𝒢 = h_V^#`, `ℱ = h_U^#`, and `s : ℱ ⟶ f^{-1} 𝒢` is the morphism induced by `c`, then via the
identifications `j_ℱ = j_U` and `j_𝒢 = j_V`, the localized site diagram of Lemma `7.28.3`
agrees with the localized sheaf-over-sheaf diagram of Lemma `7.31.3`. In Lean, this is the
comparison between the two inverse-image composites after identifying `Sh(D/V)` and `Sh(C/U)`
with the slice topoi over `h_V^#` and `h_U^#`; the right-hand composite uses the canonical
localized inverse image `((f.localization _).inverseImage ⋙ Over.pullback _)` from
Lemma `7.31.3`, not a separate Chapter 7 alias. -/
theorem representable_localization_comparison_agrees_with_localized_pullback
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    {V : D} {U : C} (c : U ⟶ u.obj V)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget U).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
    [HasWeakSheafify (JC.over U) (Type (max u₁ v₁))] :
    IsIsomorphic
      (u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) U ⋙
        JC.representableLocalizationComparison U)
      (JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
            h[V]^#[JD]).inverseImage ⋙
        Over.pullback
          (JC.sheafifiedRepresentableMap c ≫
            (continuous_sheafified_representable_iso u JD JC V).hom)) := by
  exact ⟨representable_localization_comparison_agrees_with_localized_pullback_iso u c⟩

end

end CategoryTheory
