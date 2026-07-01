import Mathlib
import stacks_project.Chap07.Lemma_7_25_4
import stacks_project.Chap07.Lemma_7_25_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {U V : C} (f : V ⟶ U)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.forget V).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify (J.over V) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.25.9:
- primary domain: relocalization between localized sheaf topoi, compared through the slice
  equivalences over the sheafified representables;
- sampled owner declarations:
  `GrothendieckTopology.representableLocalizationComparison`,
  `CategoryTheory.Over.map`,
  `CategoryTheory.Over.pullback`,
  `CategoryTheory.Over.isoMk`;
- source-facing layer: the textbook identifications of relocalization lower shriek with
  postcomposition by `h_V^# ⟶ h_U^#` and relocalization inverse image with pullback along that
  morphism;
- core/canonical owner abstractions: the slice functors `Over.map (J.sheafifiedRepresentableMap f)`
  and `Over.pullback (J.sheafifiedRepresentableMap f)` on
  `Sh(C, J) / h_V^#` and `Sh(C, J) / h_U^#`, viewed through the equivalences
  `J.representableLocalizationComparison V` and `J.representableLocalizationComparison U`;
- bridge/view layer: this file is precisely the owner-level comparison between the localization
  functors on slice sites and those canonical slice-category functors on sheaves;
- primitive data: only the site `J`, the morphism `f`, and the sheaf argument;
- derived API: the comparison isomorphism and pullback description in `Over` are induced from the
  canonical localization comparison functors and the canonical slice functors, so the public
  surface should live in `Over`, not only in raw `CommSq`/`IsPullback` form.
-/

section LowerShriek

variable [∀ F : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.map f).op.HasLeftKanExtension F]

-- Proof sketch: the component of `Functor.sheafPullbackComp'` at `𝒢` identifies
-- `j_{U!}(j_! 𝒢)` with `j_{V!} 𝒢`; under `J.representableLocalizationComparison`, this upgrades
-- the raw commutative square to an isomorphism in the slice category over `h_U^#`, comparing
-- relocalization lower shriek with `Over.map (J.sheafifiedRepresentableMap f)`. The comparison is
-- the slice specialization of the canonical owner `Functor.sheafPullbackComp'`.
/-- The canonical comparison square in `Sh(C, J)` upgrading the relocalization lower-shriek
comparison to a morphism in the slice over `h_U^#`. -/
private theorem relocalization_lower_shriek_over_map_square
    (𝒢 : Sheaf (J.over V) (Type (max u v))) :
    CommSq
      ((Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
            (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
                (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J ≅
              (Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).inv.app 𝒢)
      (J.representableLocalizationHom V 𝒢)
      (J.representableLocalizationHom U
        (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢))
      (J.sheafifiedRepresentableMap f) := sorry

/-- Lemma 7.25.9 (2): under the equivalences
`Sh(C/V) ≌ Sh(C, J) / h_V^#` and `Sh(C/U) ≌ Sh(C, J) / h_U^#`, the relocalization lower shriek is
the slice functor `Over.map (h_V^# ⟶ h_U^#)`. -/
noncomputable def relocalization_lower_shriek_over_map :
    (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
        J.representableLocalizationComparison U ≅
      J.representableLocalizationComparison V ⋙
        Over.map (J.sheafifiedRepresentableMap f) :=
  NatIso.ofComponents
    (fun 𝒢 ↦
      let e :=
        (Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
            (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
                (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J ≅
              (Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).app 𝒢
      Over.isoMk e <| by
        change
          e.hom ≫
              (J.representableLocalizationHom V 𝒢 ≫ J.sheafifiedRepresentableMap f) =
            J.representableLocalizationHom U
              (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢)
        have h :
            e.inv ≫
                J.representableLocalizationHom U
                  (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢) =
              J.representableLocalizationHom V 𝒢 ≫ J.sheafifiedRepresentableMap f := by
          simpa [e] using (relocalization_lower_shriek_over_map_square J f 𝒢).w
        have h := congrArg (e.hom ≫ ·) h
        simpa [Category.assoc, Iso.hom_inv_id_assoc] using h.symm)
    (by
      intro 𝒢 𝒢' η
      ext
      sorry)

end LowerShriek

-- Proof sketch: transport the right-adjoint description of relocalization across the slice
-- equivalences of Lemma 7.25.4. The resulting object in `Sh(C, J) / h_V^#` is exactly the
-- canonical pullback object along `J.sheafifiedRepresentableMap f`.
private theorem relocalization_inverse_image_over_pullback_obj_eq
    (𝒢 : Sheaf (J.over U) (Type (max u v))) :
    (J.overMapPullback (Type (max u v)) f ⋙
          J.representableLocalizationComparison V).obj 𝒢 =
      (J.representableLocalizationComparison U ⋙
          Over.pullback (J.sheafifiedRepresentableMap f)).obj 𝒢 := sorry

/-- Lemma 7.25.9 (1): under the equivalences
`Sh(C/U) ≌ Sh(C, J) / h_U^#` and `Sh(C/V) ≌ Sh(C, J) / h_V^#`, the relocalization inverse image is
pullback along `h_V^# ⟶ h_U^#`. -/
noncomputable def relocalization_inverse_image_over_pullback :
    J.overMapPullback (Type (max u v)) f ⋙ J.representableLocalizationComparison V ≅
      J.representableLocalizationComparison U ⋙
        Over.pullback (J.sheafifiedRepresentableMap f) :=
  NatIso.ofComponents
    (fun 𝒢 ↦ eqToIso (relocalization_inverse_image_over_pullback_obj_eq J f 𝒢))
    (by
      intro 𝒢 𝒢' η
      sorry)

end

end CategoryTheory.GrothendieckTopology
