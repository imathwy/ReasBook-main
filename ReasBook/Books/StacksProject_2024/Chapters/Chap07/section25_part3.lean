import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_25_5 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe w u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (U : C)

/- Domain-style sampling for Lemma 7.25.5:
- primary domain: localization lower shriek on sheaves, viewed through the slice-category
  description over the sheafified representable `h_U^#`;
- sampled owner API:
  `GrothendieckTopology.representableLocalizationComparison`,
  `GrothendieckTopology.representableLocalizationComparison_isEquivalence`,
  `GrothendieckTopology.representableLocalizationComparison_forget`,
  `CategoryTheory.Functor.sheafPullback`,
  `Over.preservesLimitsOfShape_forget_of_isConnected`,
  `Functor.PreservesMonomorphisms`;
- source-facing layer: the localization lower shriek `j_{U!}`;
- core/canonical owner: `CategoryTheory.Functor.sheafPullback`, specialized to `Over.forget U`;
- bridge/view: `J.representableLocalizationComparison_forget U` identifies this owner with the
  composite of the equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` and the slice forgetful functor.

Primitive data are the site `(C, J)` and the localization object `U`; the lower shriek itself is
already the canonical owner `(Over.forget U).sheafPullback ...`. Connected-limit,
finite-connected-limit, pullback, equalizer, and monomorphism preservation are derived API of
that owner. The proof below temporarily invokes the comparison equivalence from Lemma `7.25.4`,
with its sheafification and Kan-extension inputs supplied locally by canonical instance search,
rather than exposing those proof-route hypotheses in the public section context.
-/

-- Proof sketch: identify `j_{U!}` with the composite of the equivalence from Lemma `7.25.4`
-- between `Sh(C/U)` and the slice category `Sh(C)/h_U^#` and the forgetful functor from that
-- slice category to `Sh(C)`. Equivalences preserve all limits, and the forgetful functor from an
-- over category preserves connected limits, so the source statement follows for finite connected
-- shapes in particular.
/-- Lemma 7.25.5: for a site `(C, J)` and an object `U : C`, the localization lower shriek
functor `j_{U!} : Sh(C/U) ⥤ Sh(C)`, realized canonically as
`(Over.forget U).sheafPullback (Type (max u v)) (J.over U) J`, commutes with finite connected
limits. -/
theorem localizationLowerShriek_preserves_finite_connected_limits
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) := by
  letI : HasWeakSheafify J (Type (max u v)) := inferInstance
  letI : HasWeakSheafify (J.over U) (Type (max u v)) := inferInstance
  letI : ∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G :=
    fun G ↦ inferInstance
  letI : Functor.IsEquivalence (J.representableLocalizationComparison U) :=
    J.representableLocalizationComparison_isEquivalence U
  simpa using
    (inferInstance :
      PreservesLimitsOfShape I
        (J.representableLocalizationComparison U ⋙ Over.forget h[U]^#[J]))

-- Proof sketch: apply the connected-limit statement to the walking cospan, whose limits are
-- pullbacks.
/-- The localization lower shriek preserves fibre products. -/
theorem localizationLowerShriek_preserves_pullbacks
    :
    PreservesLimitsOfShape WalkingCospan
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) :=
  localizationLowerShriek_preserves_finite_connected_limits U WalkingCospan

-- Proof sketch: apply the connected-limit statement to the walking parallel pair, whose
-- limits are equalizers.
/-- The localization lower shriek preserves equalizers. -/
theorem localizationLowerShriek_preserves_equalizers
    :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) :=
  localizationLowerShriek_preserves_finite_connected_limits U WalkingParallelPair

-- Proof sketch: in a category with pullbacks, any functor preserving pullbacks preserves
-- monomorphisms. Apply this to the canonical lower-shriek owner and the previous theorem.
/-- The localization lower shriek sends monomorphisms of sheaves on `C/U` to monomorphisms of
sheaves on `C`. -/
instance localizationLowerShriek_preservesMonomorphisms
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).PreservesMonomorphisms := by
  letI :
      PreservesLimitsOfShape WalkingCospan
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) :=
    localizationLowerShriek_preserves_pullbacks U
  infer_instance

end

/-! ### Lemma_7_25_6 (from Chap07) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (U : C)
variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.25.6:
- primary domain: localization lower shriek on sheaves, compared with the slice category over the
  sheafified representable `h_U^#`;
- sampled owner API:
  `GrothendieckTopology.representableLocalizationComparison`,
  `GrothendieckTopology.representableLocalizationComparison_isEquivalence`,
  `CategoryTheory.Functor.ReflectsMonomorphisms`,
  `CategoryTheory.Functor.ReflectsEpimorphisms`;
- source-facing layer: the localization lower shriek `j_{U!}`, realized canonically as
  `(Over.forget U).sheafPullback (Type (max u v)) (J.over U) J`;
- core/canonical owner: the equivalence `J.representableLocalizationComparison U` from sheaves on
  `(C/U, J.over U)` to the slice category `Sh(C, J) / h_U^#`;
- bridge/view: composing that equivalence with the slice forgetful functor recovers `j_{U!}`,
  so reflection of monomorphisms and epimorphisms is derived API of the owner comparison rather
  than primitive data of a separate localization wrapper.

Primitive data are the site `(C, J)`, the localization object `U`, and the canonical lower-shriek
functor already owned by `Functor.sheafPullback`. Reflection of injections and surjections is
derived from the owner-level equivalence together with the standard slice forgetful functor, so
this file should reuse that comparison directly instead of introducing parallel local copies.
-/

-- Proof sketch: by Lemma `7.25.4`, `j_{U!}` identifies with the composite of the comparison
-- equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` and the slice forgetful functor to `Sh(C)`. Both functors
-- are faithful, hence both reflect monomorphisms, so the composite does as well.
/-- Lemma 7.25.6 (1): for a site `(C, J)` and an object `U : C`, the localization lower shriek
functor `j_{U!}` reflects monomorphisms; equivalently, it reflects injections of set-valued
sheaves. -/
instance localizationLowerShriek_reflectsMonomorphisms
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).ReflectsMonomorphisms := by
  let comparison := J.representableLocalizationComparison U
  haveI : comparison.IsEquivalence := J.representableLocalizationComparison_isEquivalence U
  simpa [comparison] using
    (inferInstance :
      (comparison ⋙ Over.forget h[U]^#[J]).ReflectsMonomorphisms)

-- Proof sketch: the same comparison identifies `j_{U!}` with a composite of faithful functors,
-- so epimorphisms are reflected for the same owner-level reason.
/-- Lemma 7.25.6 (2): for a site `(C, J)` and an object `U : C`, the localization lower shriek
functor `j_{U!}` reflects epimorphisms; equivalently, it reflects surjections of set-valued
sheaves. -/
instance localizationLowerShriek_reflectsEpimorphisms
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).ReflectsEpimorphisms := by
  let comparison := J.representableLocalizationComparison U
  haveI : comparison.IsEquivalence := J.representableLocalizationComparison_isEquivalence U
  simpa [comparison] using
    (inferInstance :
      (comparison ⋙ Over.forget h[U]^#[J]).ReflectsEpimorphisms)

end

/-! ### Lemma_7_25_7 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (U : C)
variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify J (Type (max u v))]
variable (F : Sheaf J (Type (max u v)))

/- Domain-style sampling for Lemma 7.25.7:
- primary domain: localization of sheaves on a slice site and the corresponding slice-category
  description over the sheafified representable `h_U^#`;
- sampled owner API:
  `GrothendieckTopology.representableLocalizationComparison`,
  `Functor.toOver_comp_forget`,
  `GrothendieckTopology.representableLocalizationComparison_inverseImage_obj`,
  `Sheaf.over`,
  `Over.star`,
  `Over.star_obj_hom`;
- source-facing layer: the canonical comparison
  `j_{U!} j_U^{-1} F ⟶ F × h[U]^#[J]`;
- core/canonical owner: the slice object `(J.representableLocalizationComparison U).obj (F.over U)`
  over `h[U]^#[J]`, canonically identified with `((Over.star h[U]^#[J]).obj F)`
  representing product with `h[U]^#[J]`;
- bridge/view: the binary-product braiding turning the canonical `h_U^# × F` slice object into the
  textbook-ordered `F × h[U]^#[J]` projection.

Primitive data are the ambient site `(C, J)`, the object `U`, and the sheaf `F`. The map to the
product is derived from the owner-level over-category comparison and the canonical identification
of inverse-image objects with `Over.star`. The localized restriction should be exposed through the
canonical owner `F.over U`, not the lower-level spelling `(J.overPullback _ U).obj F`.
-/

/-- Lemma 7.25.7: for a sheaf `F` on `(C, J)` and an object `U : C`, the localization extension by
the empty set `j_{U!} j_U^{-1} F` is isomorphic to the product `F × h[U]^#[J]`. -/
noncomputable def localization_lowerShriek_overPullback_prodIso
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        (F.over U) ≅
      (F ⨯ h[U]^#[J]) := by
  let starProdIso :
      (Over.star h[U]^#[J]).obj F ≅
        Over.mk (prod.snd : F ⨯ h[U]^#[J] ⟶ h[U]^#[J]) :=
    Over.isoMk (prod.braiding h[U]^#[J] F) (by
      rw [Over.star_obj_hom]
      calc
        prod.lift prod.snd prod.fst ≫ prod.snd = prod.fst := by
          rw [prod.lift_snd]
        _ = prod.lift prod.fst (𝟙 (h[U]^#[J] ⨯ F)) ≫ prod.fst := by
          symm
          rw [prod.lift_fst])
  simpa [GrothendieckTopology.representableLocalizationComparison] using
    Functor.mapIso
      (Over.forget h[U]^#[J])
      (J.representableLocalizationComparison_inverseImage_obj U F ≪≫ starProdIso)

/-- The forward morphism of `localization_lowerShriek_overPullback_prodIso` is an isomorphism. -/
-- Proof sketch: this morphism is the `hom` of the canonical isomorphism
-- `localization_lowerShriek_overPullback_prodIso`.
theorem localization_lowerShriek_overPullback_prodIso_hom_isIso :
    IsIso (localization_lowerShriek_overPullback_prodIso U F).hom := by
  -- The target map is literally the forward arrow of an isomorphism already constructed above.
  infer_instance

end

/-! ### Lemma_7_25_8 (from Chap07) -/
open CategoryTheory Opposite

universe u₁ v₁ uA vA

noncomputable section

section

variable {C : Type u₁} [Category.{v₁} C]
variable (J : GrothendieckTopology C)
variable {U V : C} (f : V ⟶ U)

/- Domain-style sampling for Lemma 7.25.8:
- primary domain: relocalization between slice sites and the induced sheaf functors;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `Functor.sheafPushforwardCocontinuousComp'`,
  `Functor.sheafPullbackComp'`,
  `Functor.sheafPullback`,
  `GrothendieckTopology.overMapPullback`;
- source-facing layer: the textbook comparison between localization at `V`, localization at `U`,
  and relocalization along `f`;
- core/canonical owner: the specialized slice-site functors `J.overPullback`, `J.overMapPullback`,
  and the canonical comparison
  `Functor.sheafPushforwardContinuousComp' (Over.mapForget f)`;
- bridge/view: the direct-image and lower-shriek functors are the cocontinuous pushforward and
  pullback owners attached to `Over.map f` and `Over.forget U`.

Primitive data are only the site `J` and the morphism `f`. The inverse-image comparison is derived
from the canonical owner isomorphism, the direct-image comparison is definitional, and the
lower-shriek comparison is the direct specialization of the canonical pullback-composition owner
`Functor.sheafPullbackComp'`.
-/

variable (A : Type uA) [Category.{vA} A]

/- Lemma 7.25.8: the inverse-image comparison `j_U⁻¹ ⋙ j⁻¹ ≅ j_V⁻¹` is exactly the specialized
canonical owner `Functor.sheafPushforwardContinuousComp'` for the triangle
`Over.map f ⋙ Over.forget U ≅ Over.forget V`. -/
#check
  (Functor.sheafPushforwardContinuousComp' (Over.mapForget f) A (J.over V) (J.over U) J :
    J.overPullback A U ⋙ J.overMapPullback A f ≅ J.overPullback A V)

/- The direct-image comparison `j_* ⋙ j_{U*} ≅ j_{V*}` is the specialized owner
`Functor.sheafPushforwardCocontinuousComp'` for the canonical isomorphism
`Over.mapForget f : Over.map f ⋙ Over.forget U ≅ Over.forget V`; no chapter-local wrapper is
needed. -/
section DirectImage

variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.forget V).op.HasPointwiseRightKanExtension F]

#check
  (Functor.sheafPushforwardCocontinuousComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
      (Over.map f).sheafPushforwardCocontinuous A (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPushforwardCocontinuous A (J.over U) J ≅
        (Over.forget V).sheafPushforwardCocontinuous A (J.over V) J)

end DirectImage

/- The lower-shriek comparison `j_! ⋙ j_{U!} ≅ j_{V!}` is exactly the slice specialization of the
canonical owner `Functor.sheafPullbackComp'` for the triangle
`Over.map f ⋙ Over.forget U ≅ Over.forget V`. -/
section LowerShriek

variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasLeftKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasLeftKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.forget V).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) A] [HasWeakSheafify J A]

#check
  (Functor.sheafPullbackComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
      (Over.map f).sheafPullback A (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPullback A (J.over U) J ≅
        (Over.forget V).sheafPullback A (J.over V) J)

end LowerShriek

end
