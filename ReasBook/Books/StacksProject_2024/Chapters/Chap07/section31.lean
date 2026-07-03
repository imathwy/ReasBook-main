import Mathlib
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_31_1 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.31.1:
- primary domain: localized geometric morphisms on slice topoi and the canonical `Over`
  adjunctions attached to a left adjoint;
- sampled owner API:
  `LeftExactAdjunction`,
  `LeftExactAdjunction.inverseImage`,
  `Over.postAdjunctionLeft`,
  `Over.forgetAdjStar`;
- source/core/bridge triage:
  `source-facing`: the induced localized morphism of topoi
    `Sh(𝒞) / f⁻¹ 𝒢 ⟶ Sh(𝒟) / 𝒢`;
  `core/canonical`: the generic owner `LeftExactAdjunction.localization` on the slice categories;
  `bridge/view`: the objectwise inverse-image formula and the canonical comparison of the two
    composite right adjoints, specialized to `MorphismOfTopoiIn`.

Primitive data for the core construction are only a left-exact adjunction `f⁻¹ ⊣ f_*` and an
object `Y` of the target category. In the source-facing specialization these become a morphism of
topoi `f` and a target sheaf `𝒢`. The refined API therefore promotes the construction to the
generic owner `LeftExactAdjunction.localization`; the sheaf-topos statement is then just its
specialization to `MorphismOfTopoiIn`.
-/

namespace LeftExactAdjunction

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/-- The canonical slice localization attached to a left-exact adjunction `f⁻¹ ⊣ f_*`. Its inverse
image is `Over.post f.inverseImage`, and its direct image is the corresponding slice right adjoint
obtained from `Over.postAdjunctionLeft`. -/
def localization
    [HasPullbacks B]
    (f : LeftExactAdjunction A B)
    (Y : B) :
    LeftExactAdjunction (Over (f.inverseImage.obj Y)) (Over Y) :=
  let η := f.adjunction.unit
  { inverseImageFunctor := by
      let inverseImage : Over Y ⥤ Over (f.inverseImage.obj Y) := Over.post f.inverseImage
      let _ : PreservesFiniteLimits inverseImage := by
        let _ : PreservesFiniteLimits f.inverseImage := inferInstance
        infer_instance
      exact LeftExactFunctor.of inverseImage
    pushforward := Over.post f.pushforward ⋙ Over.pullback (η.app Y)
    adjunction := by
      simpa using Over.postAdjunctionLeft f.adjunction }

-- Proof sketch: by definition the localized inverse image is `Over.post f.inverseImage`.
/-- The localized inverse image sends `(Z ⟶ Y)` to `(f⁻¹ Z ⟶ f⁻¹ Y)`. -/
@[simp] theorem localization_inverseImage_obj
    [HasPullbacks B]
    (f : LeftExactAdjunction A B)
    (Y : B)
    (Z : Over Y) :
    (f.localization Y).inverseImage.obj Z = Over.mk (f.inverseImage.map Z.hom) := by
  change (Over.post f.inverseImage).obj Z = Over.mk (f.inverseImage.map Z.hom)
  rfl

-- Proof sketch: both functors are right adjoint to
-- `Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) = Over.forget Y ⋙ f.inverseImage`,
-- so the comparison is the
-- canonical uniqueness isomorphism of right adjoints.
/-- Restricting to `f⁻¹ Y` and then pushing forward along the localized morphism is naturally
isomorphic to pushing forward along `f` and then restricting to `Y`. -/
noncomputable def localization_pushforwardStarIso
    [HasBinaryProducts A] [HasPullbacks B] [HasBinaryProducts B]
    (f : LeftExactAdjunction A B)
    (Y : B) :
    Over.star (f.inverseImage.obj Y) ⋙ (f.localization Y).pushforward ≅
      f.pushforward ⋙ Over.star Y := by
  let localizedAdj :
      Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ⊣
        Over.star (f.inverseImage.obj Y) ⋙ (f.localization Y).pushforward :=
    (Over.postAdjunctionLeft f.adjunction).comp (Over.forgetAdjStar (f.inverseImage.obj Y))
  let globalAdj :
      Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ⊣
        f.pushforward ⋙ Over.star Y :=
    ((Over.forgetAdjStar Y).comp f.adjunction).ofNatIsoLeft
      (eqToIso (by rfl) :
        Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ≅
          Over.forget Y ⋙ f.inverseImage)
  exact Adjunction.rightAdjointUniq localizedAdj globalAdj

end LeftExactAdjunction

namespace MorphismOfTopoiIn

section

variable (f : MorphismOfTopoiIn JD JC) (𝒢 : Sheaf JD (Type w))

/- Lemma 7.31.1 specialized to morphisms of topoi: for
`f : Sh(𝒞) ⟶ Sh(𝒟)` and `𝒢 : Sh(𝒟)`, the induced morphism
`Sh(𝒞) / f⁻¹ 𝒢 ⟶ Sh(𝒟) / 𝒢` is the generic slice-localization owner
`LeftExactAdjunction.localization` applied to `f`. -/
#check (f.localization 𝒢)

/- Companion specialization: on an object `(ℋ ⟶ 𝒢)`, the localized inverse image applies `f⁻¹`
to the structure morphism, giving `(f⁻¹ ℋ ⟶ f⁻¹ 𝒢)`. -/
#check (LeftExactAdjunction.localization_inverseImage_obj f 𝒢)

/- Companion specialization: restricting to `f⁻¹ 𝒢` and then pushing forward along the localized
morphism is canonically isomorphic to pushing forward along `f` and then restricting to `𝒢`. -/
#check (LeftExactAdjunction.localization_pushforwardStarIso f 𝒢)

end

end MorphismOfTopoiIn

end CategoryTheory

/-! ### Lemma_7_31_2 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn SheafifiedRepresentable

universe u₁ v₁

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₁} [Category.{v₁} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.31.2:
- primary domain: localization of a morphism of topoi at sheafified representables and its
  comparison with the slice-site morphism of Lemma `7.28.1`, expressed on inverse-image functors;
- sampled owner API:
  `continuous_sheafified_representable_iso`,
  `TwoSquare.overPost.rightAdjointIso`,
  `GrothendieckTopology.representableLocalizationComparison_inverseImageIso`,
  `Over.starPullbackIsoStar`,
  `LeftExactAdjunction.localization`;
- best owner abstraction: the localized morphism of topoi is already owned by
  `LeftExactAdjunction.localization`; Lemma `7.31.2` is a bridge/view statement transporting that
  owner through the representable identifications from Lemmas `7.13.5` and `7.30.5` so that its
  inverse image agrees with the slice-site inverse image from Lemma `7.28.2`;
- primitive data: a morphism of sites `u : D ⥤ C`, an object `V : D`, the representable
  identification
  `continuous_sheafified_representable_iso u JD JC V :
    h[u.obj V]^#[JC] ≅ u⁻¹(h[V]^#[JD])`,
  and the comparison equivalences
  `JC.representableLocalizationComparison (u.obj V)` and
  `JD.representableLocalizationComparison V`;
- derived API: the inverse-image comparison isomorphism below, comparing the slice-site inverse
  image from Lemma `7.28.2` with the inverse image of the localized morphism of topoi from
  Lemma `7.31.1` after transporting along the representable localization equivalences.

Source/core/bridge triage:
- `source-facing`: Lemma `7.31.2`, asserting that after identifying
  `𝒢 = h[V]^#[JD]`, `𝒡 = h[u.obj V]^#[JC] = f⁻¹ 𝒢`, and `j_𝒢 = j_V`, `j_𝒡 = j_{u(V)}`, the
  localized topos diagram of Lemma `7.31.1` is the one from Lemma `7.28.1`;
- `core/canonical`: `LeftExactAdjunction.localization` and the right-adjoint comparison owner
  `TwoSquare.overPost.rightAdjointIso`;
- `bridge/view`: the inverse-image comparison isomorphism below, transporting those owners through
  the representable localization equivalences.
-/

section

variable (u : D ⥤ C) [IsMorphismOfSites JD JC u]
variable [HasSheafify JD (Type (max u₁ v₁))]
variable [HasSheafify JC (Type (max u₁ v₁))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
variable [Limits.PreservesFiniteLimits
  (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
variable (V : D)
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
variable [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ v₁),
  (Over.forget (u.obj V)).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ v₁))]

/-- Lemma 7.31.2: after identifying the slice topoi
`Sh(C, JC) / h[u.obj V]^#[JC]` and `Sh(D, JD) / h[V]^#[JD]` with the slice sites
`Sh(C/u(V), JC.over (u.obj V))` and `Sh(D/V, JD.over V)`, and transporting the source slice along
the canonical representable isomorphism
`h[u.obj V]^#[JC] ≅ f⁻¹(h[V]^#[JD])`, the inverse image of the localized morphism of topoi from
Lemma `7.31.1` agrees with the slice-site inverse image from Lemma `7.28.2`. -/
noncomputable def representable_localization_comparison_inverseImageIso :
    u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V) ≅
      JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
          (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
        Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom := by
  let A := Type (max u₁ v₁)
  let f := u.morphismOfTopoiInOfContinuous JD JC
  let 𝒢 : Sheaf JD A := JD.sheafifiedRepresentable V
  let e := continuous_sheafified_representable_iso u JD JC V
  -- The slice-site comparison from Lemma 7.28.2 applies to `f⁻¹` because inverse-image
  -- functors of morphisms of topoi preserve finite limits, hence all binary products.
  let _ : PreservesFiniteLimits (f⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits f
  let _ : ∀ Y : Sheaf JD A, PreservesLimit (pair 𝒢 Y) (f⁻¹) := fun Y ↦ by
    infer_instance
  exact
    Functor.associator (u.sheafPullback A JD JC) (JC.overPullback A (u.obj V))
      (JC.representableLocalizationComparison (u.obj V)) ≪≫
    Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
      (JC.representableLocalizationComparison_inverseImageIso (u.obj V)) ≪≫
    Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
      (Over.starPullbackIsoStar e.hom).symm ≪≫
    (Functor.associator (u.sheafPullback A JD JC) (Over.star ((f⁻¹).obj 𝒢))
      (Over.pullback e.hom)).symm ≪≫
    Functor.isoWhiskerRight
      (TwoSquare.overPost.rightAdjointIso (f⁻¹) 𝒢).symm
      (Over.pullback e.hom) ≪≫
    Functor.associator (Over.star 𝒢) (Over.post (f⁻¹)) (Over.pullback e.hom) ≪≫
    (Functor.isoWhiskerRight
      (JD.representableLocalizationComparison_inverseImageIso V)
      (Over.post (f⁻¹) ⋙ Over.pullback e.hom)).symm ≪≫
    Functor.associator (JD.overPullback A V) (JD.representableLocalizationComparison V)
      (Over.post (f⁻¹) ⋙ Over.pullback e.hom)

-- Proof sketch: `representable_localization_comparison_inverseImageIso u V` is already a natural
-- isomorphism, so every component of its `hom` is an isomorphism.
/-- Each component of the functor-level comparison map in Lemma 7.31.2 is an isomorphism. -/
theorem representable_localization_comparison_inverseImageIso_hom_app_isIso
    (ℱ : Sheaf JD (Type (max u₁ v₁))) :
    IsIso
      (show
        ((u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
              JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
              JC.representableLocalizationComparison (u.obj V)).obj ℱ ⟶
            (JD.overPullback (Type (max u₁ v₁)) V ⋙
                JD.representableLocalizationComparison V ⋙
                ((u.morphismOfTopoiInOfContinuous JD JC).localization
                  (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
                Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom).obj ℱ)
          from ((representable_localization_comparison_inverseImageIso u V).hom.app ℱ)) := by
  -- The displayed morphism is the `ℱ`-component of a natural isomorphism.
  -- Hence it is an isomorphism by the canonical componentwise `IsIso` instance.
  simpa using
    (show IsIso (((representable_localization_comparison_inverseImageIso u V).app ℱ).hom) by
      infer_instance)

/-- Objectwise form of Lemma 7.31.2, obtained by evaluating the functor-level comparison at a
sheaf `ℱ` on `D`. -/
noncomputable def representable_localization_comparison_inverseImage_obj
    (ℱ : Sheaf JD (Type (max u₁ v₁))) :
    ((u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V)).obj ℱ) ≅
      ((JD.overPullback (Type (max u₁ v₁)) V ⋙
          JD.representableLocalizationComparison V ⋙
          ((u.morphismOfTopoiInOfContinuous JD JC).localization
            (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
          Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom).obj ℱ) := by
  simpa using (representable_localization_comparison_inverseImageIso u V).app ℱ

/-- The objectwise comparison is exactly the `ℱ`-component of the functor-level comparison
isomorphism. -/
@[simp] theorem representable_localization_comparison_inverseImage_obj_eq_app
    (ℱ : Sheaf JD (Type (max u₁ v₁))) :
    representable_localization_comparison_inverseImage_obj u V ℱ =
      (show
        ((u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
              JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
              JC.representableLocalizationComparison (u.obj V)).obj ℱ ≅
            (JD.overPullback (Type (max u₁ v₁)) V ⋙
                JD.representableLocalizationComparison V ⋙
                ((u.morphismOfTopoiInOfContinuous JD JC).localization
                  (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
                Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom).obj ℱ)
          from (representable_localization_comparison_inverseImageIso u V).app ℱ) := rfl

/-- Proposition-level companion to
`representable_localization_comparison_inverseImageIso`. -/
theorem representable_localization_comparison_agrees_with_localized_inverseImage
    :
    IsIsomorphic
      (u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V))
      (JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
          (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
        Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom) := by
  exact ⟨representable_localization_comparison_inverseImageIso u V⟩

end

end CategoryTheory

/-! ### Lemma_7_31_3 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.31.3:
- primary domain: slice-topos inverse-image functors built from a localized geometric morphism and
  a canonical pullback functor in `CategoryTheory.Over`, bundled at the strongest owner level
  available here;
- sampled owner declarations:
  `LeftExactAdjunction.localization`,
  `LeftExactAdjunction.localization_inverseImage_obj`,
  `Over.pullback`,
  `Over.pullbackComp`,
  `Over.pullbackCongr`;
- best owner abstraction:
  the chapter owner for the localized slice morphism is already
  `LeftExactAdjunction.localization`, while the additional map
  `s : ℱ ⟶ (f⁻¹).obj 𝒢` contributes only the canonical slice pullback owner `Over.pullback s`.
  The correct public surface is therefore the direct composite
  `((f.localization 𝒢).inverseImage ⋙ Over.pullback s)`, while the left exactness packaging is the
  derived canonical wrapper `LeftExactFunctor.of` and should not be given a second owner name;
- primitive data vs derived API:
  primitive data are the morphism of topoi `f`, the sheaves `𝒢`, `ℱ`, and the comparison map `s`;
  the source-facing inverse-image functor is the direct composite above, while its left-exact
  packaging, objectwise pullback formula, and base-change comparison are derived API from the
  owners above;
- source/core/bridge triage:
  `source-facing`: the localized inverse-image functor
    `((f.localization 𝒢).inverseImage ⋙ Over.pullback s) : Over 𝒢 ⥤ Over ℱ`;
  `core/canonical`: `LeftExactAdjunction.localization`, `LeftExactFunctor.of`, and `Over.pullback`;
  `bridge/view`: the underlying composite functor and its base-change comparison.

This file therefore works directly with the canonical composite
`((f.localization 𝒢).inverseImage ⋙ Over.pullback s)`, and leaves the left-exact wrapper as the
owner-level packaging supplied by `LeftExactFunctor.of` when needed.
-/

/-
Lemma 7.31.3: for a morphism of topoi `f : Sh(𝒞) ⟶ Sh(𝒟)` and a sheaf morphism
`s : ℱ ⟶ f^{-1} 𝒢`, the inverse-image functor of the induced localized morphism
`Sh(𝒞)/ℱ ⟶ Sh(𝒟)/𝒢` is the canonical composite of the localized inverse image from
Lemma 7.31.1 with the relocalization pullback from Lemma 7.30.6. Its left-exact packaging is
obtained directly by `LeftExactFunctor.of`, so no separate owner alias is introduced here.
-/
#check
  (fun
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    (s : ℱ ⟶ (f⁻¹).obj 𝒢) ↦
      show Over 𝒢 ⥤ₗ Over ℱ from
        LeftExactFunctor.of ((f.localization 𝒢).inverseImage ⋙ Over.pullback s))

-- Proof sketch: use that the localized inverse image from Lemma 7.31.1 is
-- `(f.localization 𝒢).inverseImage`, and then apply the objectwise description of
-- `Over.pullback s`.
/-- The localized inverse-image composite sends `(ℋ ⟶ 𝒢)` to the pullback
`(f^{-1} ℋ ×_{f^{-1} 𝒢} ℱ ⟶ ℱ)`. -/
@[simp] theorem localization_inverseImage_pullback_obj
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (ℋ : Over 𝒢) :
    ((f.localization 𝒢).inverseImage ⋙ Over.pullback s).obj ℋ =
      Over.mk (pullback.snd ((f⁻¹).map ℋ.hom) s) := by
  change (Over.pullback s).obj ((f.localization 𝒢).inverseImage.obj ℋ) =
      Over.mk (pullback.snd ((f⁻¹).map ℋ.hom) s)
  rw [LeftExactAdjunction.localization_inverseImage_obj]
  rfl

-- Proof sketch: this is the naturality step for the pullback-preservation comparison of `f⁻¹`
-- used in `localization_inverseImage_pullback_iso`.
private theorem localization_inverseImage_pullback_iso_naturality
    (f : MorphismOfTopoiIn JD JC)
    [PreservesFiniteLimits (f⁻¹)]
    {𝒢 𝒢' : Sheaf JD (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    {A B : Over 𝒢}
    (g : A ⟶ B) :
    ((Over.pullback b ⋙ Over.post (f⁻¹)).map g ≫
        (Over.isoMk (PreservesPullback.iso (f⁻¹) B.hom b)
          (by simp)).hom).left =
      (((Over.isoMk (PreservesPullback.iso (f⁻¹) A.hom b)
          (by simp)).hom ≫
        (Over.post (f⁻¹) ⋙ Over.pullback ((f⁻¹).map b)).map g)).left := by
  -- Compare the two morphisms into the pullback object by their two pullback projections.
  apply pullback.hom_ext
  · dsimp [Over.post, Over.pullback]
    rw [Category.assoc, pullbackComparison_comp_fst]
    rw [← Functor.map_comp, pullback.lift_fst, Functor.map_comp]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackComparison_comp_fst]
  · dsimp [Over.post, Over.pullback]
    rw [Category.assoc, pullbackComparison_comp_snd]
    rw [← Functor.map_comp, pullback.lift_snd]
    rw [Category.assoc, pullback.lift_snd, pullbackComparison_comp_snd]

-- Proof sketch: the equality `s' ≫ (f⁻¹).map b = a ≫ s` identifies the two pullback functors on
-- the nose; the dependent instance bookkeeping is discharged in this private theorem.
private theorem pullbackCongr_of_localization_square
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    {ℱ' : Sheaf JC (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ (f⁻¹).obj 𝒢')
    (hs : s' ≫ (f⁻¹).map b = a ≫ s) :
    Over.pullback (s' ≫ (f⁻¹).map b) = Over.pullback (a ≫ s) := by
  -- The commutative square identifies the two pullback functors on the nose.
  simp [hs]

-- Proof sketch: this is the pullback-preservation comparison for `f⁻¹` rewritten as a natural
-- isomorphism between slice pullback functors and localized inverse images.
private noncomputable def localization_inverseImage_pullback_iso
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    (b : 𝒢' ⟶ 𝒢) :
    Over.pullback b ⋙ (f.localization 𝒢').inverseImage ≅
      (f.localization 𝒢).inverseImage ⋙ Over.pullback ((f⁻¹).map b) := by
  -- The inverse image of a morphism of topoi is left exact, so it preserves the pullbacks
  -- governing the slice pullback functors.
  let _ : PreservesFiniteLimits (f⁻¹) := MorphismOfTopoiIn.inverseImage_preservesFiniteLimits f
  change Over.pullback b ⋙ Over.post (f⁻¹) ≅ Over.post (f⁻¹) ⋙ Over.pullback ((f⁻¹).map b)
  refine NatIso.ofComponents (fun A ↦ ?_) ?_
  · refine Over.isoMk (PreservesPullback.iso (f⁻¹) A.hom b) ?_
    simp
  · intro A B g
    apply Over.OverMorphism.ext
    exact localization_inverseImage_pullback_iso_naturality f b g

-- Proof sketch: first commute `Over.pullback b` past the localized inverse image using the
-- pullback-preservation comparison for `f⁻¹`, viewed through the objectwise formula from
-- Lemma `7.31.1`. Then compare the remaining iterated pullbacks by
-- `Over.pullbackComp`, and use `Over.pullbackCongr hs` for the equality
-- `s' ≫ (f⁻¹).map b = a ≫ s`.
/-- Base change for the localized inverse-image functor: a commutative square
`s' ≫ f^{-1}(b) = a ≫ s` induces the canonical comparison isomorphism on the corresponding slice
inverse-image functors. -/
noncomputable def localization_inverseImage_pullback_base_change_iso
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    {ℱ' : Sheaf JC (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ (f⁻¹).obj 𝒢')
    (hs : s' ≫ (f⁻¹).map b = a ≫ s) :
    Over.pullback b ⋙ (f.localization 𝒢').inverseImage ⋙ Over.pullback s' ≅
      (f.localization 𝒢).inverseImage ⋙ Over.pullback s ⋙ Over.pullback a := by
  exact
    (Functor.associator (Over.pullback b) (f.localization 𝒢').inverseImage (Over.pullback s')).symm ≪≫
      (Functor.isoWhiskerRight (localization_inverseImage_pullback_iso f b) (Over.pullback s')) ≪≫
      Functor.associator (f.localization 𝒢).inverseImage (Over.pullback ((f⁻¹).map b))
        (Over.pullback s') ≪≫
      (Functor.isoWhiskerLeft (f.localization 𝒢).inverseImage
        ((Over.pullbackComp s' ((f⁻¹).map b)).symm ≪≫
          eqToIso (pullbackCongr_of_localization_square f b a s s' hs) ≪≫
            Over.pullbackComp a s)) ≪≫
      Functor.associator (f.localization 𝒢).inverseImage (Over.pullback s) (Over.pullback a)

-- Proof sketch: this is the proposition-level companion obtained from the canonical functor
-- isomorphism above.
/-- Companion proposition-level base-change form for the localized inverse-image functor. -/
theorem localization_inverseImage_pullback_base_change
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    {ℱ' : Sheaf JC (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ (f⁻¹).obj 𝒢')
    (hs : s' ≫ (f⁻¹).map b = a ≫ s) :
    IsIsomorphic
      (Over.pullback b ⋙ (f.localization 𝒢').inverseImage ⋙ Over.pullback s')
      ((f.localization 𝒢).inverseImage ⋙ Over.pullback s ⋙ Over.pullback a) := by
  exact ⟨localization_inverseImage_pullback_base_change_iso f b a s s' hs⟩

end CategoryTheory

/-! ### Lemma_7_31_4 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn SheafifiedRepresentable

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
/-- Helper for Lemma 7.31.4: the source-side relocalization comparison identifies the slice-site
pullback along `c` with pullback in the slice topos over the induced map of sheafified
representables. -/
-- Route correction: we use the canonical relocalization comparison from Lemma `7.25.9`
-- directly, and only whisker it by the outer slice equivalence at `X`.
noncomputable def representable_localization_source_pullback_iso
    {X Y : C}
    [HasWeakSheafify JC (Type (max u₁ v₁))]
    [∀ P : (Over X)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget X).op.HasLeftKanExtension P]
    [∀ P : (Over Y)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget Y).op.HasLeftKanExtension P]
    (c : Y ⟶ X) :
    JC.overPullback (Type (max u₁ v₁)) X ⋙
        JC.overMapPullback (Type (max u₁ v₁)) c ⋙
        JC.representableLocalizationComparison Y ≅
      JC.overPullback (Type (max u₁ v₁)) X ⋙
        JC.representableLocalizationComparison X ⋙
        Over.pullback (JC.sheafifiedRepresentableMap c) := by
  -- The entire source-side comparison is already proved for relocalization in Lemma `7.25.9`.
  exact Functor.isoWhiskerLeft (JC.overPullback (Type (max u₁ v₁)) X)
    (JC.relocalization_inverse_image_over_pullback c)

/-- Helper for Lemma 7.31.4: Lemma 7.31.2 specialized to `u` and `V`, transporting the localized
inverse image at `u(V)` to the inverse image of the localization at `h[V]^#`. -/
noncomputable def representable_localization_target_inverseImageIso
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    (V : D)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget (u.obj V)).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
    [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ v₁))] :
    u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V) ≅
      JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization h[V]^#[JD]).inverseImage ⋙
        Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom := by
  -- This is exactly Lemma `7.31.2`, specialized from `JD.sheafifiedRepresentable V`
  -- to the local notation `h[V]^#[JD]`.
  simpa using representable_localization_comparison_inverseImageIso
    (JD := JD) (JC := JC) u V

/-- Helper for Lemma 7.31.4: the remaining target-side composite of pullbacks is the specialized
base-change comparison from Lemma 7.31.3. -/
noncomputable def representable_localization_target_base_change_iso
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    {V : D} {U : C} (c : U ⟶ u.obj V)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))] :
    let A := Type (max u₁ v₁)
    let f := u.morphismOfTopoiInOfContinuous JD JC
    let 𝒢 : Sheaf JD A := h[V]^#[JD]
    let a : h[U]^#[JC] ⟶ h[u.obj V]^#[JC] := JC.sheafifiedRepresentableMap c
    let e := continuous_sheafified_representable_iso u JD JC V
    ((f.localization 𝒢).inverseImage ⋙ Over.pullback e.hom ⋙ Over.pullback a) ≅
      (f.localization 𝒢).inverseImage ⋙ Over.pullback (a ≫ e.hom) := by
  let A := Type (max u₁ v₁)
  let f := u.morphismOfTopoiInOfContinuous JD JC
  let 𝒢 : Sheaf JD A := h[V]^#[JD]
  let a : h[U]^#[JC] ⟶ h[u.obj V]^#[JC] := JC.sheafifiedRepresentableMap c
  let e := continuous_sheafified_representable_iso u JD JC V
  -- The remaining target-side step is only the canonical composition law for pullback
  -- functors, with one associator to expose the two pullbacks next to each other.
  change ((f.localization 𝒢).inverseImage ⋙ Over.pullback e.hom ⋙ Over.pullback a) ≅
      (f.localization 𝒢).inverseImage ⋙ Over.pullback (a ≫ e.hom)
  exact
    Functor.associator ((f.localization 𝒢).inverseImage) (Over.pullback e.hom)
      (Over.pullback a) ≪≫
    Functor.isoWhiskerLeft ((f.localization 𝒢).inverseImage)
      (Over.pullbackComp a e.hom).symm

/-- Helper for Lemma 7.31.4: after localizing at `h[V]^#`, the extra pullback along
`h[U]^# ⟶ u⁻¹(h[V]^#)` is the base-change comparison from Lemma `7.31.3` specialized to the
canonical map induced by `c`. -/
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
  -- We follow the source proof literally: first rewrite the source through relocalization at
  -- `u(V)`, then transport across Lemma `7.31.2`, and finally package the remaining pullback by
  -- the base-change comparison from Lemma `7.31.3`.
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
      (representable_localization_source_pullback_iso (JC := JC) c)
  let targetIso :
      ((f.localization 𝒢).inverseImage ⋙ Over.pullback e.hom ⋙ Over.pullback a) ≅
        (f.localization 𝒢).inverseImage ⋙ Over.pullback (a ≫ e.hom) :=
    representable_localization_target_base_change_iso u c
  -- Compose the verified source rewrite, the representable-localization comparison from
  -- Lemma `7.31.2`, and the target-side base-change packaging.
  exact
    sourceIso ≪≫
      Functor.isoWhiskerRight
        (representable_localization_target_inverseImageIso (JD := JD) (JC := JC) u V)
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
