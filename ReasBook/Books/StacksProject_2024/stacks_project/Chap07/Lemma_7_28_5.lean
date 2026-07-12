import Mathlib
import StacksProject_2024.Chap07.Lemma_7_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
universe u₁ u₂ v₁ v₂ t

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (V : D)

/- Domain-style sampling for Lemma 7.28.5:
- primary domain: Grothendieck topologies induced on comma-style categories, together with the
  continuous/cocontinuous functors and the induced inverse-image and direct-image functors on
  sheaves;
- sampled owner API:
  `GrothendieckTopology.over`,
  `Functor.IsContinuous`,
  `Functor.IsCocontinuous`,
  `CategoryTheory.CatCommSq`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPullbackCocontinuous`,
  `CategoryTheory.site_square_direct_image_inverse_image_iso`,
  `Functor.toOver_comp_forget`;
- source-facing layer: the site structure on `CostructuredArrow u V` whose covering sieves are
  detected after projection to `C`, the commuting square
  `CostructuredArrow.proj u V`, `CostructuredArrow.toOver u V`, `u`, `Over.forget V`, and the
  resulting comparison of inverse-image functors;
- core/canonical layer: the mathlib/project site-functor owners for continuity, cocontinuity, and
  the corresponding inverse-image and direct-image functors on sheaves;
- bridge/view: the canonical comparison square relating `CostructuredArrow.proj u V`,
  `CostructuredArrow.toOver u V`, `u`, and `Over.forget V`. The stronger Chapter 7
  Beck-Chevalley owner lives at the direct-image level, so the direct-image comparison remains
  companion API rather than replacing the weaker source-facing inverse-image square.

Primitive data here are only the covering sieves on `CostructuredArrow u V`. The continuity,
cocontinuity, the commutative square, and the sheaf-level comparison statements are derived API,
so the public refinement keeps the source-facing topology, exposes the inverse-image square at the
source hypothesis level, and treats the stronger Beck-Chevalley direct-image comparison as a
companion consequence rather than as the main public surface.
-/

local notation "j" => CostructuredArrow.proj u V
local notation "uOver" => CostructuredArrow.toOver u V

/-- The top sieve is covering for the topology on `CostructuredArrow u V` induced by the
projection to `C`. -/
-- Proof sketch: the image of the top sieve under `CostructuredArrow.proj u V` is again the top
-- sieve on the underlying object of `C`, so this is immediate from `J.top_mem`.
private theorem cocontinuousOverTopology_top_mem
    (X : CostructuredArrow u V) :
    Sieve.functorPushforward j (⊤ : Sieve X) ∈ J X.left := sorry

/-- Pulling back a covering sieve for the topology on `CostructuredArrow u V` stays covering. -/
-- Proof sketch: a morphism in `CostructuredArrow u V` pulls back the defining arrow
-- `u(U) ⟶ V`, so the pushforward of a pullback sieve along `CostructuredArrow.proj u V`
-- identifies with the pullback of the corresponding sieve in `C`, and then one applies
-- `J.pullback_stable`.
private theorem cocontinuousOverTopology_pullback_stable
    {X Y : CostructuredArrow u V} {S : Sieve Y} (f : X ⟶ Y)
    (hS : Sieve.functorPushforward j S ∈ J Y.left) :
    Sieve.functorPushforward j (S.pullback f) ∈ J X.left := sorry

/-- The transitivity axiom for the topology on `CostructuredArrow u V` follows from the
transitivity axiom on `C`. -/
-- Proof sketch: refine each object of the covering sieve on `CostructuredArrow u V` by the
-- hypothesized covering over that object, push everything forward along the projection to `C`,
-- and invoke `J.transitive`.
private theorem cocontinuousOverTopology_transitive
    {X : CostructuredArrow u V} {S R : Sieve X}
    (hS : Sieve.functorPushforward j S ∈ J X.left)
    (hR : ∀ ⦃Y : CostructuredArrow u V⦄ (f : Y ⟶ X), S f →
      Sieve.functorPushforward j (R.pullback f) ∈ J Y.left) :
    Sieve.functorPushforward j R ∈ J X.left := sorry

/-- Lemma 7.28.5 (1): the category of arrows `u(U) ⟶ V` becomes a site by declaring a sieve to be
covering exactly when its pushforward along the projection to `C` is covering for `J`. -/
def cocontinuousOverTopology : GrothendieckTopology (CostructuredArrow u V) where
  sieves X S := Sieve.functorPushforward j S ∈ J X.left
  top_mem' := cocontinuousOverTopology_top_mem J u V
  pullback_stable' _ _ _ f hS := cocontinuousOverTopology_pullback_stable J u V f hS
  transitive' _ _ hS _ hR := cocontinuousOverTopology_transitive J u V hS hR

local notation "J'" => cocontinuousOverTopology J u V

/-- Lemma 7.28.5 (2): the projection `j : {}^u_V \mathcal I ⥤ C` is continuous for the declared
site structure on `{}^u_V \mathcal I`. -/
instance cocontinuousOverProjection_isContinuous :
    Functor.IsContinuous j J' J := sorry

/-- Lemma 7.28.5 (3): the projection `j : {}^u_V \mathcal I ⥤ C` is cocontinuous for the declared
site structure on `{}^u_V \mathcal I`. -/
instance cocontinuousOverProjection_isCocontinuous :
    Functor.IsCocontinuous j J' J := sorry

/-- The forgetful functor from the costructured-arrow category to the slice category composes with
the slice forgetful functor as the projected functor `j ⋙ u`. -/
-- Proof sketch: this is the canonical strict equality `Functor.toOver_comp_forget` specialized to
-- `CostructuredArrow.toOver u V`.
private theorem cocontinuousOver_toOver_comp_forget_eq :
    uOver ⋙ Over.forget V = j ⋙ u := sorry

/-- Lemma 7.28.5 (4): if `u` is cocontinuous, then the functor
`u' : {}^u_V \mathcal I ⥤ \mathcal D / V` is cocontinuous. -/
instance cocontinuousOverToOver_isCocontinuous
    [u.IsCocontinuous J K] :
    Functor.IsCocontinuous uOver J' (K.over V) := sorry

/-- Lemma 7.28.5 (5): the functors `j`, `u'`, `u`, and `Over.forget V` form the canonical
commutative square of sites. -/
instance cocontinuousOver_square : CatCommSq j uOver u (Over.forget V) where
  iso := eqToIso (cocontinuousOver_toOver_comp_forget_eq u V)

/-- Lemma 7.28.5 (6): on sheaves of sets, the commutative square of sites induces the expected
commutative square on inverse-image functors of topoi.

In left-to-right composition notation, this is the source-facing comparison
`j_V^{-1} ⋙ (u')^{-1} ≅ u^{-1} ⋙ j^{-1}`. -/
noncomputable def cocontinuousOver_inverseImage_iso
    [u.IsCocontinuous J K]
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)] :
    K.overPullback (Type t) V ⋙
        Functor.sheafPullbackCocontinuous uOver (Type t) J' (K.over V) ≅
      u.sheafPullbackCocontinuous (Type t) J K ⋙
        Functor.sheafPushforwardContinuous j (Type t) J' J := by
  let hcomp : uOver ⋙ Over.forget V = j ⋙ u :=
    Functor.toOver_comp_forget (j ⋙ u) V (fun X ↦ X.hom)
      (fun f ↦ by simpa using CostructuredArrow.w f)
  let leftIso :
      K.overPullback (Type t) V ⋙
          Functor.sheafPullbackCocontinuous uOver (Type t) J' (K.over V) ≅
        sheafToPresheaf K (Type t) ⋙
          (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Dᵒᵖ (Type t)).obj
            ((CostructuredArrow.toOver u V ⋙ Over.forget V).op) ⋙
          presheafToSheaf J' (Type t) := by
    calc
      K.overPullback (Type t) V ⋙
          Functor.sheafPullbackCocontinuous uOver (Type t) J' (K.over V) ≅
        K.overPullback (Type t) V ⋙ sheafToPresheaf (K.over V) (Type t) ⋙
            (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ (Over V)ᵒᵖ (Type t)).obj
              (CostructuredArrow.toOver u V).op ⋙
            presheafToSheaf J' (Type t) := by
          exact Iso.refl _
      _ ≅ sheafToPresheaf K (Type t) ⋙
            (Functor.whiskeringLeft (Over V)ᵒᵖ Dᵒᵖ (Type t)).obj (Over.forget V).op ⋙
            (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ (Over V)ᵒᵖ (Type t)).obj
              (CostructuredArrow.toOver u V).op ⋙
            presheafToSheaf J' (Type t) := by
          simpa using
            (Functor.isoWhiskerRight
              ((Over.forget V).sheafPushforwardContinuousCompSheafToPresheafIso
                (Type t) (K.over V) K)
              ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ (Over V)ᵒᵖ (Type t)).obj
                (CostructuredArrow.toOver u V).op ⋙
                presheafToSheaf J' (Type t)))
      _ ≅ sheafToPresheaf K (Type t) ⋙
            (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Dᵒᵖ (Type t)).obj
              ((CostructuredArrow.toOver u V ⋙ Over.forget V).op) ⋙
            presheafToSheaf J' (Type t) := by
          exact Functor.isoWhiskerLeft _ <| Functor.isoWhiskerRight
            (Functor.whiskeringLeftObjCompIso (CostructuredArrow.toOver u V).op
              (Over.forget V).op).symm _
  let rightIso :
      u.sheafPullbackCocontinuous (Type t) J K ⋙
          Functor.sheafPushforwardContinuous j (Type t) J' J ≅
        sheafToPresheaf K (Type t) ⋙
          (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Dᵒᵖ (Type t)).obj
            ((CostructuredArrow.proj u V ⋙ u).op) ⋙
          presheafToSheaf J' (Type t) := by
    calc
      u.sheafPullbackCocontinuous (Type t) J K ⋙
          Functor.sheafPushforwardContinuous j (Type t) J' J ≅
        sheafToPresheaf K (Type t) ⋙
            (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
            presheafToSheaf J (Type t) ⋙
            Functor.sheafPushforwardContinuous j (Type t) J' J := by
          exact Iso.refl _
      _ ≅ sheafToPresheaf K (Type t) ⋙
            (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
            (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ (Type t)).obj
              (CostructuredArrow.proj u V).op ⋙
            presheafToSheaf J' (Type t) := by
          let _ :
              IsIso ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison
                J' J) :=
            (CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison_isIso J' J
          simpa using
            (Functor.isoWhiskerLeft (sheafToPresheaf K (Type t)) <|
              Functor.isoWhiskerLeft
                ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op)
                (asIso
                  ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison
                    J' J)).symm)
      _ ≅ sheafToPresheaf K (Type t) ⋙
            (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Dᵒᵖ (Type t)).obj
              ((CostructuredArrow.proj u V ⋙ u).op) ⋙
            presheafToSheaf J' (Type t) := by
          exact Functor.isoWhiskerLeft _ <| Functor.isoWhiskerRight
            (Functor.whiskeringLeftObjCompIso (CostructuredArrow.proj u V).op u.op).symm _
  exact leftIso ≪≫ eqToIso (by rw [hcomp]) ≪≫ rightIso.symm

-- Proof sketch: this is the defining `Iso.hom_inv_id` identity for the canonical comparison
-- isomorphism `cocontinuousOver_inverseImage_iso`.
/-- The canonical inverse-image comparison isomorphism has the expected left inverse identity. -/
theorem cocontinuousOver_inverseImage_iso_hom_inv_id
    [u.IsCocontinuous J K]
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)] :
    (cocontinuousOver_inverseImage_iso J K u V).hom ≫
        (cocontinuousOver_inverseImage_iso J K u V).inv =
      𝟙
        (K.overPullback (Type t) V ⋙
          Functor.sheafPullbackCocontinuous uOver (Type t) J' (K.over V)) := sorry

/-
The stronger Beck-Chevalley comparison on direct images is already owned upstream by
`site_square_direct_image_inverse_image_iso` in `Lemma_7_28_6`. This file keeps only the
source-facing inverse-image comparison above and does not duplicate that stronger owner locally.
-/

end CategoryTheory
