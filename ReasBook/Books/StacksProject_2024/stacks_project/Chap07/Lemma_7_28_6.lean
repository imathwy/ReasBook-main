import Mathlib
import Mathlib.CategoryTheory.Adjunction.Mates
import StacksProject_2024.stacks_project.Chap07.Lemma_7_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.TwoSquare
open Opposite

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

noncomputable section

namespace CategoryTheory

section

variable {C' : Type u₁} [Category.{v₁} C']
variable {C : Type u₂} [Category.{v₂} C]
variable {D' : Type u₃} [Category.{v₃} D']
variable {D : Type u₄} [Category.{v₄} D]

variable (J' : GrothendieckTopology C') (J : GrothendieckTopology C)
variable (K' : GrothendieckTopology D') (K : GrothendieckTopology D)

variable {u' : C' ⥤ D'} {v' : C' ⥤ C} {u : C ⥤ D} {v : D' ⥤ D}

variable [Functor.IsCocontinuous u J K] [Functor.IsCocontinuous u' J' K']
variable [Functor.IsContinuous v K' K] [Functor.IsContinuous v' J' J]

/-
Domain-style sampling for Lemma 7.28.6:
- primary domain: base-change comparisons for sheaf pushforward and pullback functors on sites;
- sampled owner API:
  `CatCommSq`,
  `TwoSquare`,
  `TwoSquare.GuitartExact`,
  `TwoSquare.guitartExact_iff_final`,
  `Functor.pushforwardContinuousSheafificationComparison`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.pushforwardContinuousSheafificationCompatibility`,
  `Functor.sheafPullbackCocontinuous`,
  `Functor.sheafPullbackCocontinuousAdjunction`,
  `mateEquiv`,
  `Functor.whiskeringLeftObjCompIso`;
- source-facing layer: the base-change comparison for a commutative square of site functors;
- core/canonical layer: the sheaf functor owners
  `sheafPushforwardContinuous`, `sheafPushforwardCocontinuous`, and
  `sheafPullbackCocontinuous`, with
  the `CatCommSq v' u' u v` owner for the commutative square and the associated
  `TwoSquare.GuitartExact` exactness condition on its underlying `2`-cell;
- bridge/view layer: the induced comparison `2`-cells on inverse-image functors, the comparison
  morphisms between the two composite right adjoints, and their left-adjoint mates.

Primitive data are the chosen commutative-square owner `[CatCommSq v' u' u v]`, the
continuity/cocontinuity and Kan-extension hypotheses needed to form the sheaf functor owners, and
the finality condition on the canonical owner functors
`TwoSquare.costructuredArrowRightwards (CatCommSq.iso v' u' u v).hom V'`; the equivalent
exactness hypothesis is the canonical owner property
`TwoSquare.GuitartExact (CatCommSq.iso v' u' u v).hom` via
`TwoSquare.guitartExact_iff_final`. The public statements below therefore keep the owner-level
finality Beck-Chevalley isomorphism as the main source-facing entry and treat the
`GuitartExact`-based form as a companion used to construct it; the sheafification/pushforward
bridge is reused directly from the canonical owner
`Functor.pushforwardContinuousSheafificationCompatibility`.
-/

variable [∀ (F : C'ᵒᵖ ⥤ Type w), u'.op.HasPointwiseRightKanExtension F]
variable [∀ (F : Cᵒᵖ ⥤ Type w), u.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify J' (Type w)] [HasWeakSheafify J (Type w)]

private noncomputable def site_square_inverse_image_iso
    (sq : CatCommSq v' u' u v) :
    v.sheafPushforwardContinuous (Type w) K' K ⋙
        u'.sheafPullbackCocontinuous (Type w) J' K' ≅
      u.sheafPullbackCocontinuous (Type w) J K ⋙
        v'.sheafPushforwardContinuous (Type w) J' J :=
  let leftIso :
      v.sheafPushforwardContinuous (Type w) K' K ⋙
          u'.sheafPullbackCocontinuous (Type w) J' K' ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) := by
    calc
      v.sheafPushforwardContinuous (Type w) K' K ⋙
          u'.sheafPullbackCocontinuous (Type w) J' K' ≅
        v.sheafPushforwardContinuous (Type w) K' K ⋙
          sheafToPresheaf K' (Type w) ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) := by
          exact Iso.refl _
      _ ≅ sheafToPresheaf K (Type w) ⋙
            (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
            (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
            presheafToSheaf J' (Type w) := by
          simpa using
            Functor.isoWhiskerRight
              (v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K)
              ((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
                presheafToSheaf J' (Type w))
  let middleIso :
      sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (Type w)).obj v'.op ⋙
          presheafToSheaf J' (Type w) :=
    Functor.isoWhiskerLeft
      (sheafToPresheaf K (Type w))
      (Functor.isoWhiskerRight
        ((u'.op.whiskeringLeftObjCompIso v.op).symm ≪≫
          (Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).mapIso
            ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
              (NatIso.op sq.iso.symm).symm ≪≫
              (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _)) ≪≫
          v'.op.whiskeringLeftObjCompIso u.op)
        (presheafToSheaf J' (Type w)))
  let rightIso :
      u.sheafPullbackCocontinuous (Type w) J K ⋙
          v'.sheafPushforwardContinuous (Type w) J' J ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (Type w)).obj v'.op ⋙
          presheafToSheaf J' (Type w) := by
    calc
      u.sheafPullbackCocontinuous (Type w) J K ⋙
          v'.sheafPushforwardContinuous (Type w) J' J ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
          presheafToSheaf J (Type w) ⋙
          v'.sheafPushforwardContinuous (Type w) J' J := by
          exact Iso.refl _
      _ ≅ sheafToPresheaf K (Type w) ⋙
            (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
            (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (Type w)).obj v'.op ⋙
            presheafToSheaf J' (Type w) := by
          let _ :
              IsIso (v'.pushforwardContinuousSheafificationComparison J' J) :=
            v'.pushforwardContinuousSheafificationComparison_isIso J' J
          simpa using
            (Functor.isoWhiskerLeft
              (sheafToPresheaf K (Type w))
              (Functor.isoWhiskerLeft
                ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op)
                (asIso (v'.pushforwardContinuousSheafificationComparison J' J)).symm))
  leftIso ≪≫ middleIso ≪≫ rightIso.symm

-- Proof sketch: start from the commutative square of inverse-image functors encoded by
-- `site_square_inverse_image_iso`, and take its horizontal mate across
-- `u.sheafPullbackCocontinuousAdjunction` and `u'.sheafPullbackCocontinuousAdjunction`. This
-- yields the canonical base-change morphism `g⁻¹ f_* ⟶ f'_* (g')⁻¹` in left-to-right
-- composition notation.
/-- The canonical base-change morphism attached to the commutative square of site functors. -/
private noncomputable def site_square_direct_image_inverse_image_baseChange
    (sq : CatCommSq v' u' u v) :
    u.sheafPushforwardCocontinuous (Type w) J K ⋙
        v.sheafPushforwardContinuous (Type w) K' K ⟶
      v'.sheafPushforwardContinuous (Type w) J' J ⋙
        u'.sheafPushforwardCocontinuous (Type w) J' K' :=
  (mateEquiv
      (u.sheafPullbackCocontinuousAdjunction J K)
      (u'.sheafPullbackCocontinuousAdjunction J' K')
      (site_square_inverse_image_iso J' J K' K sq).hom)

-- Proof sketch: evaluate the canonical base-change morphism on a sheaf `ℱ` and an object
-- `V' : D'` using the right-Kan-extension descriptions of the cocontinuous pushforwards. The two
-- resulting limits are indexed by `CostructuredArrow u' V'` and `CostructuredArrow u (v.obj V')`.
-- Guitart exactness of the site square is the owner abstraction packaging the needed
-- finality hypotheses uniformly.
/-- Under Guitart exactness of the site square, the canonical base-change morphism is an
isomorphism. -/
private theorem site_square_direct_image_inverse_image_baseChange_isIso_of_guitartExact
    (sq : CatCommSq v' u' u v)
    (hsq : TwoSquare.GuitartExact sq.iso.hom) :
    IsIso (site_square_direct_image_inverse_image_baseChange J' J K' K sq) := by
  let _ : TwoSquare.GuitartExact sq.iso.hom := hsq
  sorry

-- Proof sketch: `site_square_direct_image_inverse_image_baseChange` is the canonical comparison in
-- the direction `g⁻¹ f_* ⟶ f'_* (g')⁻¹`; under Guitart exactness of the site square it
-- is an isomorphism, so we package its inverse as the comparison
-- `f'_* (g')⁻¹ ≅ g⁻¹ f_*`.
/-- `GuitartExact` companion to `site_square_direct_image_inverse_image_iso`. -/
noncomputable def site_square_direct_image_inverse_image_iso_of_guitartExact
    (sq : CatCommSq v' u' u v)
    (hsq : TwoSquare.GuitartExact sq.iso.hom) :
    v'.sheafPushforwardContinuous (Type w) J' J ⋙
        u'.sheafPushforwardCocontinuous (Type w) J' K' ≅
      u.sheafPushforwardCocontinuous (Type w) J K ⋙
        v.sheafPushforwardContinuous (Type w) K' K := by
  let _ : IsIso (site_square_direct_image_inverse_image_baseChange J' J K' K sq) :=
    site_square_direct_image_inverse_image_baseChange_isIso_of_guitartExact
      J' J K' K sq hsq
  exact
    (asIso (site_square_direct_image_inverse_image_baseChange J' J K' K sq)).symm

/-- Lemma 7.28.6: for a `CatCommSq` of site functors
`C' ⥤ C`, `C' ⥤ D'`, `C ⥤ D`, and `D' ⥤ D` with `u,u'` cocontinuous and `v,v'`
continuous, if for every
`V' : D'` the canonical functor
`TwoSquare.costructuredArrowRightwards sq.iso.hom V' :
CostructuredArrow u' V' ⥤ CostructuredArrow u (v.obj V')`
is final, then direct image along `u'` after inverse image along `v'` is canonically isomorphic to
inverse image along `v` after direct image along `u`. -/
noncomputable def site_square_direct_image_inverse_image_iso
    (sq : CatCommSq v' u' u v)
    (hfinal : ∀ V' : D', (TwoSquare.costructuredArrowRightwards sq.iso.hom V').Final) :
    v'.sheafPushforwardContinuous (Type w) J' J ⋙
      u'.sheafPushforwardCocontinuous (Type w) J' K' ≅
      u.sheafPushforwardCocontinuous (Type w) J K ⋙
        v.sheafPushforwardContinuous (Type w) K' K := by
  let hsq : TwoSquare.GuitartExact sq.iso.hom :=
    (TwoSquare.guitartExact_iff_final sq.iso.hom).2 hfinal
  exact site_square_direct_image_inverse_image_iso_of_guitartExact
    J' J K' K sq hsq

-- Proof sketch: this is the defining `Iso.hom_inv_id` identity for the canonical Beck-Chevalley
-- isomorphism `site_square_direct_image_inverse_image_iso`.
/-- The canonical direct-image/inverse-image comparison isomorphism has the expected left inverse
identity. -/
theorem site_square_direct_image_inverse_image_iso_hom_inv_id
    (sq : CatCommSq v' u' u v)
    (hfinal : ∀ V' : D', (TwoSquare.costructuredArrowRightwards sq.iso.hom V').Final) :
    (site_square_direct_image_inverse_image_iso J' J K' K sq hfinal).hom ≫
        (site_square_direct_image_inverse_image_iso J' J K' K sq hfinal).inv =
      𝟙
        (v'.sheafPushforwardContinuous (Type w) J' J ⋙
          u'.sheafPushforwardCocontinuous (Type w) J' K') := sorry

end

end CategoryTheory
