import Mathlib
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
import Mathlib.CategoryTheory.UnivLE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_28_2 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

noncomputable section

namespace CategoryTheory.TwoSquare.overPost

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : D ⥤ C)
variable [HasBinaryProducts C] [HasBinaryProducts D]

/- Domain-style sampling for Lemma 7.28.2:
- primary domain: localized slice functors in `CategoryTheory.Over`, with the square determined by
  product with a fixed object and postcomposition along a functor;
- sampled owner API:
  `TwoSquare.overPost`,
  `Over.star`,
  `Over.post`,
  `prodComparisonNatIso`;
- source-facing layer: the localized square attached to `u` and `V`;
- core/canonical owner: `TwoSquare.overPost u V`, whose comparison on right adjoints is supplied by
  `prodComparisonNatIso u V`;
- bridge/view: the induced natural isomorphism between the right adjoints of the vertical functors,
  recorded below as `TwoSquare.overPost.rightAdjointIso`.

Primitive data are only the functor `u`, the binary-product structures, and the family of
preservation hypotheses `∀ Y, PreservesLimit (pair V Y) u`. The localized square itself is
derived API from the owner square `TwoSquare.overPost u V`, so the correct public shape is the
induced natural isomorphism rather than a parallel local wrapper.
-/

/-- Lemma 7.28.2: if `u : \mathcal D ⥤ \mathcal C` preserves the binary products `V ⨯ Y`, then
the owner square `CategoryTheory.TwoSquare.overPost u V` induces the canonical comparison
isomorphism between the right adjoints of its vertical functors:
`Over.star V ⋙ Over.post u ≅ u ⋙ Over.star (u.obj V)`. -/
noncomputable def rightAdjointIso (V : D)
    [∀ Y, PreservesLimit (pair V Y) u] :
    Over.star V ⋙ Over.post u ≅ u ⋙ Over.star (u.obj V) :=
  NatIso.ofComponents
    (fun Y ↦
      Over.isoMk ((prodComparisonNatIso u V).app Y) <|
        by
          change prodComparison u V Y ≫ ((Over.star (u.obj V)).obj (u.obj Y)).hom =
            u.map (((Over.star V).obj Y).hom)
          rw [Over.star_obj_hom, Over.star_obj_hom]
          simpa only [prod.lift_fst] using prodComparison_fst u V Y)
    (by
      intro Y Y' f
      ext
      simpa [Over.star_map_left] using (prodComparisonNatIso u V).hom.naturality f)

-- Proof sketch: `rightAdjointIso u V` is already a natural isomorphism, so each component of its
-- `hom` is an isomorphism in the slice category.
/-- Each component of the canonical comparison `rightAdjointIso u V` is an isomorphism in the
relevant slice category. -/
theorem rightAdjointIso_hom_app_isIso (V Y : D)
    [∀ Z, PreservesLimit (pair V Z) u] :
    IsIso ((rightAdjointIso u V).hom.app Y) := by
  -- The comparison itself is a natural isomorphism, so its `hom` is an isomorphism of
  -- functors.
  have h : IsIso (rightAdjointIso u V).hom := by
    infer_instance
  -- The standard componentwise criterion now gives the desired slice isomorphism at `Y`.
  exact (NatTrans.isIso_iff_isIso_app (rightAdjointIso u V).hom).1 h Y

end

end CategoryTheory.TwoSquare.overPost

/-! ### Lemma_7_28_3 (from Chap07) -/
open CategoryTheory

universe w u₁ u₂ v₁ v₂

noncomputable section

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

variable (u : D ⥤ C) [u.IsContinuous JD JC]

variable [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]

/- Domain-style sampling for Lemma 7.28.3:
- primary domain: localized comparison functors for morphisms of sites and relocalization on slice
  sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `Functor.sheafPullbackComp'`,
  `GrothendieckTopology.overPullback`,
  `GrothendieckTopology.overMapPullback`,
  `relocalization_inverse_image_square_iso`;
- source-facing layer: the localized factorization and naturality statements attached to
  `c : U ⟶ u.obj V`;
- core/canonical owner: the sheaf functors `u.sheafPushforwardContinuous`,
  `(Over.post u).sheafPushforwardContinuous`, `JC.overPullback`, and `JC.overMapPullback`;
- bridge/view layer: the specialized comparison isomorphisms between those owner functors. This
  file should stay at that bridge layer and should not introduce a second family of comparison
  owners.

Primitive data are only the site functor `u`, the localization morphism `c`, and in part `(2)` the
commutative square `c' ≫ u.map b = a ≫ c`. The localized comparison functors themselves are
already derived from the chapter/mathlib owners above, so the refined file should recall and
specialize those owners directly rather than keep four broken chapter-local wrapper declarations.
-/

recall Functor.sheafPushforwardContinuousComp'
recall Functor.sheafPullbackComp'
recall relocalization_inverse_image_square_iso

section

variable {V : D} {U : C}
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type w, (Over.forget (u.obj V)).op.HasLeftKanExtension P]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.forget V).op.HasLeftKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify JC (Type w)]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
variable [HasWeakSheafify (JC.over U) (Type w)]
variable [HasWeakSheafify (JD.over V) (Type w)]
variable [IsMorphismOfSites JD JC u]

/- Lemma 7.28.3 (1): the source comparison
`j_U⁻¹ ⋙ f⁻¹ ≅ (f_c)⁻¹ ⋙ j_V⁻¹`
is obtained by composing the localized square of Lemma `7.28.1` with the relocalization triangle
of Lemma `7.25.8`. The file should therefore recall those owner comparisons directly rather than
keep a parallel chapter-local wrapper around their composite. -/
#check
  (fun
    (u : D ⥤ C)
    [u.IsContinuous JD JC]
    (V : D) ↦
      by
        letI : Functor.IsContinuous (Over.forget V ⋙ u) (JD.over V) JC :=
          Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
        exact
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (by rfl) : Over.post u ⋙ Over.forget (u.obj V) ≅ Over.forget V ⋙ u)
            (Type w) (JD.over V) (JC.over (u.obj V)) JC :
            JC.overPullback (Type w) (u.obj V) ⋙
                (Over.post u).sheafPushforwardContinuous (Type w)
                  (JD.over V) (JC.over (u.obj V)) ≅
              u.sheafPushforwardContinuous (Type w) JD JC ⋙
                JD.overPullback (Type w) V))

#check
  (fun (c : U ⟶ u.obj V) ↦
    (Functor.sheafPushforwardContinuousComp'
      (Over.mapForget c) (Type w) (JC.over U) (JC.over (u.obj V)) JC :
        JC.overPullback (Type w) (u.obj V) ⋙
            JC.overMapPullback (Type w) c ≅
          JC.overPullback (Type w) U))

end

section

variable {V V' : D} {U U' : C}
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [∀ P : (Over V')ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
variable [HasWeakSheafify (JC.over (u.obj V')) (Type w)]
variable (c : U ⟶ u.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ u.obj V') (hcomm : c' ≫ u.map b = a ≫ c)

/- Lemma 7.28.3 (2): naturality in `c` is exactly the relocalization square owner specialized to
the commutative square `c' ≫ u.map b = a ≫ c`; no separate chapter-local comparison is needed. -/
#check
  (relocalization_inverse_image_square_iso
    JC a c' c (u.map b) hcomm.symm :
      JC.overMapPullback (Type w) c ⋙
          JC.overMapPullback (Type w) a ≅
        JC.overMapPullback (Type w) (u.map b) ⋙
          JC.overMapPullback (Type w) c')

end

end

end CategoryTheory

/-! ### Lemma_7_28_4 (from Chap07) -/
universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (U : C)

/- Domain-style sampling for Lemma 7.28.4:
- primary domain: localized cocontinuous functors between slice sites and their induced
  direct-image functors on sheaf categories;
- sampled owner API:
  `Functor.IsCocontinuous`,
  `GrothendieckTopology.over`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousComp`,
  `Functor.sheafPushforwardCocontinuousComp'`;
- source/core/bridge triage:
  `source-facing`: cocontinuity of the induced slice functor `Over.post u`;
  `core/canonical`: `Functor.IsCocontinuous` together with
  `Functor.sheafPushforwardCocontinuous`;
- bridge/view: the slice specialization of `Functor.sheafPushforwardCocontinuousComp'` for
  `Over.post u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u`.

Primitive data are only the sites `J`, `K`, the cocontinuous functor `u`, and the object `U`.
The sheaf-level comparison square is derived API from the owner comparison theorems of
Lemma `7.21.2`, so the refined file keeps the localized cocontinuity instance and reuses that
canonical bridge directly, treating the right-hand composite Kan-extension hypothesis as derived
data from the left-hand one rather than exporting any separate local wrapper.
-/

-- Proof sketch: pull a covering sieve on `Over (u.obj U)` back along `Over.post u`; under the
-- equivalence between sieves on a slice object and sieves on its domain, this reduces to pulling
-- back the corresponding covering sieve in `D` along `u`, and then transporting the resulting
-- cover back to the slice site.
/-- Helper for Lemma 7.28.4: after transporting sieves on slice objects to sieves on their
domains, pulling back along `Over.post u` becomes pulling back along `u`. -/
lemma overEquiv_functorPullback_post {Y : Over U} (S : Sieve ((Over.post u).obj Y)) :
    Sieve.overEquiv Y (S.functorPullback (Over.post u)) =
      (Sieve.overEquiv ((Over.post u).obj Y) S).functorPullback u := by
  ext Z g
  let e : (Over.post u).obj (Over.mk (g ≫ Y.hom)) ⟶
      Over.mk (u.map g ≫ ((Over.post u).obj Y).hom) :=
    Over.homMk (𝟙 (u.obj Z)) (by simp)
  let eInv : Over.mk (u.map g ≫ ((Over.post u).obj Y).hom) ⟶
      (Over.post u).obj (Over.mk (g ≫ Y.hom)) :=
    Over.homMk (𝟙 (u.obj Z)) (by simp)
  have heq :
      (Over.post u).map (Over.homMk (U := Over.mk (g ≫ Y.hom)) g rfl) =
        e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl := by
    -- The image of `g` under `Over.post u` differs from the canonical lift of `u.map g`
    -- only by the evident identity isomorphism on the source object.
    apply CategoryTheory.CommaMorphism.ext
    · change u.map g = (𝟙 (u.obj Z)) ≫ u.map g
      simp
    · simp
  constructor
  · intro hg
    -- Rewrite slice membership as membership in the pulled-back sieve on the base category.
    rw [Sieve.overEquiv_iff] at hg
    change S ((Over.post u).map (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y)) at hg
    have hg' : S (e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl) := by
      convert hg using 1
      exact heq.symm
    have hdown :
        S (eInv ≫ e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl) :=
      S.downward_closed hg' eInv
    change (Sieve.overEquiv ((Over.post u).obj Y) S) (u.map g)
    rw [Sieve.overEquiv_iff]
    convert hdown using 1
    apply CategoryTheory.CommaMorphism.ext
    · change u.map g = (𝟙 (u.obj Z)) ≫ 𝟙 (u.obj Z) ≫ u.map g
      simp
    · simp
  · intro hg
    -- Conversely, precompose the canonical lift of `u.map g` by the same identity arrow.
    rw [Sieve.overEquiv_iff]
    change (Sieve.overEquiv ((Over.post u).obj Y) S) (u.map g) at hg
    rw [Sieve.overEquiv_iff] at hg
    change S ((Over.post u).map (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y))
    have hg' : S (e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl) :=
      S.downward_closed hg e
    convert hg' using 1

/-- Helper for Lemma 7.28.4: a covering sieve on `u.obj Y.left` lifts to the pullback covering
for the induced slice functor `Over.post u`. -/
lemma over_post_cover_lift [u.IsCocontinuous J K] {Y : Over U}
    {S : Sieve ((Over.post u).obj Y)}
    (hS : Sieve.overEquiv ((Over.post u).obj Y) S ∈ K (u.obj Y.left)) :
    Sieve.overEquiv Y (S.functorPullback (Over.post u)) ∈ J Y.left := by
  -- After the transport lemma, the textbook covering argument is exactly `u.cover_lift`.
  rw [overEquiv_functorPullback_post (u := u) (U := U)]
  exact u.cover_lift J K hS

/-- Lemma 7.28.4: a cocontinuous functor between sites induces a cocontinuous functor on the
corresponding localized sites. -/
instance overPost_isCocontinuous [u.IsCocontinuous J K] :
    Functor.IsCocontinuous (Over.post u) (J.over U) (K.over (u.obj U)) where
  cover_lift {Y} S hS := by
    -- Transport the slice covering condition to the base sites, apply cocontinuity of `u`,
    -- and transport the lifted cover back to the slice site.
    rw [K.mem_over_iff] at hS
    rw [J.mem_over_iff]
    exact over_post_cover_lift (J := J) (K := K) (u := u) (U := U) hS

section

variable [u.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over (u.obj U))ᵒᵖ ⥤ Type w,
  (Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.post u).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w,
  (Over.post u ⋙ Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F]

/- Lemma 7.28.4: on sheaves of sets, the localized direct-image square is exactly the slice
specialization of the owner comparison theorems
`Functor.sheafPushforwardCocontinuousComp'` and
`Functor.sheafPushforwardCocontinuousComp`. The right-hand composite
`(Over.forget U ⋙ u).op` has pointwise right Kan extensions by transport across the definitional
identity `Over.post u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u`, so no local wrapper is
needed. -/
#check
  (by
    letI : Functor.IsCocontinuous (Over.forget U ⋙ u) (J.over U) K :=
      isCocontinuous_comp (Over.forget U) u (J.over U) J
    letI : ∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U ⋙ u).op.HasPointwiseRightKanExtension F := by
      intro F
      change (Over.post u ⋙ Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F
      infer_instance
    exact
      (Functor.sheafPushforwardCocontinuousComp'
          (J.over U) (K.over (u.obj U)) K (Over.post u) (Over.forget (u.obj U))
          (show Over.post u ⋙ Over.forget (u.obj U) ≅ Over.forget U ⋙ u from Iso.refl _) ≪≫
        (Functor.sheafPushforwardCocontinuousComp
          (J.over U) J K (Over.forget U) u).symm :
        (Over.post u).sheafPushforwardCocontinuous (Type w) (J.over U) (K.over (u.obj U)) ⋙
            (Over.forget (u.obj U)).sheafPushforwardCocontinuous (Type w)
              (K.over (u.obj U)) K ≅
          (Over.forget U).sheafPushforwardCocontinuous (Type w) (J.over U) J ⋙
            u.sheafPushforwardCocontinuous (Type w) J K))

end

end

end CategoryTheory
