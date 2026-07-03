import Mathlib
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
import Mathlib.CategoryTheory.UnivLE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_28_5 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
universe u₁ u₂ u₃ v₁ v₂ v₃ t w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

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

/-- Helper for Lemma 7.28.5: composing type-valued sheaves with any ambient `ULift` functor
preserves the sheaf condition on the site in use. -/
private instance uliftFunctor_hasSheafCompose_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) where
  isSheaf P hP := by
    -- Reduce to the concrete type-valued sheaf condition where `ULift` is stable.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := L)
      ((isSheaf_iff_isSheaf_of_type L P).1 hP)

/-- The top sieve is covering for the topology on `CostructuredArrow u V` induced by the
projection to `C`. -/
-- Proof sketch: the image of the top sieve under `CostructuredArrow.proj u V` is again the top
-- sieve on the underlying object of `C`, so this is immediate from `J.top_mem`.
private theorem cocontinuousOverTopology_top_mem
    (X : CostructuredArrow u V) :
    Sieve.functorPushforward j (⊤ : Sieve X) ∈ J X.left := by
  -- The induced topology declares covers exactly by pushforward along `j`.
  rw [Sieve.functorPushforward_top]
  exact J.top_mem X.left

/-- Pulling back a covering sieve for the topology on `CostructuredArrow u V` stays covering. -/
-- Proof sketch: a morphism in `CostructuredArrow u V` pulls back the defining arrow
-- `u(U) ⟶ V`, so the pushforward of a pullback sieve along `CostructuredArrow.proj u V`
-- identifies with the pullback of the corresponding sieve in `C`, and then one applies
-- `J.pullback_stable`.
private theorem cocontinuousOverTopology_pullback_stable
    {X Y : CostructuredArrow u V} {S : Sieve Y} (f : X ⟶ Y)
    (hS : Sieve.functorPushforward j S ∈ J Y.left) :
    Sieve.functorPushforward j (S.pullback f) ∈ J X.left := by
  -- Any arrow in the pullback of the pushed-forward sieve lifts to the pullback sieve itself.
  have hle :
      Sieve.pullback f.left (Sieve.functorPushforward j S) ≤
        Sieve.functorPushforward j (Sieve.pullback f S) := by
    intro W k hk
    rcases hk with ⟨Z, g, i, hg, hki⟩
    have hki' : k ≫ f.left = i ≫ g.left := by
      simpa using hki
    let W' : CostructuredArrow u V := CostructuredArrow.mk (u.map k ≫ X.hom)
    let hX : W' ⟶ X := CostructuredArrow.homMk k
    have hZw : u.map i ≫ Z.hom = W'.hom := by
      have hwg : u.map i ≫ Z.hom = u.map (i ≫ g.left) ≫ Y.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun t => u.map i ≫ t) (CostructuredArrow.w g).symm
      have hwf : u.map (k ≫ f.left) ≫ Y.hom = u.map k ≫ X.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun t => u.map k ≫ t) (CostructuredArrow.w f)
      have hmid' : u.map (i ≫ g.left) ≫ Y.hom = u.map (k ≫ f.left) ≫ Y.hom := by
        rw [hki'.symm]
      exact (hwg.trans hmid').trans (by simpa [W'] using hwf)
    let hZ : W' ⟶ Z := CostructuredArrow.homMk i hZw
    have hpull : S.pullback f hX := by
      have hcomp : hX ≫ f = hZ ≫ g := by
        ext
        exact hki'
      change S (hX ≫ f)
      rw [hcomp]
      exact S.downward_closed hg hZ
    simpa [hX] using
      (Sieve.image_mem_functorPushforward (F := j) (R := S.pullback f) hpull)
  exact J.superset_covering hle (J.pullback_stable f.left hS)

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
    Sieve.functorPushforward j R ∈ J X.left := by
  -- Refine the pushed-forward cover one arrow at a time and reduce to `J.transitive`.
  apply J.transitive hS
  rintro Y _ ⟨Z, g, i, hg, rfl⟩
  have hcover :
      Sieve.pullback i (Sieve.pullback g.left (Sieve.functorPushforward j R)) ∈ J Y := by
    apply J.pullback_stable i
    refine J.superset_covering (Sieve.functorPushforward_pullback_le (F := j) g R) (hR g hg)
  simpa [Sieve.pullback_comp] using hcover

/-- Lemma 7.28.5 (1): the category of arrows `u(U) ⟶ V` becomes a site by declaring a sieve to be
covering exactly when its pushforward along the projection to `C` is covering for `J`. -/
def cocontinuousOverTopology : GrothendieckTopology (CostructuredArrow u V) where
  sieves X S := Sieve.functorPushforward j S ∈ J X.left
  top_mem' := cocontinuousOverTopology_top_mem J u V
  pullback_stable' _ _ _ f hS := cocontinuousOverTopology_pullback_stable J u V f hS
  transitive' _ _ hS _ hR := cocontinuousOverTopology_transitive J u V hS hR

local notation "J'" => cocontinuousOverTopology J u V

/-- Helper for Lemma 7.28.5: covers for the induced topology on `CostructuredArrow u V` are
already defined by pushforward along the projection `j`. -/
private theorem cocontinuousOverProjection_coverPreserving :
    CoverPreserving J' J j where
  cover_preserve hS := hS

/-- Helper for Lemma 7.28.5: the projection `j` preserves compatible families because a common
comparison object can be built directly in `CostructuredArrow u V`. -/
private theorem cocontinuousOverProjection_compatiblePreserving :
    CompatiblePreserving J j where
  compatible {ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : CostructuredArrow u V := CostructuredArrow.mk (u.map f₁ ≫ Y₁.hom)
    -- The equality in `C` forces the two structure maps to `V` to agree.
    have hw_base : u.map f₂ ≫ Y₂.hom = u.map f₁ ≫ Y₁.hom := by
      have hleft : f₂ ≫ g₂.left = f₁ ≫ g₁.left := by
        simpa using h.symm
      have hw₂ : u.map f₂ ≫ Y₂.hom = u.map (f₂ ≫ g₂.left) ≫ Z.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun k => u.map f₂ ≫ k) (CostructuredArrow.w g₂).symm
      have hmid : u.map (f₂ ≫ g₂.left) ≫ Z.hom = u.map (f₁ ≫ g₁.left) ≫ Z.hom := by
        simpa using congrArg (fun k => u.map k ≫ Z.hom) hleft
      have hw₁ : u.map (f₁ ≫ g₁.left) ≫ Z.hom = u.map f₁ ≫ Y₁.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun k => u.map f₁ ≫ k) (CostructuredArrow.w g₁)
      exact hw₂.trans (hmid.trans hw₁)
    have hw : u.map f₂ ≫ Y₂.hom = W'.hom := by
      simpa [W'] using hw_base
    let g₁' : W' ⟶ Y₁ := CostructuredArrow.homMk f₁
    let g₂' : W' ⟶ Y₂ := CostructuredArrow.homMk f₂ hw
    -- Compatibility in the comma category reduces to the original equality in `C`.
    have hcomp : g₁' ≫ g₁ = g₂' ≫ g₂ := by
      ext
      exact h
    simpa [g₁', g₂'] using hx g₁' g₂' hg₁ hg₂ hcomp

/-- Helper for Lemma 7.28.5: every arrow into `X.left` lifts canonically to an arrow into `X` in
the costructured-arrow category. -/
private theorem cocontinuousOverProjection_le_pushforward_functorPullback
    (X : CostructuredArrow u V) (S : Sieve X.left) :
    S ≤ Sieve.functorPushforward j (Sieve.functorPullback j S) := by
  intro Y f hf
  let Y' : CostructuredArrow u V := CostructuredArrow.mk (u.map f ≫ X.hom)
  have hmem : Sieve.functorPullback j S (CostructuredArrow.homMk f : Y' ⟶ X) := by
    simpa using hf
  -- The lifted arrow maps back to the original arrow under `j`.
  simpa using
    (Sieve.image_mem_functorPushforward (F := j) (R := Sieve.functorPullback j S) hmem)

/-- Lemma 7.28.5 (2): the projection `j : {}^u_V \mathcal I ⥤ C` is continuous for the declared
site structure on `{}^u_V \mathcal I`. -/
instance cocontinuousOverProjection_isContinuous :
    Functor.IsContinuous j J' J := by
  -- Continuity follows from the induced-cover definition plus compatibility preservation.
  exact Functor.isContinuous_of_coverPreserving
    (cocontinuousOverProjection_compatiblePreserving (J := J) (u := u) (V := V))
    (cocontinuousOverProjection_coverPreserving (J := J) (u := u) (V := V))

/-- Lemma 7.28.5 (3): the projection `j : {}^u_V \mathcal I ⥤ C` is cocontinuous for the declared
site structure on `{}^u_V \mathcal I`. -/
instance cocontinuousOverProjection_isCocontinuous :
    Functor.IsCocontinuous j J' J where
  cover_lift {X} S hS := by
    -- Every base arrow lifts to an arrow in `CostructuredArrow u V`, so covers lift along `j`.
    change Sieve.functorPushforward j (Sieve.functorPullback j S) ∈ J X.left
    exact J.superset_covering
      (cocontinuousOverProjection_le_pushforward_functorPullback (u := u) (V := V) X S)
      hS

/-- The forgetful functor from the costructured-arrow category to the slice category composes with
the slice forgetful functor as the projected functor `j ⋙ u`. -/
-- Proof sketch: this is the canonical strict equality `Functor.toOver_comp_forget` specialized to
-- `CostructuredArrow.toOver u V`.
private theorem cocontinuousOver_toOver_comp_forget_eq :
    uOver ⋙ Over.forget V = j ⋙ u := by
  -- This is the canonical strict equality for `Functor.toOver`.
  exact Functor.toOver_comp_forget (j ⋙ u) V (fun X ↦ X.hom)
    (fun f ↦ by simpa using CostructuredArrow.w f)

/-- Helper for Lemma 7.28.5: after pulling a sieve on `Over V` back along `uOver`, pushing it
forward along `j` lands inside the pullback along `u` of the corresponding base sieve on `D`. -/
private theorem cocontinuousOverToOver_pushforward_pullback_le
    (X : CostructuredArrow u V) (S : Sieve ((CostructuredArrow.toOver u V).obj X)) :
    Sieve.functorPullback u
        (Sieve.overEquiv ((CostructuredArrow.toOver u V).obj X) S) ≤
      Sieve.functorPushforward j (Sieve.functorPullback (CostructuredArrow.toOver u V) S) := by
  intro Y f hf
  change (Sieve.overEquiv ((CostructuredArrow.toOver u V).obj X) S) (u.map f) at hf
  rw [Sieve.overEquiv_iff] at hf
  let Y' : CostructuredArrow u V := CostructuredArrow.mk (u.map f ≫ X.hom)
  have hpull :
      Sieve.functorPullback (CostructuredArrow.toOver u V) S
        (CostructuredArrow.homMk f : Y' ⟶ X) := by
    change S ((CostructuredArrow.toOver u V).map (CostructuredArrow.homMk f : Y' ⟶ X))
    simpa using hf
  -- The lifted arrow in `CostructuredArrow u V` maps back to the original base arrow.
  simpa using
    (Sieve.image_mem_functorPushforward
      (F := j) (R := Sieve.functorPullback (CostructuredArrow.toOver u V) S) hpull)

/-- Lemma 7.28.5 (4): if `u` is cocontinuous, then the functor
`u' : {}^u_V \mathcal I ⥤ \mathcal D / V` is cocontinuous. -/
instance cocontinuousOverToOver_isCocontinuous
    [u.IsCocontinuous J K] :
    Functor.IsCocontinuous uOver J' (K.over V) where
  cover_lift {X} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS
    -- Route correction: prove cocontinuity through the base sieve `Sieve.overEquiv _ S` on `D`,
    -- then compare it with the pushed-forward pullback along `j`.
    change Sieve.functorPushforward j (Sieve.functorPullback uOver S) ∈ J X.left
    exact J.superset_covering
      (cocontinuousOverToOver_pushforward_pullback_le (u := u) (V := V) X S)
      (u.cover_lift J K hS)

/-- Lemma 7.28.5 (5): the functors `j`, `u'`, `u`, and `Over.forget V` form the canonical
commutative square of sites. -/
instance cocontinuousOver_square : CatCommSq j uOver u (Over.forget V) where
  iso := eqToIso (cocontinuousOver_toOver_comp_forget_eq u V)

/-- Helper for Lemma 7.28.5: the sectionwise source equivalence for part `(5)` is the canonical
equivalence between the costructured-arrow category of `uOver` over `Y` and the costructured-arrow
category of `u` over `Y.left`. -/
private noncomputable def cocontinuousOver_costructuredArrow_toOver_equivalence
    (Y : Over V) :
    CostructuredArrow uOver Y ≌ CostructuredArrow u Y.left :=
  CostructuredArrow.costructuredArrowToOverEquivalence u Y

/-- Helper for Lemma 7.28.5: restricting a sheaf along `j` evaluates on an object of
`CostructuredArrow u V` by forgetting to its underlying object of `C`. -/
private theorem cocontinuousOver_projection_restrict_obj
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf J (Type t)) (X : CostructuredArrow u V) :
    (((Functor.sheafPushforwardContinuous j (Type t) J' J).obj ℱ).obj.obj (Opposite.op X)) =
      ℱ.obj.obj (Opposite.op X.left) := by
  -- Continuous pushforward along `j` is restriction of the underlying presheaf along `j.op`.
  rfl

/-- Helper for Lemma 7.28.5: after restricting a sheaf on `D` along `u`, the only nontrivial
comparison on the `j`-side is the continuous sheafification map. -/
private noncomputable def cocontinuousOver_projection_specializedComparison
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)] :
    sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ (Type t)).obj
          (CostructuredArrow.proj u V).op ⋙
        presheafToSheaf J' (Type t) ⟶
      sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        presheafToSheaf J (Type t) ⋙
        Functor.sheafPushforwardContinuous j (Type t) J' J :=
  Functor.whiskerLeft
    (sheafToPresheaf K (Type t) ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op)
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J)

/-- Helper for Lemma 7.28.5: precomposing the source-facing `j`-comparison with `toSheafify`
recovers whiskering of the sheafification unit. -/
private lemma cocontinuousOver_projection_comparison_precompose_toSheafify_app
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t)
    (X : (CostructuredArrow u V)ᵒᵖ) :
    ((toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)).app X ≫
        ((sheafToPresheaf J' (Type t)).map
          (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
            F)).app X) =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)).app X := by
  -- This is the defining `sheafifyLift` relation for the source-facing comparison, evaluated at `X`.
  change
    ((toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)).app X ≫
        (sheafifyLift J'
          (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F))
          ((presheafToSheaf J (Type t) ⋙
              (CostructuredArrow.proj u V).sheafPushforwardContinuous (Type t) J' J).obj F).property).app
            X) =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)).app X
  exact
    congrArg (fun η => η.app X)
      (toSheafify_sheafifyLift J'
        (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F))
        ((presheafToSheaf J (Type t) ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous (Type t) J' J).obj F).property)

/-- Helper for Lemma 7.28.5: the source-facing `j`-comparison is characterized globally by the
expected `toSheafify` factorization. -/
private lemma cocontinuousOver_projection_comparison_precompose_toSheafify
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
        (sheafToPresheaf J' (Type t)).map
          (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
            F) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F) := by
  -- Compare the two owner morphisms pointwise on each object of `{}^u_V \mathcal I`.
  ext X x
  exact congrFun
    (cocontinuousOver_projection_comparison_precompose_toSheafify_app
      (J := J) (u := u) (V := V) F X)
    x

/-- Helper for Lemma 7.28.5: forgetting the image of a sheaf morphism under continuous
pushforward along `j` is just whiskering its underlying presheaf morphism by `j.op`. -/
private lemma cocontinuousOver_projection_sheafPushforward_map_app_eq_whiskerLeft
    {A : Type*} [Category A]
    [HasWeakSheafify J A]
    [HasWeakSheafify J' A]
    {ℱ 𝒢 : Sheaf J A}
    (α : ℱ ⟶ 𝒢)
    (X : (CostructuredArrow u V)ᵒᵖ) :
    ((sheafToPresheaf J' A).map
        (((CostructuredArrow.proj u V).sheafPushforwardContinuous A J' J).map α)).app X =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op
        ((sheafToPresheaf J A).map α)).app X := by
  -- Continuous pushforward along `j` is defined by whiskering the underlying presheaf map.
  rfl

/-- Helper for Lemma 7.28.5: specializing the `j`-comparison precompose identity to a sheaf on
`D` rewrites the source component entirely in terms of the restricted presheaf `u.op ⋙ ℱ.1`. -/
private lemma cocontinuousOver_projection_specializedComparison_precompose_toSheafify_app
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t))
    (X : (CostructuredArrow u V)ᵒᵖ) :
    let F : Cᵒᵖ ⥤ Type t :=
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ)
    ((toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)).app X ≫
        ((sheafToPresheaf J' (Type t)).map
          ((cocontinuousOver_projection_specializedComparison
            (J := J) (K := K) (u := u) (V := V)).app ℱ)).app X) =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)).app X := by
  -- Unfold only the specialized comparison and reuse the generic precompose identity.
  dsimp [cocontinuousOver_projection_specializedComparison]
  simpa using
    cocontinuousOver_projection_comparison_precompose_toSheafify_app
      (J := J) (u := u) (V := V)
      (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ))
      X

/-- Helper for Lemma 7.28.5: the specialized `j`-comparison is characterized owner-level by the
expected `toSheafify` factorization on the restricted presheaf `u.op ⋙ ℱ.1`. -/
private lemma cocontinuousOver_projection_specializedComparison_precompose_toSheafify
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t)) :
    let F : Cᵒᵖ ⥤ Type t :=
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ)
    toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
        (sheafToPresheaf J' (Type t)).map
          ((cocontinuousOver_projection_specializedComparison
            (J := J) (K := K) (u := u) (V := V)).app ℱ) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F) := by
  let F : Cᵒᵖ ⥤ Type t :=
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
      ((sheafToPresheaf K (Type t)).obj ℱ)
  -- Compare the two owner maps pointwise on each object of `{}^u_V \mathcal I`.
  ext X x
  exact congrFun
    (cocontinuousOver_projection_specializedComparison_precompose_toSheafify_app
      (J := J) (K := K) (u := u) (V := V) ℱ X)
    x

/-- Helper for Lemma 7.28.5: precomposing by the `J'`-sheafification unit preserves an
owner-level forgotten equality of morphisms. -/
private lemma cocontinuousOver_projection_toSheafify_comp_eq_of_eq
    [HasWeakSheafify J' (Type t)]
    {A B : (CostructuredArrow u V)ᵒᵖ ⥤ Type t}
    {f g : ((presheafToSheaf J' (Type t)).obj A).1 ⟶ B}
    (h : f = g) :
    toSheafify J' A ≫ f = toSheafify J' A ≫ g := by
  -- Precomposition by the sheafification unit preserves the normalized owner equality.
  simp [h]

/-- Helper for Lemma 7.28.5: after forgetting to presheaves, the specialized comparison at `X`
is definitionally the owner comparison for `j` evaluated on the restricted presheaf `u.op ⋙ ℱ.1`.
-/
private lemma cocontinuousOver_projection_specializedComparison_underlying_app_eq_projectionComparison
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t))
    (X : CostructuredArrow u V) :
    let F : Cᵒᵖ ⥤ Type t :=
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ)
    (((sheafToPresheaf J' (Type t)).map
        ((cocontinuousOver_projection_specializedComparison
          (J := J) (K := K) (u := u) (V := V)).app ℱ)).app (Opposite.op X)) =
      (((sheafToPresheaf J' (Type t)).map
      (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
          F)).app (Opposite.op X)) := by
  -- The specialized comparison is definitionally the whiskered `j`-comparison on `F`.
  rfl

/-- Helper for Lemma 7.28.5: the source-proof indexing category over `X` is equivalent to the
comma category of arrows into `X` inside `{}^u_V \mathcal I`. -/
private noncomputable def cocontinuousOver_projection_index_equivalence
    (X : C) :
    CostructuredArrow (Over.forget X ⋙ u) V ≌ CostructuredArrow j X :=
  { functor :=
      { obj := fun Y ↦
          let Z : CostructuredArrow u V := CostructuredArrow.mk Y.hom
          CostructuredArrow.mk (S := j) (Y := Z) Y.left.hom
        map := fun {Y₁ Y₂} φ ↦
          -- The source proof forgets only the `Over X` packaging and keeps the same
          -- underlying arrows `u(Y) ⟶ V` and `Y ⟶ X`.
          let φleft :
              (CostructuredArrow.mk (S := u) Y₁.hom : CostructuredArrow u V) ⟶
                (CostructuredArrow.mk (S := u) Y₂.hom : CostructuredArrow u V) :=
            CostructuredArrow.homMk φ.left.left (by
              simpa using CostructuredArrow.w φ)
          CostructuredArrow.homMk φleft (by
            show φ.left.left ≫ Y₂.left.hom = Y₁.left.hom
            simpa using Over.w φ.left)
        map_id := by
          intro Y
          apply CostructuredArrow.ext
          apply CostructuredArrow.ext
          simp
        map_comp := by
          intro Y₁ Y₂ Y₃ φ ψ
          apply CostructuredArrow.ext
          apply CostructuredArrow.ext
          simp }
    inverse :=
      { obj := fun Y ↦
          let Z : Over X := Over.mk Y.hom
          CostructuredArrow.mk (S := Over.forget X ⋙ u) (Y := Z) Y.left.hom
        map := fun {Y₁ Y₂} φ ↦
          -- Conversely, the arrow into `X` repackages the left object as an object of `Over X`.
          let φleft :
              Over.mk Y₁.hom ⟶ Over.mk Y₂.hom :=
            Over.homMk φ.left.left (by
              simpa using CostructuredArrow.w φ)
          CostructuredArrow.homMk φleft (by
            show u.map φ.left.left ≫ Y₂.left.hom = Y₁.left.hom
            simpa using CostructuredArrow.w φ.left)
        map_id := by
          intro Y
          apply CostructuredArrow.ext
          apply Over.OverMorphism.ext
          simp
        map_comp := by
          intro Y₁ Y₂ Y₃ φ ψ
          apply CostructuredArrow.ext
          apply Over.OverMorphism.ext
          simp }
    unitIso := NatIso.ofComponents (fun Y ↦
      -- Both composites are definitionally the identity after forgetting the comma packaging.
      let e : Y.left ≅ Over.mk Y.left.hom :=
        Over.isoMk (Iso.refl _) (by simp)
      CostructuredArrow.isoMk e (by simp [e]))
    counitIso := NatIso.ofComponents (fun Y ↦
      -- The target-side composite keeps the same object of `{}^u_V \mathcal I` and the same
      -- structure map to `X`, so only the nested comma packaging changes.
      let e : Y.left ≅ (CostructuredArrow.mk (S := u) Y.left.hom : CostructuredArrow u V) :=
        CostructuredArrow.isoMk (Iso.refl _) (by simp)
      CostructuredArrow.isoMk e (by simp [e])) }

/-- Helper for Lemma 7.28.5: the structured-arrow category used for pointwise right Kan
extensions is the opposite of the source-proof comma category. -/
private noncomputable def cocontinuousOver_projection_structuredArrow_equivalence
    (X : C) :
    StructuredArrow (Opposite.op X) (CostructuredArrow.proj u V).op ≌
      (CostructuredArrow (Over.forget X ⋙ u) V)ᵒᵖ :=
  (((cocontinuousOver_projection_index_equivalence (u := u) (V := V) X).op).trans
    (costructuredArrowOpEquivalence (CostructuredArrow.proj u V) X)).symm

/-- Helper for Lemma 7.28.5: after identifying the sectionwise structured-arrow category with the
source-proof comma category, the projection functor is exactly the opposite of the canonical
precomposition functor `CostructuredArrow.pre`. -/
private noncomputable def cocontinuousOver_projection_structuredArrow_proj_iso
    (X : C) :
    StructuredArrow.proj (Opposite.op X) (CostructuredArrow.proj u V).op ≅
      (cocontinuousOver_projection_structuredArrow_equivalence
        (u := u) (V := V) X).functor ⋙
        (CostructuredArrow.pre (Over.forget X) u V).op := by
  -- The explicit equivalence was chosen so that the textbook projection becomes definitional.
  exact Iso.refl _

/-- Helper for Lemma 7.28.5: each sectionwise structured-arrow diagram defining the pointwise
right Kan extension of `j.op` has a limit in the lifted universe where the source indexing
category is small enough for `Type`-limits. -/
private theorem cocontinuousOver_projection_structuredArrow_hasLimit_lifted
    (X : C) (P : (CostructuredArrow u V)ᵒᵖ ⥤ Type (max (max (max (max t u₁) u₂) v₁) v₂)) :
    HasLimit (StructuredArrow.proj (Opposite.op X) (CostructuredArrow.proj u V).op ⋙ P) := by
  -- Route correction: compute the pointwise right Kan extension in the lifted universe, where
  -- the source indexing category from the textbook is small enough for the ambient `Type`.
  let e :=
    Functor.isoWhiskerRight
      (cocontinuousOver_projection_structuredArrow_proj_iso
        (u := u) (V := V) X) P
  -- After transporting along the explicit source-proof identification, the remaining diagram is
  -- an ordinary large-`Type` diagram and its limit is provided by the ambient `Type` instance.
  have htransport :
      HasLimit
        ((cocontinuousOver_projection_structuredArrow_equivalence
            (u := u) (V := V) X).functor ⋙
          (CostructuredArrow.pre (Over.forget X) u V).op ⋙ P) := by
    infer_instance
  exact hasLimit_of_iso e

/-- Helper for Lemma 7.28.5: in the lifted presheaf universe, the projection `j.op` admits the
pointwise right Kan extensions required by the owner comparison theorem. -/
private theorem cocontinuousOver_projection_pointwiseRan_lifted
    (P : (CostructuredArrow u V)ᵒᵖ ⥤ Type (max (max (max (max t u₁) u₂) v₁) v₂)) :
    Functor.HasPointwiseRightKanExtension (CostructuredArrow.proj u V).op P := by
  intro X
  -- In the lifted universe, each structured-arrow diagram is small enough for the ambient
  -- `Type` limits instance, so the owner witness is available directly.
  infer_instance

/-- Helper for Lemma 7.28.5: the owner comparison for the projection `j` is already an
isomorphism, so the remaining source proof only needs the specialization rewrite. -/
private theorem cocontinuousOver_projection_target_transport_underlying
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    (sheafToPresheaf J' Tl).map
        (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
          ((sheafComposeNatTrans J U
            (sheafificationAdjunction J (Type t))
            (sheafificationAdjunction J Tl)).app F)) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op
        ((sheafToPresheaf J Tl).map
          ((sheafComposeNatTrans J U
            (sheafificationAdjunction J (Type t))
            (sheafificationAdjunction J Tl)).app F)) := by
  -- Forgetting the target-side map along `j` is definitionally just whiskering the underlying
  -- presheaf map by `j.op`.
  ext X x
  rfl

/-- Helper for Lemma 7.28.5: in the lifted universe, precomposing the owner comparison with
`toSheafify` again recovers whiskering of the sheafification unit. -/
private lemma cocontinuousOver_projection_comparison_precompose_toSheafify_lifted
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
      (sheafToPresheaf J' Tl).map
        ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
          (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) := by
  -- The lifted comparison is again defined by `sheafifyLift`, so the defining unit factorization
  -- is unchanged after moving to the larger `Type` universe.
  ext X x
  change
    ((toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙
          CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})).app X ≫
        (sheafifyLift J'
          (Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (toSheafify J
              (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})))
          ((presheafToSheaf J
              (Type (max (max (max (max t u₁) u₂) v₁) v₂)) ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous
              (Type (max (max (max (max t u₁) u₂) v₁) v₂)) J' J).obj
              (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})).property).app
          X) x = _
  exact congrFun
    (congrArg (fun η => η.app X)
      (toSheafify_sheafifyLift J'
        (Functor.whiskerLeft (CostructuredArrow.proj u V).op
          (toSheafify J
            (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})))
        ((presheafToSheaf J
            (Type (max (max (max (max t u₁) u₂) v₁) v₂)) ⋙
          (CostructuredArrow.proj u V).sheafPushforwardContinuous
            (Type (max (max (max (max t u₁) u₂) v₁) v₂)) J' J).obj
            (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})).property))
    x

/-- Helper for Lemma 7.28.5: after moving the source comparison through `ULift`, the forgotten
comparison factors through the large-universe owner comparison and the target-side transport map. -/
private lemma cocontinuousOver_projection_comparison_app_whisker_ulift_normalized
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    let α :=
      ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
    let β :
        ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
            (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
          presheafToSheaf J Tl ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
      Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
        (G := CostructuredArrow.proj u V) J' J
    toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
        (((sheafToPresheaf J' Tl).map
            ((sheafComposeNatTrans J' U
              (sheafificationAdjunction J' (Type t))
              (sheafificationAdjunction J' Tl)).app ((CostructuredArrow.proj u V).op ⋙ F))) ≫
          (Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U)) =
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
        ((sheafToPresheaf J' Tl).map (β.app (F ⋙ U)) ≫
          (sheafToPresheaf J' Tl).map
            (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
              ((sheafComposeNatTrans J U
                (sheafificationAdjunction J (Type t))
                (sheafificationAdjunction J Tl)).app F))) := by
  dsimp
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F)
  let common :=
    Functor.whiskerRight
      (toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
        (sheafToPresheaf J' (Type t)).map α)
      U
  have hsource :
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
          (sheafToPresheaf J' Tl).map
            ((sheafComposeNatTrans J' U
                (sheafificationAdjunction J' (Type t))
                (sheafificationAdjunction J' Tl)).app
              ((CostructuredArrow.proj u V).op ⋙ F)) ≫
            Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U =
        common := by
    -- First expose the `J'`-sheafification unit for `sheafComposeNatTrans`, then repack the
    -- resulting composite as a whiskered precomposition.
    have hfac :=
      sheafComposeNatTrans_fac J' U
        (sheafificationAdjunction J' (Type t))
        (sheafificationAdjunction J' Tl)
        ((CostructuredArrow.proj u V).op ⋙ F)
    have hfac' :=
      congrArg (fun k ↦ k ≫ Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U) hfac
    calc
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
          (sheafToPresheaf J' Tl).map
            ((sheafComposeNatTrans J' U
                (sheafificationAdjunction J' (Type t))
                (sheafificationAdjunction J' Tl)).app
              ((CostructuredArrow.proj u V).op ⋙ F)) ≫
            Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U =
          Functor.whiskerRight (toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)) U ≫
            Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U := by
        simpa [Category.assoc] using hfac'
      _ = Functor.whiskerRight
            (toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
              (sheafToPresheaf J' (Type t)).map α) U := by
        ext X x
        rfl
      _ = common := rfl
  have htarget :
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
          (sheafToPresheaf J' Tl).map
            ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
                (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) ≫
          (sheafToPresheaf J' Tl).map
            (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
              ((sheafComposeNatTrans J U
                  (sheafificationAdjunction J (Type t))
                  (sheafificationAdjunction J Tl)).app F)) =
        common := by
    -- Normalize the lifted owner comparison, then rewrite the transport term back to the same
    -- whiskered precomposition as on the source side.
    have hβ :
        toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
            (sheafToPresheaf J' Tl).map
              ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
                  (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) := by
      simpa [Tl, U] using
        cocontinuousOver_projection_comparison_precompose_toSheafify_lifted
          (J := J) (u := u) (V := V) F
    have htransport :
        (sheafToPresheaf J' Tl).map
            (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
              ((sheafComposeNatTrans J U
                  (sheafificationAdjunction J (Type t))
                  (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op
            ((sheafToPresheaf J Tl).map
              ((sheafComposeNatTrans J U
                  (sheafificationAdjunction J (Type t))
                  (sheafificationAdjunction J Tl)).app F)) := by
      simpa [Tl, U] using
        cocontinuousOver_projection_target_transport_underlying
          (J := J) (u := u) (V := V) F
    have hβ' :=
      congrArg
        (fun k ↦
          k ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)))
        hβ
    have hfac :=
      sheafComposeNatTrans_fac J U
        (sheafificationAdjunction J (Type t))
        (sheafificationAdjunction J Tl)
        F
    have hcompare :=
      cocontinuousOver_projection_comparison_precompose_toSheafify
        (J := J) (u := u) (V := V) F
    have hstep1 :
        toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
            (sheafToPresheaf J' Tl).map
              ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
                  (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) := by
      simpa [Category.assoc] using hβ'
    have hstep2 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            Functor.whiskerLeft (CostructuredArrow.proj u V).op
              ((sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) := by
      ext X x
      let τ :=
        (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U))).app X
      have htransportX := congrArg (fun η => η.app X) htransport
      simpa [τ, Category.assoc] using
        congrFun (congrArg (fun k ↦ τ ≫ k) htransportX) x
    have hstep3 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            Functor.whiskerLeft (CostructuredArrow.proj u V).op
              ((sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (toSheafify J (F ⋙ U) ≫
              (sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) := by
      rfl
    have hstep4 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (toSheafify J (F ⋙ U) ≫
              (sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (Functor.whiskerRight (toSheafify J F) U) := by
      simpa using
        congrArg (fun η ↦ Functor.whiskerLeft (CostructuredArrow.proj u V).op η) hfac
    have hstep5 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (Functor.whiskerRight (toSheafify J F) U) =
          Functor.whiskerRight
            (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)) U := by
      ext X x
      rfl
    have hstep6 :
        Functor.whiskerRight
            (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)) U =
          common := by
      unfold common
      symm
      simpa using congrArg (fun η ↦ Functor.whiskerRight η U) hcompare
    exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans hstep6))))
  exact hsource.trans htarget.symm

/-- Helper for Lemma 7.28.5: the target-side lifted comparison is the unique sheaf morphism whose
precomposition with the `J'`-sheafification unit matches the normalized source-side candidate. -/
private theorem cocontinuousOver_projection_comparison_target_candidate_eq
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    let α :=
      ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
    let β :
        ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
            (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
          presheafToSheaf J Tl ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
      Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
        (G := CostructuredArrow.proj u V) J' J
    ((sheafComposeNatTrans J' U
        (sheafificationAdjunction J' (Type t))
        (sheafificationAdjunction J' Tl)).app ((CostructuredArrow.proj u V).op ⋙ F)) ≫
      ((sheafCompose J' U).map α) =
      (β.app (F ⋙ U)) ≫
        ((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
          ((sheafComposeNatTrans J U
            (sheafificationAdjunction J (Type t))
            (sheafificationAdjunction J Tl)).app F) := by
  dsimp
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
  let β :
      ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
          (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
        presheafToSheaf J Tl ⋙
          (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
    Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
      (G := CostructuredArrow.proj u V) J' J
  -- The normalized owner equality already identifies the two candidates after precomposition by
  -- `toSheafify`, so injectivity of the sheafification adjunction closes the sheaf-level equality.
  apply (sheafificationAdjunction J' Tl).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simpa [Functor.map_comp, Category.assoc, Tl, U, α, β] using
    cocontinuousOver_projection_comparison_app_whisker_ulift_normalized
      (J := J) (u := u) (V := V) F

private theorem cocontinuousOver_projection_comparison_app_whisker_ulift
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    let α :=
      ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
    let β :
        ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
            (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
          presheafToSheaf J Tl ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
      Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
        (G := CostructuredArrow.proj u V) J' J
    ((sheafToPresheaf J' Tl).map
        ((sheafComposeNatTrans J' U
          (sheafificationAdjunction J' (Type t))
          (sheafificationAdjunction J' Tl)).app ((CostructuredArrow.proj u V).op ⋙ F))) ≫
      (Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U) =
      (sheafToPresheaf J' Tl).map (β.app (F ⋙ U)) ≫
        (sheafToPresheaf J' Tl).map
          (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
            ((sheafComposeNatTrans J U
              (sheafificationAdjunction J (Type t))
              (sheafificationAdjunction J Tl)).app F)) := by
  -- Route correction: first identify the two sheaf morphisms upstairs, then forget that
  -- equality to the presheaf level where the displayed transport statement lives.
  dsimp
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
  let β :
      ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
          (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
        presheafToSheaf J Tl ⋙
          (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
    Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
      (G := CostructuredArrow.proj u V) J' J
  -- Forget the sheaf-level equality furnished by the owner uniqueness step.
  simpa [Functor.map_comp, Category.assoc, Tl, U, α, β] using
    congrArg
      (fun k ↦ (sheafToPresheaf J' Tl).map k)
      (cocontinuousOver_projection_comparison_target_candidate_eq
        (J := J) (u := u) (V := V) F)

/-- Helper for Lemma 7.28.5: whiskering a locally injective morphism of `Type`-valued presheaves
by `ULift` does not change the equalizer sieves. -/
private theorem locallyInjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w)))] :
    Presheaf.IsLocallyInjective L η where
  equalizerSieve_mem {X} x y h := by
    let x' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).obj X := ULift.up x
    let y' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).obj X := ULift.up y
    -- Lift the equal pair to the larger universe, use local injectivity there, and descend.
    have hUp :
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).app X x' =
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w))).app X y' := by
      change ULift.up (η.app X x) = ULift.up (η.app X y)
      exact congrArg ULift.up h
    let S : Sieve X.unop :=
      Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w)))
        x' y'
    have hS : S ∈ L X.unop := by
      exact
        Presheaf.equalizerSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w)))
          x' y' hUp
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ULift.up ((P.map f.op) x) = ULift.up ((P.map f.op) y) at hf
    change (P.map f.op) x = (P.map f.op) y
    exact ULift.up.inj hf

/-- Helper for Lemma 7.28.5: whiskering a locally injective morphism of `Type`-valued presheaves
by `ULift` does not change the equalizer sieves. -/
private theorem isLocallyInjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L η] :
    Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  refine ⟨?_⟩
  intro X x y h
  -- The `ULift` whiskering only repackages sections, so the equalizer sieve is unchanged.
  have hDown : η.app X x.down = η.app X y.down := by
    change ULift.up (η.app X x.down) = ULift.up (η.app X y.down) at h
    exact ULift.up.inj h
  have hSieve :
      Presheaf.equalizerSieve
          (F := P ⋙
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w)))
          x y =
        Presheaf.equalizerSieve (F := P) x.down y.down := by
    ext Y f
    constructor
    · intro hEq
      change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down) at hEq
      exact ULift.up.inj hEq
    · intro hEq
      change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down)
      exact congrArg ULift.up hEq
  rw [hSieve]
  exact Presheaf.equalizerSieve_mem L η x.down y.down hDown

/-- Helper for Lemma 7.28.5: whiskering a type-valued presheaf morphism by `ULift` does not
change its image sieve. -/
private theorem imageSieve_whisker_ulift
    {E : Type u₃} [Category.{v₃} E]
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q) {X : E}
    (x :
      (Q ⋙
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w))).obj (Opposite.op X)) :
    Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))) x =
      Presheaf.imageSieve η x.down := by
  ext Y f
  constructor
  · rintro ⟨y, hy⟩
    -- Any lifted local preimage descends by `ULift.down`.
    refine ⟨y.down, ?_⟩
    exact congrArg ULift.down hy
  · rintro ⟨y, hy⟩
    -- Conversely, any ordinary local preimage lifts back via `ULift.up`.
    refine ⟨ULift.up y, ?_⟩
    change ULift.up (η.app (Opposite.op Y) y) = ULift.up (Q.map f.op x.down)
    exact congrArg ULift.up hy

/-- Helper for Lemma 7.28.5: whiskering a locally surjective morphism of `Type`-valued presheaves
by `ULift` does not change the image sieves. -/
private theorem locallySurjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w)))] :
    Presheaf.IsLocallySurjective L η where
  imageSieve_mem {X} x := by
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).obj (Opposite.op X) := ULift.up x
    let S : Sieve X :=
      Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w)))
        x'
    -- Lift the target section upstairs, obtain a local preimage there, and descend it.
    have hS : S ∈ L X := by
      exact
        Presheaf.imageSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w)))
          x'
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ∃ t : (P ⋙
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w))).obj (Opposite.op Y),
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w))).app (Opposite.op Y) t =
        (Q ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).map f.op x' at hf
    rcases hf with ⟨y, hy⟩
    refine ⟨y.down, ?_⟩
    change ULift.up (η.app (Opposite.op Y) y.down) = ULift.up (Q.map f.op x) at hy
    exact ULift.up.inj hy

/-- Helper for Lemma 7.28.5: whiskering a locally surjective morphism of `Type`-valued presheaves
by `ULift` does not change the image sieves. -/
private theorem isLocallySurjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L η] :
    Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  refine ⟨?_⟩
  intro X x
  -- After identifying the image sieve with the unlifted one, reuse local surjectivity of `η`.
  rw [imageSieve_whisker_ulift (η := η) (x := x)]
  exact Presheaf.imageSieve_mem L η x.down

/-- Helper for Lemma 7.28.5: the identity functor on any `Type` universe preserves
sheafification tautologically. -/
private instance preservesSheafification_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (𝟭 (Type t)) where
  le P Q f hf := by
    -- Whiskering by the identity functor leaves the `W`-morphism unchanged.
    simpa using hf

/-- Helper for Lemma 7.28.5: the forgetful functor on any `Type` universe is the identity, so it
preserves sheafification tautologically as well. -/
private instance preservesSheafification_forget_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (forget (Type t)) where
  le P Q f hf := by
    -- For `Type`, the forgetful functor is definitionally the identity functor.
    simpa using hf

/-- Helper for Lemma 7.28.5: the concrete `Plus` map is locally injective for type-valued
presheaves in any universe. -/
private theorem toPlus_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective L (L.toPlus P) := by
  -- Compare representatives of equal `Plus` sections on a covering sieve.
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      open GrothendieckTopology.Plus in
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, h₁, h₂, eq⟩ := h
      exact L.superset_covering (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Lemma 7.28.5: the concrete `Plus` map is locally surjective for type-valued
presheaves in any universe. -/
private theorem toPlus_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective L (L.toPlus P) := by
  -- Every `Plus` section is locally represented by an actual presheaf section.
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) := {
    imageSieve_mem := by
      intro X x
      open GrothendieckTopology.Plus in
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine L.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using
        x.2
          { fst.hf := hf
            snd.hf := S.1.downward_closed hf g
            r.g₁ := g
            r.g₂ := 𝟙 Z
            .. } }
  infer_instance

/-- Helper for Lemma 7.28.5: the concrete `plus-plus` model of sheafification is locally
injective for type-valued presheaves in any universe. -/
private theorem concrete_toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) :=
    toPlus_isLocallyInjective_type (L := L) P
  letI : Presheaf.IsLocallyInjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallyInjective_type (L := L) (L.plusObj P)
  -- Rewrite the concrete sheafification unit as a composite of two `Plus` maps.
  change Presheaf.IsLocallyInjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.28.5: the concrete `plus-plus` model of sheafification is locally
surjective for type-valued presheaves in any universe. -/
private theorem concrete_toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) :=
    toPlus_isLocallySurjective_type (L := L) P
  letI : Presheaf.IsLocallySurjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallySurjective_type (L := L) (L.plusObj P)
  -- The same concrete `Plus` factorization gives local surjectivity of `L.toSheafify`.
  change Presheaf.IsLocallySurjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.28.5: formal universe bridge for the source proof.

The source statement only needs the inverse-image square `j_V^{-1} (u')^{-1} ≅ u^{-1} j^{-1}`
on set-valued sheaves. The current formal proof transports that square through an auxiliary
`ULift` universe; this helper is exactly the required `W = local bijectivity` bridge in that
auxiliary universe, not an extra mathematical hypothesis of Lemma 7.28.5. -/
private theorem large_type_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max t w))] :
    L.WEqualsLocallyBijective (Type (max t w)) := by
  -- Source-facing repair target: package the already-existing concrete `plus-plus`
  -- sheafification proof into a universe-stable transport from the small `Type t` unit to the
  -- auxiliary `Type (max t w)` unit. Do not change the final Lemma 7.28.5 statement; the
  -- obstruction is only this formal universe bridge.
  sorry

/-- Helper for Lemma 7.28.5: if the small `Type`-valued sheafification unit is locally bijective
for every presheaf, then `W` agrees with local bijectivity in the small universe as well. -/
private theorem small_type_WEqualsLocallyBijective_of_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    (hInj :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallyInjective L (toSheafify L P))
    (hSurj :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallySurjective L (toSheafify L P)) :
    L.WEqualsLocallyBijective (Type t) := by
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallyInjective L (toSheafify L P) := hInj
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallySurjective L (toSheafify L P) := hSurj
  let _ : L.PreservesSheafification (forget (Type t)) := by
    -- The forgetful functor on `Type t` is the identity, so it preserves sheafification.
    simpa using
      (preservesSheafification_id_type (L := L) :
        L.PreservesSheafification (𝟭 (Type t)))
  let _ : L.HasSheafCompose (forget (Type t)) := by
    infer_instance
  -- Package the unitwise local bijectivity data into the canonical `WEqualsLocallyBijective`
  -- structure.
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := Type t)

/-- Helper for Lemma 7.28.5: once `W` agrees with local bijectivity in both `Type` universes,
whiskering by the fixed `ULift` functor preserves sheafification. -/
private theorem uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    [L.WEqualsLocallyBijective (Type t)]
    [L.WEqualsLocallyBijective (Type (max t w))] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  refine ⟨?_⟩
  intro P Q f hf
  let _ : Presheaf.IsLocallyInjective L f :=
    (L.W_iff_isLocallyBijective f).1 hf |>.1
  let _ : Presheaf.IsLocallySurjective L f :=
    (L.W_iff_isLocallyBijective f).1 hf |>.2
  -- `ULift` leaves equalizer and image sieves unchanged, so local bijectivity transports
  -- directly across whiskering.
  let _ : Presheaf.IsLocallyInjective L (Functor.whiskerRight f F) :=
    isLocallyInjective_whisker_ulift (L := L) (η := f)
  let _ : Presheaf.IsLocallySurjective L (Functor.whiskerRight f F) :=
    isLocallySurjective_whisker_ulift (L := L) (η := f)
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight f F))

/-- Helper for Lemma 7.28.5: the fixed `ULift` functor on types preserves sheafification for any
site once the small and large sheafification units are known to be locally bijective. -/
private theorem uliftFunctor_preservesSheafification_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) := by
  -- TODO: once the large-universe `WEqualsLocallyBijective` owner is installed, package it
  -- together with the small `Type t` owner and apply
  -- `uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective`.
  sorry

/-- Helper for Lemma 7.28.5: for any site, the `ULift` sheafification comparison component is an
isomorphism because the whiskered sheafification unit is locally bijective upstairs. -/
private noncomputable def ulift_sheafCompose_comparison_hom
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    sheafify L (P ⋙ (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) ⟶
      sheafify L P ⋙ (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) :=
  (sheafToPresheaf L (Type (max t w))).map
    ((sheafComposeNatTrans L
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))
      (sheafificationAdjunction L (Type t))
      (sheafificationAdjunction L (Type (max t w)))).app P)

/-- Helper for Lemma 7.28.5: the underlying `ULift` comparison satisfies the standard
`toSheafify` factorization. -/
private theorem ulift_sheafCompose_comparison_hom_fac
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    toSheafify L
        (P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))) ≫
      ulift_sheafCompose_comparison_hom (L := L) P =
        Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w)) := by
  -- Unfold the named comparison back to the standard sheafification comparison component.
  simpa [ulift_sheafCompose_comparison_hom] using
    sheafComposeNatTrans_fac L
      (CategoryTheory.uliftFunctor.{w, t} :
        Type t ⥤ Type (max t w))
      (sheafificationAdjunction L (Type t))
      (sheafificationAdjunction L (Type (max t w))) P

/-- Helper for Lemma 7.28.5: the `ULift` comparison component is an isomorphism exactly when the
whiskered small sheafification unit is a `W`-morphism in the large target universe. -/
private theorem ulift_sheafComposeNatTrans_app_isIso_iff_whiskered_toSheafify_W
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))
          (sheafificationAdjunction L (Type t))
          (sheafificationAdjunction L (Type (max t w)))).app P) ↔
      L.W
        (Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))) := by
  let Tl := Type (max t w)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{w, t}
  let η :=
    (sheafComposeNatTrans L U
      (sheafificationAdjunction L (Type t))
      (sheafificationAdjunction L Tl)).app P
  have hW :
      L.W (ulift_sheafCompose_comparison_hom (L := L) P) ↔ IsIso η := by
    -- Forgetting to presheaves identifies the comparison with the corresponding `W`-statement.
    simpa [ulift_sheafCompose_comparison_hom, η] using
      (L.W_sheafToPresheaf_map_iff_isIso η)
  -- Reduce the componentwise isomorphism to a `W`-statement for its underlying presheaf map.
  change IsIso η ↔ L.W (Functor.whiskerRight (toSheafify L P) U)
  rw [← hW, ← ulift_sheafCompose_comparison_hom_fac (L := L) (P := P)]
  -- Precomposition by the large-universe sheafification unit does not change membership in `W`.
  exact
    (((GrothendieckTopology.W (J := L) (A := Tl)).precomp_iff
      (W' := GrothendieckTopology.W (J := L) (A := Tl))
      (toSheafify L (P ⋙ U))
      (ulift_sheafCompose_comparison_hom (L := L) P)
      (L.W_toSheafify (P ⋙ U))).symm)

/-- Helper for Lemma 7.28.5: if the small sheafification unit is locally bijective, then its
`ULift`-whiskering is locally bijective as well. -/
private theorem whiskered_toSheafify_isLocallyBijective_for_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    (P : Eᵒᵖ ⥤ Type t)
    [HasWeakSheafify L (Type t)]
    [Presheaf.IsLocallyInjective L (toSheafify L P)]
    [Presheaf.IsLocallySurjective L (toSheafify L P)] :
    Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) ∧
      Presheaf.IsLocallySurjective L
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  let F : Type t ⥤ Type (max t w) :=
    CategoryTheory.uliftFunctor.{w, t}
  constructor
  · -- `ULift` leaves the equalizer sieves unchanged, so local injectivity transports directly.
    exact isLocallyInjective_whisker_ulift (L := L) (η := toSheafify L P)
  · -- The same argument on image sieves transports local surjectivity across `ULift`.
    exact isLocallySurjective_whisker_ulift (L := L) (η := toSheafify L P)

/-- Helper for Lemma 7.28.5: the small `Type`-valued sheafification unit is locally bijective
once the same site admits weak sheafification in the larger `ULift` target universe. -/
private theorem small_type_toSheafify_isLocallyBijective_for_site
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t)
    (hPres :
      L.PreservesSheafification
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)))
    (hInj :
      Presheaf.IsLocallyInjective L
        (toSheafify L
          (P ⋙
            (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)))))
    (hSurj :
      Presheaf.IsLocallySurjective L
        (toSheafify L
          (P ⋙
            (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))))) :
    Presheaf.IsLocallyInjective L (toSheafify L P) ∧
      Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  have hWhiskerInj :
      Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P) F) := by
    let _ : L.PreservesSheafification F := hPres
    let _ : Presheaf.IsLocallyInjective L (toSheafify L (P ⋙ F)) := hInj
    -- Rewrite the whiskered small unit to the large unit before reflecting injectivity back.
    rw [← sheafComposeIso_hom_fac (J := L) (F := F) (P := P)]
    infer_instance
  have hWhiskerSurj :
      Presheaf.IsLocallySurjective L
        (Functor.whiskerRight (toSheafify L P) F) := by
    let _ : L.PreservesSheafification F := hPres
    let _ : Presheaf.IsLocallySurjective L (toSheafify L (P ⋙ F)) := hSurj
    -- The same comparison identifies the whiskered small unit with the large unit upstairs.
    rw [← sheafComposeIso_hom_fac (J := L) (F := F) (P := P)]
    infer_instance
  constructor
  · letI :
        Presheaf.IsLocallyInjective L
          (Functor.whiskerRight (toSheafify L P) F) := hWhiskerInj
    -- Reflect local injectivity back down through `ULift`.
    simpa [F] using
      (locallyInjective_of_whisker_ulift (L := L) (η := toSheafify L P) :
        Presheaf.IsLocallyInjective L (toSheafify L P))
  · letI :
        Presheaf.IsLocallySurjective L
          (Functor.whiskerRight (toSheafify L P) F) := hWhiskerSurj
    -- Reflect local surjectivity back down through `ULift`.
    simpa [F] using
      (locallySurjective_of_whisker_ulift (L := L) (η := toSheafify L P) :
        Presheaf.IsLocallySurjective L (toSheafify L P))

/-- Helper for Lemma 7.28.5: once the small sheafification unit is locally bijective and `W`
agrees with local bijectivity in the target universe, the whiskered unit is already in `W`. -/
private theorem whiskered_toSheafify_W_of_small_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    (P : Eᵒᵖ ⥤ Type t)
    [Presheaf.IsLocallyInjective L (toSheafify L P)]
    [Presheaf.IsLocallySurjective L (toSheafify L P)]
    (hW : L.WEqualsLocallyBijective (Type (max t w))) :
    L.W
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  let _ : L.WEqualsLocallyBijective Ts := hW
  rcases whiskered_toSheafify_isLocallyBijective_for_ulift (L := L) P with ⟨hWhiskerInj, hWhiskerSurj⟩
  letI :
      Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P) F) := hWhiskerInj
  letI :
      Presheaf.IsLocallySurjective L
        (Functor.whiskerRight (toSheafify L P) F) := hWhiskerSurj
  -- Once the whiskered unit is locally bijective in the target universe, `W` follows formally.
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight (toSheafify L P) F))

/-- Helper for Lemma 7.28.5: once the small sheafification unit is locally bijective, its
`ULift`-whiskering is already a `W`-morphism in the larger target universe. -/
private theorem whiskered_toSheafify_W_for_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    L.W
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  let hPres : L.PreservesSheafification F :=
    @uliftFunctor_preservesSheafification_type.{u₃, v₃, t, w} E _ L inferInstance inferInstance
  let hW : L.WEqualsLocallyBijective Ts :=
    @large_type_WEqualsLocallyBijective.{u₃, v₃, t, w} E _ L inferInstance
  let _ : L.WEqualsLocallyBijective Ts := hW
  have hLargeInj :
      Presheaf.IsLocallyInjective L (toSheafify L (P ⋙ F)) := by
    exact ((L.W_iff_isLocallyBijective (toSheafify L (P ⋙ F))).1 (L.W_toSheafify (P ⋙ F))).1
  have hLargeSurj :
      Presheaf.IsLocallySurjective L (toSheafify L (P ⋙ F)) := by
    exact ((L.W_iff_isLocallyBijective (toSheafify L (P ⋙ F))).1 (L.W_toSheafify (P ⋙ F))).2
  rcases
      small_type_toSheafify_isLocallyBijective_for_site (L := L) P hPres hLargeInj hLargeSurj with
    ⟨hSmallInj, hSmallSurj⟩
  let _ : Presheaf.IsLocallyInjective L (toSheafify L P) := hSmallInj
  let _ : Presheaf.IsLocallySurjective L (toSheafify L P) := hSmallSurj
  -- Once the small unit is locally bijective, its `ULift`-whiskering is in `W`.
  exact
    whiskered_toSheafify_W_of_small_unit_local_bijectivity (L := L) P hW

/-- Helper for Lemma 7.28.5: for any site, the `ULift` sheafification comparison component is an
isomorphism because the whiskered sheafification unit is locally bijective upstairs. -/
private theorem ulift_sheafComposeNatTrans_app_isIso_for_site
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))
          (sheafificationAdjunction L (Type t))
          (sheafificationAdjunction L (Type (max t w)))).app P) := by
  -- Route correction: first reduce the comparison component to the source-faithful `W`-statement
  -- for the whiskered sheafification unit, then close that `W`-goal via local bijectivity.
  rw [ulift_sheafComposeNatTrans_app_isIso_iff_whiskered_toSheafify_W (L := L) (P := P)]
  -- The explicit `W`-bridge isolates the only universe-sensitive step.
  exact whiskered_toSheafify_W_for_ulift (L := L) P

private theorem cocontinuousOver_projection_comparison_target_chain_isIso
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    let β :
        ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
            (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
          presheafToSheaf J Tl ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
      Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
        (G := CostructuredArrow.proj u V) J' J
    IsIso
      ((β.app (F ⋙ U)) ≫
        ((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
          ((sheafComposeNatTrans J U
            (sheafificationAdjunction J (Type t))
            (sheafificationAdjunction J Tl)).app F)) := by
  -- Source-facing repair target: specialize the pointwise right-Kan-extension owner for the
  -- textbook projection `j : {}^u_V I -> C` to the exact lifted universe `Tl`; then the standard
  -- pushforward/sheafification comparison gives `IsIso (β.app (F ⋙ U))`, and the only remaining
  -- step is composing with the target-side `ULift` comparison isomorphism.
  sorry

/-- Helper for Lemma 7.28.5: after whiskering the source-facing comparison by `ULift`, the result
identifies with the already-controlled large-universe comparison, hence is invertible. -/
private theorem cocontinuousOver_projection_comparison_whiskered_isIso
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    IsIso
      (((sheafCompose J' U).map
        (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
          F))) := by
  -- Route correction: once `cocontinuousOver_projection_comparison_target_chain_isIso` is in
  -- place, this lemma is only a cancellation step along
  -- `cocontinuousOver_projection_comparison_target_candidate_eq`.
  dsimp
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U :
      Type t ⥤ Type (max (max (max (max t u₁) u₂) v₁) v₂) :=
    CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
  let β :
      ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
          (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
        presheafToSheaf J Tl ⋙
          (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
    Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
      (G := CostructuredArrow.proj u V) J' J
  let δ :=
    (sheafComposeNatTrans J' U
      (sheafificationAdjunction J' (Type t))
      (sheafificationAdjunction J' Tl)).app ((CostructuredArrow.proj u V).op ⋙ F)
  let _ :
      IsIso
        ((β.app (F ⋙ U)) ≫
          ((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
            ((sheafComposeNatTrans J U
              (sheafificationAdjunction J (Type t))
              (sheafificationAdjunction J Tl)).app F)) :=
    cocontinuousOver_projection_comparison_target_chain_isIso
      (J := J) (u := u) (V := V) (F := F)
  have hcandidate :
      δ ≫ ((sheafCompose J' U).map α) =
        (β.app (F ⋙ U)) ≫
          ((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
            ((sheafComposeNatTrans J U
              (sheafificationAdjunction J (Type t))
              (sheafificationAdjunction J Tl)).app F) := by
    simpa [δ, α, β] using
      cocontinuousOver_projection_comparison_target_candidate_eq
        (J := J) (u := u) (V := V) F
  -- TODO: instantiate the site-level `ULift` comparison isomorphism at
  -- `((CostructuredArrow.proj u V).op ⋙ F)`, rewrite the composite by `hcandidate`, and cancel
  -- the left factor `δ`.
  sorry

private theorem cocontinuousOver_projection_comparison_isIso
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    IsIso (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
      F) := by
  -- Reflect the isomorphism from the whiskered comparison back through the fully faithful
  -- sheaf-composition functor induced by `ULift`.
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
  let _ : IsIso ((sheafCompose J' U).map α) :=
    cocontinuousOver_projection_comparison_whiskered_isIso
      (J := J) (u := u) (V := V) (F := F)
  -- Since `ULift` is fully faithful, `sheafCompose J' U` reflects isomorphisms.
  exact isIso_of_reflects_iso α (sheafCompose J' U)

/-- Helper for Lemma 7.28.5: after forgetting to presheaves, the specialized comparison should be
an isomorphism on each object of `{}^u_V \mathcal I`; this is the remaining sectionwise source
comparison. -/
private theorem cocontinuousOver_projection_specializedComparison_underlying_app_isIso
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t))
    (X : CostructuredArrow u V) :
    IsIso (((sheafToPresheaf J' (Type t)).map
      ((cocontinuousOver_projection_specializedComparison
        (J := J) (K := K) (u := u) (V := V)).app ℱ)).app (Opposite.op X)) :=
by
  let F : Cᵒᵖ ⥤ Type t :=
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
      ((sheafToPresheaf K (Type t)).obj ℱ)
  -- Rewrite the specialized component to the owner comparison for `j` on the restricted presheaf
  -- `u.op ⋙ ℱ.1`, then inherit invertibility from the owner theorem.
  rw [cocontinuousOver_projection_specializedComparison_underlying_app_eq_projectionComparison
    (J := J) (K := K) (u := u) (V := V) (ℱ := ℱ) (X := X)]
  letI : IsIso (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
      F) :=
    cocontinuousOver_projection_comparison_isIso
    (J := J) (u := u) (V := V) (F := F)
  letI :
      IsIso
        ((sheafToPresheaf J' (Type t)).map
          (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
            F)) := by
    infer_instance
  exact
    NatIso.isIso_app_of_isIso
      ((sheafToPresheaf J' (Type t)).map
        (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F))
      (Opposite.op X)

/-- Helper for Lemma 7.28.5: the specialized `j`-side sheafification comparison is invertible on
presheaves coming from restriction along `u`. -/
private theorem cocontinuousOver_projection_specializedComparison_isIso
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t)) :
    IsIso ((cocontinuousOver_projection_specializedComparison
      (J := J) (K := K) (u := u) (V := V)).app ℱ) := by
  -- Route correction: reflect the sheaf isomorphism question to presheaves and isolate the
  -- remaining blocker as the sectionwise source comparison at each `X : {}^u_V \mathcal I`.
  let η :=
    (cocontinuousOver_projection_specializedComparison
      (J := J) (K := K) (u := u) (V := V)).app ℱ
  letI :
      (sheafToPresheaf J' (Type t)).ReflectsIsomorphisms :=
    (fullyFaithfulSheafToPresheaf J' (Type t)).reflectsIsomorphisms
  have hη :
      IsIso ((sheafToPresheaf J' (Type t)).map η) := by
    -- Once forgotten to presheaves, pointwise isomorphism is the exact sectionwise target.
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact cocontinuousOver_projection_specializedComparison_underlying_app_isIso
      (J := J) (K := K) (u := u) (V := V) ℱ X.unop
  letI : IsIso ((sheafToPresheaf J' (Type t)).map η) := hη
  simpa [η] using isIso_of_reflects_iso η (sheafToPresheaf J' (Type t))

/-- Helper for Lemma 7.28.5: the componentwise specialized comparison is already natural in the
input sheaf on `D`. -/
private theorem cocontinuousOver_projection_specializedSheafificationIso_naturality
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    {ℱ 𝒢 : Sheaf K (Type t)}
    [IsIso ((cocontinuousOver_projection_specializedComparison
      (J := J) (K := K) (u := u) (V := V)).app ℱ)]
    [IsIso ((cocontinuousOver_projection_specializedComparison
      (J := J) (K := K) (u := u) (V := V)).app 𝒢)]
    (η : ℱ ⟶ 𝒢) :
    (sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ (Type t)).obj
          (CostructuredArrow.proj u V).op ⋙
        presheafToSheaf J' (Type t)).map η ≫
        (asIso ((cocontinuousOver_projection_specializedComparison
          (J := J) (K := K) (u := u) (V := V)).app 𝒢)).hom =
      (asIso ((cocontinuousOver_projection_specializedComparison
        (J := J) (K := K) (u := u) (V := V)).app ℱ)).hom ≫
        (sheafToPresheaf K (Type t) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
          presheafToSheaf J (Type t) ⋙
          Functor.sheafPushforwardContinuous j (Type t) J' J).map η := by
  -- Naturality is inherited from the underlying comparison transformation.
  simpa [cocontinuousOver_projection_specializedComparison] using
    (cocontinuousOver_projection_specializedComparison
      (J := J) (K := K) (u := u) (V := V)).naturality η

/-- Helper for Lemma 7.28.5: packaging the specialized `j`-side comparison as a natural
isomorphism gives the source-faithful sheafification step for the square. -/
private noncomputable def cocontinuousOver_projection_specializedSheafificationIso
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)] :
    sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ (Type t)).obj
          (CostructuredArrow.proj u V).op ⋙
        presheafToSheaf J' (Type t) ≅
      sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        presheafToSheaf J (Type t) ⋙
        Functor.sheafPushforwardContinuous j (Type t) J' J :=
  NatIso.ofComponents
    (fun ℱ ↦
      letI := cocontinuousOver_projection_specializedComparison_isIso
        (J := J) (K := K) (u := u) (V := V) ℱ
      asIso ((cocontinuousOver_projection_specializedComparison
        (J := J) (K := K) (u := u) (V := V)).app ℱ))
    (fun {ℱ 𝒢} η ↦
      letI := cocontinuousOver_projection_specializedComparison_isIso
        (J := J) (K := K) (u := u) (V := V) ℱ
      letI := cocontinuousOver_projection_specializedComparison_isIso
        (J := J) (K := K) (u := u) (V := V) 𝒢
      cocontinuousOver_projection_specializedSheafificationIso_naturality
        (J := J) (K := K) (u := u) (V := V) η)

/-- Helper for Lemma 7.28.5: the left side of the inverse-image square is the evident strict
presheaf composite on the slice site `D / V`. -/
private noncomputable def cocontinuousOver_inverseImage_leftIso
    [u.IsCocontinuous J K]
    [HasWeakSheafify J' (Type t)] :
    K.overPullback (Type t) V ⋙
        Functor.sheafPullbackCocontinuous uOver (Type t) J' (K.over V) ≅
      sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft (Over V)ᵒᵖ Dᵒᵖ (Type t)).obj (Over.forget V).op ⋙
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ (Over V)ᵒᵖ (Type t)).obj
          (CostructuredArrow.toOver u V).op ⋙
        presheafToSheaf J' (Type t) :=
  Functor.isoWhiskerRight
    ((Over.forget V).sheafPushforwardContinuousCompSheafToPresheafIso
      (Type t) (K.over V) K)
    ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ (Over V)ᵒᵖ (Type t)).obj
      (CostructuredArrow.toOver u V).op ⋙ presheafToSheaf J' (Type t))

/-- Helper for Lemma 7.28.5: strict commutativity of the square rewrites the slice-side
precomposition square to the base-side precomposition square. -/
private noncomputable def cocontinuousOver_inverseImage_middleIso
    [HasWeakSheafify J' (Type t)] :
    sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft (Over V)ᵒᵖ Dᵒᵖ (Type t)).obj (Over.forget V).op ⋙
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ (Over V)ᵒᵖ (Type t)).obj
          (CostructuredArrow.toOver u V).op ⋙
        presheafToSheaf J' (Type t) ≅
      sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ (Type t)).obj
          (CostructuredArrow.proj u V).op ⋙
        presheafToSheaf J' (Type t) :=
  let sq : CatCommSq j uOver u (Over.forget V) := inferInstance
  Functor.isoWhiskerLeft
    (sheafToPresheaf K (Type t))
    (Functor.isoWhiskerRight
      (((CostructuredArrow.toOver u V).op.whiskeringLeftObjCompIso (Over.forget V).op).symm ≪≫
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Dᵒᵖ (Type t)).mapIso
          ((show (CostructuredArrow.toOver u V).op ⋙ (Over.forget V).op ≅
              (uOver ⋙ Over.forget V).op
              from Iso.refl _) ≪≫
            (NatIso.op sq.iso.symm).symm ≪≫
            (show (j ⋙ u).op ≅ (CostructuredArrow.proj u V).op ⋙ u.op from Iso.refl _)) ≪≫
        (CostructuredArrow.proj u V).op.whiskeringLeftObjCompIso u.op)
      (presheafToSheaf J' (Type t)))

/-- Helper for Lemma 7.28.5: the inverse-image comparison is obtained by rewriting both sides to
the same presheaf square and then inserting the specialized `j`-side sheafification isomorphism. -/
private noncomputable def cocontinuousOver_inverseImage_comparison
    [u.IsCocontinuous J K]
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)] :
    K.overPullback (Type t) V ⋙
        Functor.sheafPullbackCocontinuous uOver (Type t) J' (K.over V) ⟶
      u.sheafPullbackCocontinuous (Type t) J K ⋙
        Functor.sheafPushforwardContinuous j (Type t) J' J :=
  (cocontinuousOver_inverseImage_leftIso (J := J) (K := K) (u := u) (V := V)).hom ≫
    (cocontinuousOver_inverseImage_middleIso (J := J) (K := K) (u := u) (V := V)).hom ≫
    (cocontinuousOver_projection_specializedSheafificationIso
      (J := J) (K := K) (u := u) (V := V)).hom

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
        Functor.sheafPushforwardContinuous j (Type t) J' J :=
  (cocontinuousOver_inverseImage_leftIso (J := J) (K := K) (u := u) (V := V)) ≪≫
    (cocontinuousOver_inverseImage_middleIso (J := J) (K := K) (u := u) (V := V)) ≪≫
    (cocontinuousOver_projection_specializedSheafificationIso
      (J := J) (K := K) (u := u) (V := V))

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
          Functor.sheafPullbackCocontinuous uOver (Type t) J' (K.over V)) := by
  -- The comparison isomorphism satisfies the standard `hom ≫ inv = 𝟙` identity.
  exact (cocontinuousOver_inverseImage_iso J K u V).hom_inv_id

/-
The stronger Beck-Chevalley comparison on direct images is already owned upstream by
`site_square_direct_image_inverse_image_iso` in `Lemma_7_28_6`. This file keeps only the
source-facing inverse-image comparison above and does not duplicate that stronger owner locally.
-/

end CategoryTheory
