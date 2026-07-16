import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.FiberTransport
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.CoverDescent
import Mathlib.Tactic.StacksAttribute

universe u v

namespace CategoryTheory

open Bicategory
open BasedFunctor
open FibredCategoryMor
open InducedCategory.Hom
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

/-- Helper for Lemma 8.8.1: on objects already in the image of `G₁`, the remaining `W`-statement
for the comparison map of `H` is reduced to the composite comparison map for `G₁ ≫ H`. This is
the first source-faithful cancellation step in the direct comparison argument. -/
theorem comparison_stackification_presheafMap_W_on_source_image_of_composite
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (H : Y₁ ⟶ Y₂)
    {U : C} (x y : X.p.Fiber U)
    (hcomp :
      (J.over U).W
        (fibredMorphismPresheafMap
          (G₁ ≫ stack_morphism_toFibredCategoryMor H) x y)) :
    (J.over U).W
      (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj y)) := by
  -- Expand the composite Hom-presheaf map; since `G₁` is a stackification its factor lies in
  -- `W`, so the `2`-out-of-`3` property of `W` cancels it and leaves the `H`-factor in `W`.
  rw [fibredMorphismPresheafMap_comp G₁ (stack_morphism_toFibredCategoryMor H) x y] at hcomp
  exact (J.over U).W.of_precomp _ _ (hG₁.morphismPresheafMap_W U x y) hcomp

/-- Helper for Lemma 8.8.1: once the composite comparison map is known to lie in `W`, the
source-image cancellation step only depends on the owner-level comparison isomorphism
`G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂`. This packages the owner-surface route used later by the direct
comparison proof. -/
theorem comparison_stackification_presheafMap_W_on_source_image_of_ownerIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂)
    {U : C} (x y : X.p.Fiber U)
    :
    (J.over U).W
      (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj y)) := by
  -- The composite comparison map for `G₁ ≫ H` lies in `W` (transported from the stackification
  -- data of `G₂` across the owner iso `α`); cancel the `G₁`-factor by the previous lemma.
  exact
    comparison_stackification_presheafMap_W_on_source_image_of_composite
      (J := J) G₁ hG₁ H x y
      (comparison_stackification_composite_presheafMap_W_of_ownerIso
        (J := J) G₁ G₂ hG₂ H α x y)

/-- Helper for Lemma 8.8.1: the same source-image cancellation step can be fed directly with the
comparison isomorphism that lives in the precomposition category. This removes a repeated
definitionally-trivial conversion from the later full-faithfulness proof. -/
theorem comparison_stackification_presheafMap_W_on_source_image_of_precomposeIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂)
    {U : C} (x y : X.p.Fiber U)
    :
    (J.over U).W
      (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj y)) := by
  -- The precomposition-category comparison iso is definitionally the owner-level iso; feed it to
  -- the owner-iso form of the cancellation step.
  exact
    comparison_stackification_presheafMap_W_on_source_image_of_ownerIso
      (J := J) G₁ G₂ hG₁ hG₂ H
      (comparison_stackification_ownerIsoOfPrecomposeIso (J := J) α) x y

/-- Helper for Lemma 8.8.1: for morphisms between stacks, a fiberwise Hom-presheaf comparison
map that lies in `W` is already an isomorphism, because both Hom presheaves are sheaves on the
slice site. -/
theorem stack_hom_presheafMap_isIso_of_W
    {Y₁ Y₂ : StackOver J}
    (H : Y₁ ⟶ Y₂)
    {U : C} (x y : Y₁.p.Fiber U)
    (hW :
      (J.over U).W
        (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y)) :
    IsIso (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) := by
  -- The source and target Hom-presheaves are sheaves on the slice site `J.over U`, because `Y₁`
  -- and `Y₂` are stacks (hence prestacks). `(J.over U).W` is `ObjectProperty.isLocal` of the
  -- sheaf property, and a `W`-morphism between sheaves is an isomorphism.
  have hSrc :
      Presheaf.IsSheaf (J.over U)
        ((canonicalFiberPseudofunctor Y₁.p).presheafHom x y) :=
    Pseudofunctor.IsPrestack.isSheaf
      (F := canonicalFiberPseudofunctor Y₁.p) (J := J) (S := U) x y
  have hTgt :
      Presheaf.IsSheaf (J.over U)
        ((canonicalFiberPseudofunctor Y₂.p).presheafHom
          (((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor U).obj x)
          (((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor U).obj y)) :=
    Pseudofunctor.IsPrestack.isSheaf
      (F := canonicalFiberPseudofunctor Y₂.p) (J := J) (S := U) _ _
  exact (ObjectProperty.isLocal_iff_isIso
    (P := Presheaf.IsSheaf (J.over U)) _ hSrc hTgt).1 hW

/-- Helper for Lemma 8.8.1: on objects already in the image of `G₁`, the direct comparison map
for `H` is not merely in `W`; it is an actual isomorphism of Hom presheaves because the source
and target are stacks. -/
theorem comparison_stackification_presheafMap_isIso_on_source_image_of_precomposeIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂)
    {U : C} (x y : X.p.Fiber U) :
    IsIso
      (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj y)) := by
  -- The comparison map on source-image objects lies in `W`, and both Hom presheaves are sheaves
  -- because `Y₁`, `Y₂` are stacks, so the `W`-map is an isomorphism.
  exact
    stack_hom_presheafMap_isIso_of_W (J := J) H
      ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
      ((FibredCategoryMor.fiberFunctor G₁ U).obj y)
      (comparison_stackification_presheafMap_W_on_source_image_of_precomposeIso
        (J := J) G₁ G₂ hG₁ hG₂ H α x y)

/-- Helper for Lemma 8.8.1: after choosing local source models for `x` and `y`, the arbitrary
target-object Hom-presheaf map for `H` is the source-image comparison map conjugated by the
explicit source-side and target-side transport isomorphisms. This is the fixed-cover transport
identity isolated by the source-faithful comparison route. -/
theorem comparison_stackification_restricted_presheafMap_factor_of_local_models
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {G₁ : X ⟶ Y₁}
    (H : Y₁ ⟶ Y₂)
    {U : C} {x y : Y₁.p.Fiber U} {xI yI : X.p.Fiber U}
    (hxI : ((FibredCategoryMor.fiberFunctor G₁ U).obj xI) ≅ x)
    (hyI : ((FibredCategoryMor.fiberFunctor G₁ U).obj yI) ≅ y) :
    fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y =
      (comparison_stackification_source_hom_presheaf_iso_of_local_models
        (G₁ := G₁) hxI hyI).inv ≫
        fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
          ((FibredCategoryMor.fiberFunctor G₁ U).obj xI)
          ((FibredCategoryMor.fiberFunctor G₁ U).obj yI) ≫
        (comparison_stackification_target_hom_presheaf_iso_of_local_models
          (G₁ := G₁) (H := H) hxI hyI).hom := by
  -- Both transport isos are canonical `fiberHomPresheafIso`s, so this is the natural-conjugation
  -- identity proved objectwise by `fibredMorphismPresheafMap_natural_of_fiberIso_app`.
  -- Reduce to objectwise equality on the source presheaf.
  apply NatTrans.ext
  funext W
  apply funext
  intro s
  -- The source-side transport iso is `fiberHomPresheafIso (Y := Y₁) hxI hyI`. Set the preimage
  -- of `s` under its hom, so the source-conjugation cancels.
  set δ : ((canonicalFiberPseudofunctor Y₁.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G₁ U).obj xI)
      ((FibredCategoryMor.fiberFunctor G₁ U).obj yI)).obj W :=
    (fiberHomPresheafIso (Y := Y₁.toFibredCategoryOver) hxI hyI).inv.app W s with hδ
  have hs :
      (fiberHomPresheafIso (Y := Y₁.toFibredCategoryOver) hxI hyI).hom.app W δ = s := by
    rw [hδ]
    exact congrFun (congrArg (fun t => NatTrans.app t W)
      (fiberHomPresheafIso (Y := Y₁.toFibredCategoryOver) hxI hyI).inv_hom_id) s
  -- Unfold both composite natural transformations objectwise; the source-side `inv ∘ hom` cancels
  -- to `δ`, leaving exactly the objectwise naturality identity from Step C.
  simp only [NatTrans.comp_app, types_comp_apply]
  rw [← hδ, ← hs]
  exact fibredMorphismPresheafMap_natural_of_fiberIso_app
    (stack_morphism_toFibredCategoryMor H) hxI hyI W δ

/-- Helper for Lemma 8.8.1: once the restricted comparison map has been rewritten through fixed
local source models, it is an isomorphism because the source-image comparison map is already an
isomorphism between stack Hom sheaves. -/
theorem comparison_stackification_coverwise_presheafMap_isIso_of_local_models
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂)
    {U : C} {x y : Y₁.p.Fiber U} {xI yI : X.p.Fiber U}
    (hxI : ((FibredCategoryMor.fiberFunctor G₁ U).obj xI) ≅ x)
    (hyI : ((FibredCategoryMor.fiberFunctor G₁ U).obj yI) ≅ y) :
    IsIso (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) := by
  -- Rewrite the restricted comparison map through the fixed local source models. The middle
  -- source-image factor is an isomorphism of stack Hom sheaves, and the two transport maps are
  -- isomorphisms, so the whole conjugated composite is an isomorphism.
  rw [comparison_stackification_restricted_presheafMap_factor_of_local_models
    (J := J) (G₁ := G₁) H hxI hyI]
  haveI :
      IsIso (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj xI)
        ((FibredCategoryMor.fiberFunctor G₁ U).obj yI)) :=
    comparison_stackification_presheafMap_isIso_on_source_image_of_precomposeIso
      (J := J) G₁ G₂ hG₁ hG₂ H α xI yI
  infer_instance


/-- Helper for Lemma 8.8.1: the pullback-cover family on a slice object generates a covering
sieve in `(J.over U) T`. This isolates the slice-site cover packaging from the later
componentwise-bijectivity proof. -/
theorem comparison_stackification_slice_pullback_cover_family_mem
    {U : C} (S : J.Cover U) (T : Over U) :
    (comparison_stackification_slice_pullback_cover_family (J := J) S T).toSieve ∈
      (J.over U) T := by
  -- Membership in the slice topology `J.over U` is membership of the pushforward sieve on
  -- `T.left`; the already-covering pullback cover `S.pullback T.hom` refines that pushforward.
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ (S.pullback T.hom).condition
  intro Z g hg
  let I : (S.pullback T.hom).Arrow := ⟨Z, g, hg⟩
  rw [Sieve.overEquiv_iff]
  change (comparison_stackification_slice_pullback_cover_family (J := J) S T).toSieve
      (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T)
  rw [SemiRepresentableFamily.Over.toSieve_ofArrows]
  exact Sieve.ofArrows_mk _ _ I

/-- Helper for Lemma 8.8.1: at a slice object `W : Over U`, the canonical Hom-presheaf comparison
map of `F` is bijective exactly when the fiberwise map of `F` over `W.left` is bijective between
the pulled-back objects `W.hom ^* x` and `W.hom ^* y`. This is the objectwise translation of the
`pullbackComparison`-conjugation formula for `fibredMorphismPresheafMap`. -/
theorem fibredMorphismPresheafMap_app_bijective_iff_fiberFunctor_map_bijective
    {X Y : FibredCategoryOver C}
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (W : Over U) :
    Function.Bijective ((fibredMorphismPresheafMap F x y).app (op W)) ↔
      Function.Bijective
        ((F.toHom.fiberFunctor W.left).map :
          (W.hom ^*[canonicalPullbackChoice X.p] x ⟶ W.hom ^*[canonicalPullbackChoice X.p] y) →
            ((F.toHom.fiberFunctor W.left).obj (W.hom ^*[canonicalPullbackChoice X.p] x) ⟶
              (F.toHom.fiberFunctor W.left).obj (W.hom ^*[canonicalPullbackChoice X.p] y))) := by
  -- The component is conjugation by the two pullback-comparison isomorphisms around the fiber map.
  let xW := W.hom ^*[canonicalPullbackChoice X.p] x
  let yW := W.hom ^*[canonicalPullbackChoice X.p] y
  let ex := FibredCategoryMor.pullbackComparison F W.hom x
  let ey := FibredCategoryMor.pullbackComparison F W.hom y
  let eCongr :
      ((F.toHom.fiberFunctor W.left).obj xW ⟶ (F.toHom.fiberFunctor W.left).obj yW) ≃
        ((canonicalFiberPseudofunctor Y.p).presheafHom
          ((F.toHom.fiberFunctor U).obj x)
          ((F.toHom.fiberFunctor U).obj y)).obj (op W) :=
    Iso.homCongr ex.symm ey.symm
  have hApp :
      (fibredMorphismPresheafMap F x y).app (op W) =
        fun δ : xW ⟶ yW ↦ eCongr ((F.toHom.fiberFunctor W.left).map δ) := by
    funext δ
    rfl
  rw [hApp]
  -- `app = eCongr ∘ fiberMap` with `eCongr` an equivalence, so bijectivity transfers both ways.
  constructor
  · intro hbij
    have : Function.Bijective
        (eCongr ∘ ((F.toHom.fiberFunctor W.left).map :
          (xW ⟶ yW) →
            ((F.toHom.fiberFunctor W.left).obj xW ⟶ (F.toHom.fiberFunctor W.left).obj yW))) :=
      hbij
    exact (Equiv.comp_bijective _ eCongr).1 this
  · intro hbij
    exact (Equiv.comp_bijective _ eCongr).2 hbij

/-- Helper for Lemma 8.8.1: bijectivity of a functor's map on a Hom-set is invariant under
replacing the source and target objects by isomorphic ones. -/
theorem functor_map_bijective_of_iso
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a a' b b' : A} (ea : a ≅ a') (eb : b ≅ b')
    (h : Function.Bijective
      ((F.map : (a' ⟶ b') → (F.obj a' ⟶ F.obj b')))) :
    Function.Bijective ((F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b))) := by
  -- Conjugate by `Iso.homCongr ea eb` on the source and `Iso.homCongr (F.mapIso ea) (F.mapIso eb)`
  -- on the target; functoriality makes the square commute, so bijectivity transfers.
  have hsq :
      (F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)) =
        (Iso.homCongr (F.mapIso ea) (F.mapIso eb)).symm ∘
          (F.map : (a' ⟶ b') → (F.obj a' ⟶ F.obj b')) ∘
          (Iso.homCongr ea eb) := by
    funext φ
    simp [Iso.homCongr, Functor.mapIso, Functor.map_comp]
  rw [hsq]
  exact ((Iso.homCongr (F.mapIso ea) (F.mapIso eb)).symm).bijective.comp
    (h.comp (Iso.homCongr ea eb).bijective)

/-- Helper for Lemma 8.8.1: at a slice object `W` whose leg `W.hom : W.left ⟶ U` lies in the
common-model cover `S`, the comparison Hom-presheaf map of `H` is objectwise bijective. The leg
itself is an arrow of `S`, so the pulled-back objects `W.hom ^* x`, `W.hom ^* y` admit common
source models over `W.left`, and the coverwise isomorphism lemma applies at the base `W.left`. -/
theorem comparison_stackification_presheafMap_app_bijective_of_leg_mem
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂)
    {U : C} (x y : Y₁.p.Fiber U)
    (S : J.Cover U)
    (hS :
      ∀ I : S.Arrow,
        ∃ xI yI : X.p.Fiber I.Y,
          Nonempty
            (((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅
              I.f ^*[canonicalPullbackChoice Y₁.p] x) ∧
          Nonempty
            (((FibredCategoryMor.fiberFunctor G₁ I.Y).obj yI) ≅
              I.f ^*[canonicalPullbackChoice Y₁.p] y))
    (W : Over U) (hW : S.1 W.hom) :
    Function.Bijective
      ((fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y).app (op W)) := by
  -- View the leg of `W` as an arrow of the cover `S`.
  let I : S.Arrow := ⟨W.left, W.hom, hW⟩
  -- Choose the common source models over `W.left` for the pulled-back objects.
  obtain ⟨xI, yI, ⟨hxI⟩, ⟨hyI⟩⟩ := hS I
  -- The coverwise isomorphism lemma applies at base `W.left` to the pulled-back objects.
  haveI hiso :
      IsIso (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
        (I.f ^*[canonicalPullbackChoice Y₁.p] x) (I.f ^*[canonicalPullbackChoice Y₁.p] y)) :=
    comparison_stackification_coverwise_presheafMap_isIso_of_local_models
      (J := J) G₁ G₂ hG₁ hG₂ H α (x := I.f ^*[canonicalPullbackChoice Y₁.p] x)
      (y := I.f ^*[canonicalPullbackChoice Y₁.p] y) hxI hyI
  -- Read off bijectivity of that natural iso at the identity slice object of `C/W.left`.
  have hbij_id :
      Function.Bijective
        ((fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
            (I.f ^*[canonicalPullbackChoice Y₁.p] x) (I.f ^*[canonicalPullbackChoice Y₁.p] y)).app
          (op (Over.mk (𝟙 W.left)))) := by
    rw [← isIso_iff_bijective]
    exact (NatTrans.isIso_iff_isIso_app _).mp hiso _
  -- Translate that to bijectivity of the fiber map of `H` over `W.left` between the
  -- `(𝟙 W.left)`-pullbacks of the `I.f`-pullbacks of `x` and `y`.
  rw [fibredMorphismPresheafMap_app_bijective_iff_fiberFunctor_map_bijective] at hbij_id
  -- The `(𝟙 W.left)`-pullback is canonically isomorphic to the object itself, so bijectivity
  -- transfers to the fiber map between `I.f ^* x` and `I.f ^* y`.
  have hbij_id' :
      Function.Bijective
        (((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor W.left).map :
          ((𝟙 W.left) ^*[canonicalPullbackChoice Y₁.p] (I.f ^*[canonicalPullbackChoice Y₁.p] x) ⟶
            (𝟙 W.left) ^*[canonicalPullbackChoice Y₁.p] (I.f ^*[canonicalPullbackChoice Y₁.p] y)) →
            _) := hbij_id
  have hbij_fiber :
      Function.Bijective
        (((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor W.left).map :
          (I.f ^*[canonicalPullbackChoice Y₁.p] x ⟶ I.f ^*[canonicalPullbackChoice Y₁.p] y) →
            (((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor W.left).obj
                (I.f ^*[canonicalPullbackChoice Y₁.p] x) ⟶
              ((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor W.left).obj
                (I.f ^*[canonicalPullbackChoice Y₁.p] y))) :=
    functor_map_bijective_of_iso
      ((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor W.left)
      ((canonicalPullbackChoice Y₁.p).pullbackIdComponentIso W.left
        (I.f ^*[canonicalPullbackChoice Y₁.p] x))
      ((canonicalPullbackChoice Y₁.p).pullbackIdComponentIso W.left
        (I.f ^*[canonicalPullbackChoice Y₁.p] y))
      hbij_id'
  -- Conclude bijectivity of the comparison-map component at `W` itself, whose leg is `W.hom = I.f`.
  rw [fibredMorphismPresheafMap_app_bijective_iff_fiberFunctor_map_bijective]
  exact hbij_fiber

/-- Helper for Lemma 8.8.1: a morphism of presheaves on the slice site `C/U` that is objectwise
surjective at every slice object whose leg lies in the cover `S` is locally surjective. The image
sieve of any section is refined by the `S`-pullback cover of the slice object. -/
theorem presheaf_isLocallySurjective_over_of_bijective_on_cover
    {X' Y' : FibredCategoryOver C}
    {U : C} {x y : X'.p.Fiber U} {x' y' : Y'.p.Fiber U}
    (f :
      (canonicalFiberPseudofunctor X'.p).presheafHom x y ⟶
        (canonicalFiberPseudofunctor Y'.p).presheafHom x' y')
    (S : J.Cover U)
    (hbij : ∀ (W : Over U), S.1 W.hom → Function.Surjective (f.app (op W))) :
    Presheaf.IsLocallySurjective (J.over U) f := by
  refine ⟨fun {T} s ↦ ?_⟩
  -- The image sieve of `s` contains the covering sieve coming from `S.pullback T.hom`.
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ (S.pullback T.hom).condition
  intro Z g hg
  rw [Sieve.overEquiv_iff]
  -- `g ≫ T.hom` lies in `S`, so `f` is surjective at the domain slice object `Over.mk (g ≫ T.hom)`.
  obtain ⟨t, ht⟩ :=
    hbij (Over.mk (g ≫ T.hom)) hg
      (((canonicalFiberPseudofunctor Y'.p).presheafHom x' y').map
        (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T).op s)
  exact ⟨t, ht⟩

/-- Helper for Lemma 8.8.1: a morphism of presheaves on the slice site `C/U` that is objectwise
injective at every slice object whose leg lies in the cover `S` is locally injective. The
equalizer sieve of any two equal-image sections is refined by the `S`-pullback cover. -/
theorem presheaf_isLocallyInjective_over_of_bijective_on_cover
    {X' Y' : FibredCategoryOver C}
    {U : C} {x y : X'.p.Fiber U} {x' y' : Y'.p.Fiber U}
    (f :
      (canonicalFiberPseudofunctor X'.p).presheafHom x y ⟶
        (canonicalFiberPseudofunctor Y'.p).presheafHom x' y')
    (S : J.Cover U)
    (hbij : ∀ (W : Over U), S.1 W.hom → Function.Injective (f.app (op W))) :
    Presheaf.IsLocallyInjective (J.over U) f := by
  refine ⟨fun {T} a b hab ↦ ?_⟩
  -- The equalizer sieve of `a, b` contains the covering sieve coming from `S.pullback T.unop.hom`.
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ (S.pullback T.unop.hom).condition
  intro Z g hg
  rw [Sieve.overEquiv_iff]
  -- `g ≫ T.unop.hom` lies in `S`, so `f` is injective at `Over.mk (g ≫ T.unop.hom)`; combined with
  -- naturality of `f` and `hab`, the two restricted sections coincide.
  refine hbij (Over.mk (g ≫ T.unop.hom)) hg ?_
  -- By naturality of `f`, both restricted sections are images of `f.app T a`, `f.app T b`, which
  -- coincide by `hab`.
  let m : (T : (Over U)ᵒᵖ) ⟶ op (Over.mk (g ≫ T.unop.hom)) :=
    (Over.homMk g : Over.mk (g ≫ T.unop.hom) ⟶ T.unop).op
  calc
    (f.app (op (Over.mk (g ≫ T.unop.hom))))
        ((((canonicalFiberPseudofunctor X'.p).presheafHom x y).map m) a)
        = (((canonicalFiberPseudofunctor Y'.p).presheafHom x' y').map m) ((f.app T) a) :=
      NatTrans.naturality_apply f m a
    _ = (((canonicalFiberPseudofunctor Y'.p).presheafHom x' y').map m) ((f.app T) b) :=
      congrArg (((canonicalFiberPseudofunctor Y'.p).presheafHom x' y').map m) hab
    _ = (f.app (op (Over.mk (g ≫ T.unop.hom))))
        ((((canonicalFiberPseudofunctor X'.p).presheafHom x y).map m) b) :=
      (NatTrans.naturality_apply f m b).symm

/-- Helper for Lemma 8.8.1: to prove full faithfulness of a direct comparison morphism between two
stackifications, it remains to globalize the already-finished source-image Hom-presheaf
isomorphism to arbitrary target objects of `Y₁`. -/
theorem comparison_stackification_presheafMap_W_of_common_local_models
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂)
    {U : C} (x y : Y₁.p.Fiber U)
    (S : J.Cover U)
    (hS :
      ∀ I : S.Arrow,
        ∃ xI yI : X.p.Fiber I.Y,
          Nonempty
            (((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅
              I.f ^*[canonicalPullbackChoice Y₁.p] x) ∧
          Nonempty
            (((FibredCategoryMor.fiberFunctor G₁ I.Y).obj yI) ≅
              I.f ^*[canonicalPullbackChoice Y₁.p] y)) :
    (J.over U).W
      (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) := by
  -- On every slice object whose leg lies in `S`, the comparison map is objectwise bijective by the
  -- coverwise isomorphism lemma applied at that base.
  have hbij :
      ∀ (W : Over U), S.1 W.hom →
        Function.Bijective
          ((fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y).app (op W)) :=
    fun W hW ↦
      comparison_stackification_presheafMap_app_bijective_of_leg_mem
        (J := J) G₁ G₂ hG₁ hG₂ H α x y S hS W hW
  -- A presheaf map that is objectwise bijective on every member of the `S`-pullback cover of each
  -- slice object is both locally injective and locally surjective, hence lies in `W`.
  haveI hsurj :
      Presheaf.IsLocallySurjective (J.over U)
        (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) :=
    presheaf_isLocallySurjective_over_of_bijective_on_cover
      (J := J) _ S (fun W hW ↦ (hbij W hW).2)
  haveI hinj :
      Presheaf.IsLocallyInjective (J.over U)
        (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) :=
    presheaf_isLocallyInjective_over_of_bijective_on_cover
      (J := J) _ S (fun W hW ↦ (hbij W hW).1)
  -- Both Hom presheaves are sheaves on the slice site (`Y₁`, `Y₂` are stacks ⟹ prestacks). A
  -- locally bijective morphism between sheaves is an isomorphism, hence lies in `W`.
  have hSrc :
      Presheaf.IsSheaf (J.over U)
        ((canonicalFiberPseudofunctor Y₁.p).presheafHom x y) :=
    Pseudofunctor.IsPrestack.isSheaf
      (F := canonicalFiberPseudofunctor Y₁.p) (J := J) (S := U) x y
  have hTgt :
      Presheaf.IsSheaf (J.over U)
        ((canonicalFiberPseudofunctor Y₂.p).presheafHom
          (((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor U).obj x)
          (((stack_morphism_toFibredCategoryMor H).toHom.fiberFunctor U).obj y)) :=
    Pseudofunctor.IsPrestack.isSheaf
      (F := canonicalFiberPseudofunctor Y₂.p) (J := J) (S := U) _ _
  -- Bundle the comparison map as a morphism of sheaves and read off `IsIso` from local bijectivity.
  let fSheaf :
      (⟨_, hSrc⟩ : Sheaf (J.over U) (Type _)) ⟶ ⟨_, hTgt⟩ :=
    ⟨fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y⟩
  haveI : Presheaf.IsLocallyInjective (J.over U)
      ((sheafToPresheaf (J.over U) (Type _)).map fSheaf) := hinj
  haveI : Presheaf.IsLocallySurjective (J.over U)
      ((sheafToPresheaf (J.over U) (Type _)).map fSheaf) := hsurj
  haveI hisoSheaf : IsIso fSheaf :=
    (Sheaf.isLocallyBijective_iff_isIso fSheaf).1 ⟨inferInstance, inferInstance⟩
  haveI : IsIso (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) :=
    (sheafToPresheaf (J.over U) (Type _)).map_isIso fSheaf
  exact (ObjectProperty.isLocal_iff_isIso
    (P := Presheaf.IsSheaf (J.over U)) _ hSrc hTgt).2 inferInstance

/-- Helper for Lemma 8.8.1: once the common-cover comparison map is globalized to a `W`
statement on the slice site, the stack Hom-sheaf property upgrades it to an actual isomorphism.
This isolates the final sheaf argument from the still-missing coverwise globalization step. -/
theorem comparison_stackification_presheafMap_isIso_of_w
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂)
    {U : C} (x y : Y₁.p.Fiber U)
    (hW :
      (J.over U).W
        (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y)) :
    IsIso (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) := by
  -- Both Hom presheaves are sheaves on the slice site (stacks), so a `W`-map is an isomorphism.
  exact stack_hom_presheafMap_isIso_of_W (J := J) H x y hW

-- Route correction: the remaining uniqueness-side blocker is exactly the source-faithful local
-- model argument for arbitrary objects of `Y₁`, not another round of the arbitrary-target
-- precomposition-equivalence proof.
theorem comparison_stackification_presheafMap_isIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂)
    {U : C} (x y : Y₁.p.Fiber U) :
    IsIso (fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H) x y) := by
  -- Choose a common cover on which both `x` and `y` admit local source models, globalize the
  -- source-image comparison isomorphism to a `W`-statement on the slice site, then upgrade that
  -- `W`-statement to an actual isomorphism via the stack Hom-sheaf property.
  obtain ⟨S, hS⟩ := stackification_common_local_models (J := J) G₁ hG₁ x y
  exact
    comparison_stackification_presheafMap_isIso_of_w (J := J) G₁ G₂ hG₁ hG₂ H α x y
      (comparison_stackification_presheafMap_W_of_common_local_models
        (J := J) G₁ G₂ hG₁ hG₂ H α x y S hS)

end

end CategoryTheory
