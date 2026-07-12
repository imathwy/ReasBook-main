import StacksProject_2024.Chap08.Lemma_8_8_1.Criteria
import StacksProject_2024.Chap08.Lemma_8_4_8
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

/-- Helper for Lemma 8.8.1: at the identity object of the slice site `C/U`, the canonical
Hom-presheaf comparison map agrees with the ordinary map on fiber morphisms. -/
-- Evaluate `fibredMorphismPresheafMap` at `Over.mk (𝟙 U)` and normalize the two
-- pullback-comparison isomorphisms over the identity to recover the plain fiber-functor map.
-- Both sides reduce, via strong-cartesian uniqueness against the chosen pullback of `F(y)` over
-- `𝟙 U`, to the common composite `(canonicalPullbackChoice Y.p).map (𝟙 U) (F x) ≫ F.map φ`.
theorem fibredMorphismPresheafMap_app_id_local
    {X Y : FibredCategoryOver C}
    (F : X ⟶ Y)
    {U : C} (x y : X.p.Fiber U)
    (φ : x ⟶ y) :
    (fibredMorphismPresheafMap F x y).app (Opposite.op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv φ) =
      (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv
        ((FibredCategoryMor.fiberFunctor F U).map φ) := by
  simp only [fibredMorphismPresheafMap, Pseudofunctor.presheafHomObjHomEquiv]
  apply Functor.Fiber.hom_ext
  -- Reduce both sides to explicit `pullbackIdComponentIso` / `pullbackComparison` composites.
  change
    ((FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom ≫
        (F.toHom.fiberFunctor U).map
          ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv ≫
            φ ≫ (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom) ≫
        (FibredCategoryMor.pullbackComparison F (𝟙 U) y).inv).1 =
      ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
            ((F.toHom.fiberFunctor U).obj x)).inv ≫
          (F.toHom.fiberFunctor U).map φ ≫
          (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
            ((F.toHom.fiberFunctor U).obj y)).hom).1
  change
    (FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 ≫
        F.toHom.map
          ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
            φ.1 ≫ (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1) ≫
        (FibredCategoryMor.pullbackComparison F (𝟙 U) y).inv.1 =
      (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
            ((F.toHom.fiberFunctor U).obj x)).inv.1 ≫
          F.toHom.map φ.1 ≫
          (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
            ((F.toHom.fiberFunctor U).obj y)).hom.1
  letI hSC : Y.p.IsStronglyCartesian (𝟙 U)
      ((canonicalPullbackChoice Y.p).map (𝟙 U) ((F.toHom.fiberFunctor U).obj y)) :=
    (canonicalPullbackChoice Y.p).isStronglyCartesian (𝟙 U) ((F.toHom.fiberFunctor U).obj y)
  letI hl_lhs : Y.p.IsHomLift (𝟙 U)
      ((FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 ≫
        F.toHom.map
          ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
            φ.1 ≫ (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1) ≫
        (FibredCategoryMor.pullbackComparison F (𝟙 U) y).inv.1) := by
    have h1 : Y.p.IsHomLift (𝟙 U) (FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 :=
      (FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.2
    have hδ :
        (X.toBasedCategory).p.IsHomLift (𝟙 U)
          ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
            φ.1 ≫ (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1) :=
      ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv ≫
          φ ≫ (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom).2
    have h2 :
        Y.p.IsHomLift (𝟙 U)
          (F.toHom.map
            ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
              φ.1 ≫
              (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1)) :=
      F.toHom.preserves_isHomLift (𝟙 U) _
    have h3 : Y.p.IsHomLift (𝟙 U) (FibredCategoryMor.pullbackComparison F (𝟙 U) y).inv.1 :=
      (FibredCategoryMor.pullbackComparison F (𝟙 U) y).inv.2
    have h23 := @CategoryTheory.IsHomLift.comp_of_lift_id _ _ _ _ Y.p U _ _ _ _ _ h2 h3
    exact @CategoryTheory.IsHomLift.comp_of_lift_id _ _ _ _ Y.p U _ _ _ _ _ h1 h23
  letI hl_rhs : Y.p.IsHomLift (𝟙 U)
      ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
            ((F.toHom.fiberFunctor U).obj x)).inv.1 ≫
        F.toHom.map φ.1 ≫
        (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
          ((F.toHom.fiberFunctor U).obj y)).hom.1) := by
    have h1 : Y.p.IsHomLift (𝟙 U)
        (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
          ((F.toHom.fiberFunctor U).obj x)).inv.1 :=
      (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
        ((F.toHom.fiberFunctor U).obj x)).inv.2
    have hφ : (X.toBasedCategory).p.IsHomLift (𝟙 U) φ.1 := φ.2
    have h2 : Y.p.IsHomLift (𝟙 U) (F.toHom.map φ.1) := F.toHom.preserves_isHomLift (𝟙 U) _
    have h3 : Y.p.IsHomLift (𝟙 U)
        (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
          ((F.toHom.fiberFunctor U).obj y)).hom.1 :=
      (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
        ((F.toHom.fiberFunctor U).obj y)).hom.2
    have h23 := @CategoryTheory.IsHomLift.comp_of_lift_id _ _ _ _ Y.p U _ _ _ _ _ h2 h3
    exact @CategoryTheory.IsHomLift.comp_of_lift_id _ _ _ _ Y.p U _ _ _ _ _ h1 h23
  refine Functor.IsStronglyCartesian.ext Y.p (𝟙 U)
    ((canonicalPullbackChoice Y.p).map (𝟙 U) ((F.toHom.fiberFunctor U).obj y)) (𝟙 U) ?_
  have hRHS :
      ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
            ((F.toHom.fiberFunctor U).obj x)).inv.1 ≫
          F.toHom.map φ.1 ≫
          (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice Y.p) U
            ((F.toHom.fiberFunctor U).obj y)).hom.1) ≫
        (canonicalPullbackChoice Y.p).map (𝟙 U) ((F.toHom.fiberFunctor U).obj y) =
      (canonicalPullbackChoice Y.p).map (𝟙 U) ((F.toHom.fiberFunctor U).obj x) ≫
        F.toHom.map φ.1 := by
    rw [Category.assoc, Category.assoc]
    erw [PullbackChoice.pullbackIdComponentIso_fac, Category.comp_id]
    conv_lhs => rw [PullbackChoice.pullbackIdComponentIso_inv_eq]
    rfl
  have hX :
      ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
            φ.1 ≫
            (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1) ≫
          (canonicalPullbackChoice X.p).map (𝟙 U) y =
        (canonicalPullbackChoice X.p).map (𝟙 U) x ≫ φ.1 := by
    rw [Category.assoc, Category.assoc]
    erw [PullbackChoice.pullbackIdComponentIso_fac, Category.comp_id]
    rw [PullbackChoice.pullbackIdComponentIso_inv_eq]
  have hFX :
      F.toHom.map
            ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
              φ.1 ≫
              (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map (𝟙 U) y) =
        F.toHom.map ((canonicalPullbackChoice X.p).map (𝟙 U) x) ≫ F.toHom.map φ.1 := by
    rw [← F.toHom.toFunctor.map_comp, ← F.toHom.toFunctor.map_comp, hX]
  have hLHS :
      ((FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 ≫
          F.toHom.map
            ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
              φ.1 ≫
              (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1) ≫
          (FibredCategoryMor.pullbackComparison F (𝟙 U) y).inv.1) ≫
        (canonicalPullbackChoice Y.p).map (𝟙 U) ((F.toHom.fiberFunctor U).obj y) =
      (canonicalPullbackChoice Y.p).map (𝟙 U) ((F.toHom.fiberFunctor U).obj x) ≫
        F.toHom.map φ.1 := by
    rw [Category.assoc, Category.assoc]
    erw [FibredCategoryMor.pullbackComparison_inv_postcompose_owner]
    calc
      (FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 ≫
            F.toHom.map
              ((PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U x).inv.1 ≫
                φ.1 ≫
                (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice X.p) U y).hom.1) ≫
              F.toHom.map ((canonicalPullbackChoice X.p).map (𝟙 U) y)
          = (FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 ≫
              F.toHom.map ((canonicalPullbackChoice X.p).map (𝟙 U) x) ≫ F.toHom.map φ.1 :=
            congrArg ((FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 ≫ ·) hFX
      _ = ((FibredCategoryMor.pullbackComparison F (𝟙 U) x).hom.1 ≫
              F.toHom.map ((canonicalPullbackChoice X.p).map (𝟙 U) x)) ≫ F.toHom.map φ.1 :=
            (Category.assoc _ _ _).symm
      _ = (canonicalPullbackChoice Y.p).map (𝟙 U) ((F.toHom.fiberFunctor U).obj x) ≫
              F.toHom.map φ.1 :=
            congrArg (· ≫ F.toHom.map φ.1)
              (FibredCategoryMor.pullbackComparison_hom_postcompose F (𝟙 U) x)
  rw [hLHS, hRHS]

/-- Helper for Lemma 8.8.1: a morphism of fibred categories is fully faithful exactly when all of
its fiberwise Hom-presheaf comparison maps are isomorphisms. This local owner-level bridge keeps
this file independent of the currently broken aggregate import for Lemma `8.4.7`. -/
theorem fibredCategoryMor_fullyFaithful_iff_fibredMorphismPresheafMap_isIso
    {X Y : FibredCategoryOver C}
    (F : X ⟶ Y) :
    Nonempty F.toHom.FullyFaithful ↔
      ∀ ⦃U : C⦄ (x y : X.p.Fiber U),
        IsIso (fibredMorphismPresheafMap F x y) := by
  constructor
  · intro hF U x y
    -- The forward direction is exactly the owner-level Hom-presheaf isomorphism criterion for
    -- a fully faithful morphism of fibred categories.
    exact fibredMorphismPresheafMap_isIso_of_fullyFaithful_local F hF x y
  · intro hF
    -- Evaluate the Hom-presheaf comparison at the identity object of `C/U` to recover the
    -- fiberwise map on morphism sets, then use the standard fiberwise full-faithfulness test.
    refine (FibredCategoryMor.fullyFaithful_iff_fiberwise F).2 ?_
    intro U
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro x y
    let eX :
        (x ⟶ y) ≃
          ((canonicalFiberPseudofunctor X.p).presheafHom x y).obj
            (Opposite.op (Over.mk (𝟙 U))) :=
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
    let eY :
        ((FibredCategoryMor.fiberFunctor F U).obj x ⟶
            (FibredCategoryMor.fiberFunctor F U).obj y) ≃
          ((canonicalFiberPseudofunctor Y.p).presheafHom
              ((FibredCategoryMor.fiberFunctor F U).obj x)
              ((FibredCategoryMor.fiberFunctor F U).obj y)).obj
            (Opposite.op (Over.mk (𝟙 U))) :=
      (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv
    let map :
        (x ⟶ y) →
          ((FibredCategoryMor.fiberFunctor F U).obj x ⟶
            (FibredCategoryMor.fiberFunctor F U).obj y) :=
      (FibredCategoryMor.fiberFunctor F U).map
    let app :=
      (fibredMorphismPresheafMap F x y).app (Opposite.op (Over.mk (𝟙 U)))
    have hApp :
        Function.Bijective app := by
      rw [← isIso_iff_bijective]
      exact
        (NatTrans.isIso_iff_isIso_app (fibredMorphismPresheafMap F x y)).mp
          (hF x y) _
    have hApp_id (φ : x ⟶ y) :
        app (eX φ) = eY (map φ) := by
      exact fibredMorphismPresheafMap_app_id_local F x y φ
    have hAppComp : Function.Bijective (app ∘ eX) :=
      (Equiv.bijective_comp eX app).2 hApp
    have hCompEq : app ∘ eX = eY ∘ map := by
      funext φ
      exact hApp_id φ
    have hMapComp : Function.Bijective (eY ∘ map) := by
      rw [← hCompEq]
      exact hAppComp
    exact (Equiv.comp_bijective map eY).1 hMapComp

-- (The discarded "arbitrary-target precomposition universal property" route — the lemmas
-- `local_stackification_exists_lift_to_stack_of_precompose_isEquivalence`,
-- `local_stackification_precompose_fullFaithful/essSurj/isEquivalence` — has been removed; the
-- file proves uniqueness via the direct comparison morphism instead, so these were dead.)

/-- Helper for Lemma 8.8.1: a morphism of stacks is fully faithful once its fiberwise Hom-presheaf
comparison maps are all isomorphisms. -/
theorem stack_morphism_fullyFaithful_of_fibredMorphismPresheafMap_isIso
    {Y₁ Y₂ : StackOver J}
    (H : Y₁ ⟶ Y₂)
    (hH :
      ∀ ⦃U : C⦄ (x y : Y₁.p.Fiber U),
        IsIso (fibredMorphismPresheafMap
          (InducedCategory.Hom.toFibredCategoryMor H) x y)) :
    Nonempty (InducedCategory.Hom.toBasedFunctor H).FullyFaithful := by
  -- Translate full faithfulness to the owner-level Hom-presheaf criterion from Lemma `8.4.7`.
  exact
    (fibredCategoryMor_fullyFaithful_iff_fibredMorphismPresheafMap_isIso
      (F := InducedCategory.Hom.toFibredCategoryMor H)).2
      (fun {_} x y ↦ hH x y)

/-- Helper for Lemma 8.8.1: once a comparison morphism of stacks is fully faithful, local
essential surjectivity upgrades it to an equivalence over the base. -/
theorem stack_morphism_fiberFunctor_fullyFaithful_of_fullyFaithful
    {Y₁ Y₂ : StackOver J}
    (H : Y₁ ⟶ Y₂)
    (hff : Nonempty (InducedCategory.Hom.toBasedFunctor H).FullyFaithful)
    (U : C) :
    Nonempty ((InducedCategory.Hom.fiberFunctor H U).FullyFaithful) := by
  -- Restrict the global full-faithfulness owner to the fixed fiber over `U`.
  simpa [InducedCategory.Hom.fiberFunctor, InducedCategory.Hom.toBasedFunctor,
    InducedCategory.Hom.toFibredCategoryMor] using
    (FibredCategoryMor.fullyFaithful_iff_fiberwise
      (F := InducedCategory.Hom.toFibredCategoryMor H)).1 hff U

/-- Helper for Lemma 8.8.1: on a fixed fiber, a fully faithful stack morphism induces a
bijection on morphism sets. This packages the concrete fiberwise lifting interface needed by the
blocked equivalence-over-base argument. -/
theorem stack_morphism_fiberFunctor_map_bijective_of_fullyFaithful
    {Y₁ Y₂ : StackOver J}
    (H : Y₁ ⟶ Y₂)
    (hff : Nonempty (InducedCategory.Hom.toBasedFunctor H).FullyFaithful)
    (U : C)
    (x y : Y₁.p.Fiber U) :
    Function.Bijective
      ((InducedCategory.Hom.fiberFunctor H U).map :
        (x ⟶ y) →
          ((InducedCategory.Hom.fiberFunctor H U).obj x ⟶
            (InducedCategory.Hom.fiberFunctor H U).obj y)) := by
  rcases
    stack_morphism_fiberFunctor_fullyFaithful_of_fullyFaithful
      (J := J) H hff U with ⟨hFFU⟩
  exact hFFU.map_bijective x y

-- This is exactly the `←` direction of Lemma 8.4.8 (Tag 046N): full faithfulness plus local
-- essential surjectivity on objects of a stack morphism is an equivalence over the base. The
-- object-descent argument lives in `Lemma_8_4_8`.
theorem stack_morphism_isEquivalenceOverBase_of_fullyFaithful_of_locallyEssentiallySurjective
    {Y₁ Y₂ : StackOver J}
    (H : Y₁ ⟶ Y₂)
    (hff : Nonempty (InducedCategory.Hom.toBasedFunctor H).FullyFaithful)
    (hess : InducedCategory.Hom.LocallyEssentiallySurjectiveOnObjects J H) :
    InducedCategory.Hom.IsEquivalenceOverBase H :=
  (isEquivalenceOverBase_iff_locallyEssentiallySurjectiveOnObjects_of_fullyFaithful H hff).2 hess

/-- Helper for Lemma 8.8.1: the identity morphism of a stack already satisfies the two
stackification clauses. This is the normalization used to diagnose whether later uniqueness
helpers have the right statement shape. -/
theorem stack_identity_isStackification
    (Y : StackOver J) :
    FibredCategoryMor.IsStackification
      (𝟙 Y.toFibredCategoryOver : Y.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) := by
  refine ⟨?_, ?_⟩
  · intro U x y
    -- The identity morphism is fully faithful, so its Hom-presheaf comparison is already an
    -- isomorphism and hence belongs to `(J.over U).W`.
    have hIdFF :
        Nonempty
          ((𝟙 Y.toFibredCategoryOver :
              Y.toFibredCategoryOver ⟶ Y.toFibredCategoryOver).toHom.FullyFaithful) := by
      change Nonempty ((𝟭 Y.toBasedCategory).FullyFaithful)
      exact ⟨Functor.FullyFaithful.id _⟩
    have hIdIso :
        IsIso
          (fibredMorphismPresheafMap
            (𝟙 Y.toFibredCategoryOver : Y.toFibredCategoryOver ⟶ Y.toFibredCategoryOver)
            x y) :=
      (fibredCategoryMor_fullyFaithful_iff_fibredMorphismPresheafMap_isIso
        (F := (𝟙 Y.toFibredCategoryOver :
          Y.toFibredCategoryOver ⟶ Y.toFibredCategoryOver))).1 hIdFF x y
    let _ :
        IsIso
          (fibredMorphismPresheafMap
            (𝟙 Y.toFibredCategoryOver : Y.toFibredCategoryOver ⟶ Y.toFibredCategoryOver)
            x y) := hIdIso
    exact
      (J.over U).W.of_isIso
        (fibredMorphismPresheafMap
          (𝟙 Y.toFibredCategoryOver : Y.toFibredCategoryOver ⟶ Y.toFibredCategoryOver)
          x y)
  · intro U y
    -- For the identity, each restricted target object is already literally in the essential image
    -- on the trivial cover.
    refine ⟨⊤, ?_⟩
    intro I
    refine ⟨I.f ^*[canonicalPullbackChoice Y.p] y, ?_⟩
    simpa using ⟨Iso.refl (I.f ^*[canonicalPullbackChoice Y.p] y)⟩


/-- Helper for Lemma 8.8.1: an equivalence over the base induces isomorphisms on all fiberwise
Hom-presheaf comparison maps. -/
theorem fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase
    {X₁ X₂ : FibredCategoryOver C}
    (F : X₁ ⟶ X₂)
    (hF : FibredCategoryMor.IsEquivalenceOverBase F)
    {U : C} (x y : X₁.p.Fiber U) :
    IsIso (fibredMorphismPresheafMap F x y) := by
  -- Route correction: reuse the Chapter 8 fully-faithful Hom-presheaf criterion instead of
  -- maintaining a second manual componentwise-bijectivity proof here.
  -- Reinterpret the equivalence-over-base hypothesis as full faithfulness for the underlying
  -- based functor, then invoke the existing owner-level Hom-presheaf isomorphism lemma.
  have hFF : Nonempty F.toHom.FullyFaithful := by
    let _ : F.toHom.IsEquivalence :=
      BasedFunctor.isEquivalence_of_isEquivalenceOverBase F.toHom hF
    exact ⟨Functor.FullyFaithful.ofFullyFaithful F.toHom.toFunctor⟩
  exact
    (fibredCategoryMor_fullyFaithful_iff_fibredMorphismPresheafMap_isIso
      (F := F)).1 hFF x y

/-- Helper for Lemma 8.8.1: the pullback-comparison isomorphism for a composite fibred-category
morphism is the composite of the two pullback-comparison isomorphisms. -/
theorem pullbackComparison_comp_hom
    {X₁ X₂ X₃ : FibredCategoryOver C}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U V : C} (f : V ⟶ U) (x : X₁.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison (F ≫ G) f x).hom =
      (FibredCategoryMor.pullbackComparison G f ((FibredCategoryMor.fiberFunctor F U).obj x)).hom ≫
        (FibredCategoryMor.fiberFunctor G V).map
          (FibredCategoryMor.pullbackComparison F f x).hom := by
  let eF := FibredCategoryMor.pullbackComparison F f x
  let eG :=
    FibredCategoryMor.pullbackComparison G f ((FibredCategoryMor.fiberFunctor F U).obj x)
  let eGF := FibredCategoryMor.pullbackComparison (F ≫ G) f x
  have hcomp :
      eG.hom ≫ (FibredCategoryMor.fiberFunctor G V).map eF.hom = eGF.hom := by
    -- Compare the composite boundary with the direct boundary after postcomposition by the
    -- image of the chosen source pullback arrow; the explicit cartesian lift avoids instance
    -- search on the wrong chosen target pullback.
    apply Functor.Fiber.hom_ext
    let θ := (F ≫ G).toHom.map ((canonicalPullbackChoice X₁.p).map f x)
    have hθ : X₃.p.IsStronglyCartesian f θ := by
      change X₃.p.IsStronglyCartesian f
        (G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)))
      exact
        FibredCategoryMor.map_stronglyCartesian_of_lift
          G f
          (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x))
          (FibredCategoryMor.map_stronglyCartesian_of_lift
            F f ((canonicalPullbackChoice X₁.p).map f x)
            ((canonicalPullbackChoice X₁.p).isStronglyCartesian f x))
    have hleft : X₃.p.IsHomLift (𝟙 V)
        (eG.hom.1 ≫ ((FibredCategoryMor.fiberFunctor G V).map eF.hom).1) := by
      exact (eG.hom ≫ (FibredCategoryMor.fiberFunctor G V).map eF.hom).2
    have hright : X₃.p.IsHomLift (𝟙 V) eGF.hom.1 := by
      exact eGF.hom.2
    have hpost :
        (eG.hom.1 ≫ ((FibredCategoryMor.fiberFunctor G V).map eF.hom).1) ≫ θ =
          eGF.hom.1 ≫ θ := by
      have hF :
          eF.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X₁.p).map f x) =
            (canonicalPullbackChoice X₂.p).map f
              ((FibredCategoryMor.fiberFunctor F U).obj x) := by
        simpa only [eF] using
          FibredCategoryMor.pullbackComparison_hom_postcompose F f x
      have hG :
          eG.hom.1 ≫ G.toHom.map
              ((canonicalPullbackChoice X₂.p).map f
                ((FibredCategoryMor.fiberFunctor F U).obj x)) =
            (canonicalPullbackChoice X₃.p).map f
              ((FibredCategoryMor.fiberFunctor G U).obj
                ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
        simpa only [eG] using
          FibredCategoryMor.pullbackComparison_hom_postcompose G f
            ((FibredCategoryMor.fiberFunctor F U).obj x)
      have hGF :
          eGF.hom.1 ≫ θ =
            (canonicalPullbackChoice X₃.p).map f
              ((FibredCategoryMor.fiberFunctor G U).obj
                ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
        simpa only [eGF, θ, BasedFunctor.comp] using
          FibredCategoryMor.pullbackComparison_hom_postcompose (F ≫ G) f x
      change
        (eG.hom.1 ≫ G.toHom.map eF.hom.1) ≫
            G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) =
          eGF.hom.1 ≫ θ
      have hstep₁ :
          (eG.hom.1 ≫ G.toHom.map eF.hom.1) ≫
              G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) =
            eG.hom.1 ≫
              G.toHom.map
                (eF.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) := by
        rw [Functor.map_comp]
        exact Category.assoc eG.hom.1 (G.toHom.map eF.hom.1)
          (G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)))
      have hstep₂ :
          eG.hom.1 ≫
              G.toHom.map
                (eF.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) =
            eG.hom.1 ≫
              G.toHom.map
                ((canonicalPullbackChoice X₂.p).map f
                  ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
        exact congrArg (fun m ↦ eG.hom.1 ≫ G.toHom.map m) hF
      exact hstep₁.trans (hstep₂.trans (hG.trans hGF.symm))
    exact
      @Functor.IsStronglyCartesian.ext _ _ _ _ X₃.p _ _ _ _
        f θ hθ _ _ (𝟙 V)
        (eG.hom.1 ≫ ((FibredCategoryMor.fiberFunctor G V).map eF.hom).1)
        eGF.hom.1 hleft hright hpost
  exact hcomp.symm

/-- Helper for Lemma 8.8.1: the inverse of the pullback-comparison isomorphism for a composite
fibred-category morphism is the reverse composite of the inverse comparisons. -/
theorem pullbackComparison_comp_inv
    {X₁ X₂ X₃ : FibredCategoryOver C}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U V : C} (f : V ⟶ U) (x : X₁.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison (F ≫ G) f x).inv =
      (FibredCategoryMor.fiberFunctor G V).map
          (FibredCategoryMor.pullbackComparison F f x).inv ≫
        (FibredCategoryMor.pullbackComparison G f
          ((FibredCategoryMor.fiberFunctor F U).obj x)).inv := by
  let eF := FibredCategoryMor.pullbackComparison F f x
  let eG :=
    FibredCategoryMor.pullbackComparison G f ((FibredCategoryMor.fiberFunctor F U).obj x)
  let eGF := FibredCategoryMor.pullbackComparison (F ≫ G) f x
  have hhom :
      eGF.hom = eG.hom ≫ (FibredCategoryMor.fiberFunctor G V).map eF.hom := by
    simpa only [eF, eG, eGF] using pullbackComparison_comp_hom F G f x
  -- Postcompose both candidate inverses with the composite comparison hom; the two inverse
  -- identities then reduce the goal to functoriality of `G` on the inverse of `eF`.
  rw [← cancel_mono eGF.hom]
  calc
    eGF.inv ≫ eGF.hom = 𝟙 _ := by
      simp only [Iso.inv_hom_id]
    _ =
        ((FibredCategoryMor.fiberFunctor G V).map eF.inv ≫ eG.inv) ≫ eGF.hom := by
      rw [hhom]
      symm
      calc
        ((FibredCategoryMor.fiberFunctor G V).map eF.inv ≫ eG.inv) ≫ eG.hom ≫
            (FibredCategoryMor.fiberFunctor G V).map eF.hom =
          (FibredCategoryMor.fiberFunctor G V).map eF.inv ≫
            (eG.inv ≫ eG.hom) ≫
              (FibredCategoryMor.fiberFunctor G V).map eF.hom := by
            simp only [Category.assoc]
        _ = 𝟙 _ := by
          simp only [Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]

/-- Helper for Lemma 8.8.1: the Hom-presheaf map attached to a composite of fibred-category
morphisms agrees pointwise with the composite of the two Hom-presheaf maps. -/
theorem fibredMorphismPresheafMap_comp_app
    {X₁ X₂ X₃ : FibredCategoryOver C}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U : C} (x y : X₁.p.Fiber U)
    (W : (Over U)ᵒᵖ)
    (δ : ((canonicalFiberPseudofunctor X₁.p).presheafHom x y).obj W) :
    (FibredCategoryMor.fibredMorphismPresheafMap (F ≫ G) x y).app W δ =
      (FibredCategoryMor.fibredMorphismPresheafMap F x y ≫
        FibredCategoryMor.fibredMorphismPresheafMap G
          ((FibredCategoryMor.fiberFunctor F U).obj x)
          ((FibredCategoryMor.fiberFunctor F U).obj y)).app W δ := by
  -- Normalize the natural transformations to their app-level comparison shells.
  simp only [FibredCategoryMor.fibredMorphismPresheafMap, NatTrans.comp_app]
  -- Rewrite the composite comparison on both endpoints and then use functoriality in the
  -- middle vertical morphism.
  change
    (FibredCategoryMor.pullbackComparison (F ≫ G) W.unop.hom x).hom ≫
        (FibredCategoryMor.fiberFunctor (F ≫ G) W.unop.left).map δ ≫
          (FibredCategoryMor.pullbackComparison (F ≫ G) W.unop.hom y).inv =
      (FibredCategoryMor.pullbackComparison G W.unop.hom
          ((FibredCategoryMor.fiberFunctor F U).obj x)).hom ≫
        (FibredCategoryMor.fiberFunctor G W.unop.left).map
          ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
            (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫
              (FibredCategoryMor.pullbackComparison F W.unop.hom y).inv) ≫
          (FibredCategoryMor.pullbackComparison G W.unop.hom
            ((FibredCategoryMor.fiberFunctor F U).obj y)).inv
  rw [pullbackComparison_comp_hom F G W.unop.hom x]
  rw [pullbackComparison_comp_inv F G W.unop.hom y]
  simp only [Functor.map_comp]
  change
      ((FibredCategoryMor.pullbackComparison G W.unop.hom
            ((FibredCategoryMor.fiberFunctor F U).obj x)).hom ≫
          (FibredCategoryMor.fiberFunctor G W.unop.left).map
            (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom) ≫
        (FibredCategoryMor.fiberFunctor G W.unop.left).map
          ((FibredCategoryMor.fiberFunctor F W.unop.left).map δ) ≫
          (FibredCategoryMor.fiberFunctor G W.unop.left).map
            (FibredCategoryMor.pullbackComparison F W.unop.hom y).inv ≫
            (FibredCategoryMor.pullbackComparison G W.unop.hom
              ((FibredCategoryMor.fiberFunctor F U).obj y)).inv =
      (FibredCategoryMor.pullbackComparison G W.unop.hom
          ((FibredCategoryMor.fiberFunctor F U).obj x)).hom ≫
        ((FibredCategoryMor.fiberFunctor G W.unop.left).map
            (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
          (FibredCategoryMor.fiberFunctor G W.unop.left).map
            ((FibredCategoryMor.fiberFunctor F W.unop.left).map δ) ≫
          (FibredCategoryMor.fiberFunctor G W.unop.left).map
            (FibredCategoryMor.pullbackComparison F W.unop.hom y).inv) ≫
        (FibredCategoryMor.pullbackComparison G W.unop.hom
          ((FibredCategoryMor.fiberFunctor F U).obj y)).inv
  simp only [Category.assoc]

/-- Helper for Lemma 8.8.1: the canonical Hom-presheaf map for a composite is the composite of
the two canonical Hom-presheaf maps. -/
theorem fibredMorphismPresheafMap_comp
    {X₁ X₂ X₃ : FibredCategoryOver C}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U : C} (x y : X₁.p.Fiber U) :
    fibredMorphismPresheafMap (F ≫ G) x y =
      fibredMorphismPresheafMap F x y ≫
        fibredMorphismPresheafMap G
          ((FibredCategoryMor.fiberFunctor F U).obj x)
          ((FibredCategoryMor.fiberFunctor F U).obj y) := by
  -- Prove equality of natural transformations at each object and section of the source Hom
  -- presheaf; the app-level lemma keeps the kernel from unfolding the whole comparison shell.
  ext W δ
  exact fibredMorphismPresheafMap_comp_app F G x y W δ

end

end CategoryTheory
