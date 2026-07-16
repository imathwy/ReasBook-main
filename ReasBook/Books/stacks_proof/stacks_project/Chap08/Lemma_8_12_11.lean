import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_18_3
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1
import stacks_proof.stacks_project.Chap08.Lemma_8_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open scoped CategoryTheory.FibredCategoryOver
universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasFiniteNonemptyLimits C]

/-
Domain-style sampling for Lemma 8.12.11:
- primary domain: stackifications of fibred categories and their functoriality under the
  localized pushforward construction along `u : C ⥤ D`.
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `FibredCategoryOver.pushforward`,
  `pushforwardFibredCategoryMap`,
  `stackification_precompose_functor`,
  `Functor.IsEquivalence`.
- best owner abstraction: the public statement should stay on the owner predicate
  `FibredCategoryMor.IsStackification` for the canonical composite
  `pushforwardFibredCategoryMap u G ≫ iYinv`, rather than introducing a local comparison wrapper.
- primitive data: a stackification `G : X ⟶ Y`, a chosen inverse-image stackification
  `iYinv : u ₚ Y ⟶ Yinv`, and the induced canonical pushforward morphism
  `pushforwardFibredCategoryMap u G : u ₚ X ⟶ u ₚ Y`.
- derived API: the composed stackification statement below and, when needed downstream, the
  canonical equivalence object `(stackification_precompose_functor _ iYinv).asEquivalence`.

Source/core/bridge triage:
- `source-facing`: the theorem `inverseImageStackAlong_isStackification_of_stackification`.
- `core/canonical`: `FibredCategoryMor.IsStackification`, `FibredCategoryOver.pushforward`,
  `pushforwardFibredCategoryMap`.
- `bridge/view`: the canonical owner statement
  `Functor.IsEquivalence (stackification_precompose_functor _ iYinv)`, whose `.asEquivalence`
  supplies the universal-property perspective on these stackification morphisms. -/

/-- Helper for Lemma 8.12.11: the chosen inverse-image stackification gives the expected
precomposition equivalence into every stack target over `(D, K)`. -/
private theorem inverseImageChosenStackification_precompose_isEquivalence
    (u : C ⥤ D) [Functor.IsContinuous u J K] [PreservesFiniteNonemptyLimits u]
    {Y : StackOver J} {Yinv T : StackOver K}
    (iYinv : u ₚ Y ⟶ Yinv)
    (hiYinv : FibredCategoryMor.IsStackification iYinv) :
    Functor.IsEquivalence
      (stackification_precompose_functor T iYinv :
        (Yinv ⟶ T) ⥤ ((u ₚ Y : FibredCategoryOver D) ⟶ T)) := by
  -- This is exactly the public universal property attached to the stackification morphism
  -- `iYinv`; naming it isolates the target-side half of the final composite argument.
  exact stackification_precompose_functor_isEquivalence T iYinv hiYinv

/-- Helper for Lemma 8.12.11: the chosen inverse-image stackification supplies the target-side
Hom-presheaf `W` condition. -/
private theorem inverseImageChosenStackification_morphismPresheafMap_W
    (u : C ⥤ D) [Functor.IsContinuous u J K] [PreservesFiniteNonemptyLimits u]
    {Y : StackOver J} {Yinv : StackOver K}
    (iYinv : u ₚ Y ⟶ Yinv)
    (hiYinv : FibredCategoryMor.IsStackification iYinv)
    (U : D) (x y : (u ₚ Y).p.Fiber U) :
    (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap iYinv x y) := by
  -- This is the first field of the stackification proof for the chosen inverse-image model.
  exact hiYinv.morphismPresheafMap_W U x y

/-- Helper for Lemma 8.12.11: the target-side Hom-presheaf `W` condition remains available
after precomposing the chosen inverse-image stackification with any fibred-category map into
`uₚ Y`. -/
private theorem inverseImageChosenStackification_morphismPresheafMap_W_after
    (u : C ⥤ D) [Functor.IsContinuous u J K] [PreservesFiniteNonemptyLimits u]
    {Z : FibredCategoryOver D} {Y : StackOver J} {Yinv : StackOver K}
    (F : Z ⟶ u ₚ Y)
    (iYinv : u ₚ Y ⟶ Yinv)
    (hiYinv : FibredCategoryMor.IsStackification iYinv)
    (U : D) (x y : Z.p.Fiber U) :
    (K.over U).W
      (FibredCategoryMor.fibredMorphismPresheafMap iYinv
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)) := by
  -- Feed the two objects obtained from `F` into the first field of the chosen target
  -- stackification; the remaining source-side factor is handled separately.
  exact hiYinv.morphismPresheafMap_W U _ _

/-- Helper for Lemma 8.12.11: the chosen inverse-image stackification supplies the target-side
local essential-image condition. -/
private theorem inverseImageChosenStackification_locallyEssentiallySurjectiveOnObjects
    (u : C ⥤ D) [Functor.IsContinuous u J K] [PreservesFiniteNonemptyLimits u]
    {Y : StackOver J} {Yinv : StackOver K}
    (iYinv : u ₚ Y ⟶ Yinv)
    (hiYinv : FibredCategoryMor.IsStackification iYinv) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K iYinv := by
  -- This is the second field of the stackification proof for the chosen inverse-image model.
  exact hiYinv.locallyEssentiallySurjectiveOnObjects

/-- Helper for Lemma 8.12.11: the Hom-presheaf map attached to a composite of fibred-category
morphisms has the expected pullback-comparison boundary on its source object. -/
private theorem stackificationPushforward_pullbackComparison_comp_hom
    {X₁ X₂ X₃ : FibredCategoryOver D}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U V : D} (f : V ⟶ U) (x : X₁.p.Fiber U) :
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

/-- Helper for Lemma 8.12.11: the inverse of the pullback-comparison isomorphism for a composite
fibred-category morphism is the reverse composite of the inverse comparisons. -/
private theorem stackificationPushforward_pullbackComparison_comp_inv
    {X₁ X₂ X₃ : FibredCategoryOver D}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U V : D} (f : V ⟶ U) (x : X₁.p.Fiber U) :
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
    simpa only [eF, eG, eGF] using
      stackificationPushforward_pullbackComparison_comp_hom F G f x
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

/-- Helper for Lemma 8.12.11: the Hom-presheaf map attached to a composite of fibred-category
morphisms agrees pointwise with the composite of the two Hom-presheaf maps. -/
private theorem stackificationPushforward_fibredMorphismPresheafMap_comp_app
    {X₁ X₂ X₃ : FibredCategoryOver D}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U : D} (x y : X₁.p.Fiber U)
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
  rw [stackificationPushforward_pullbackComparison_comp_hom F G W.unop.hom x]
  rw [stackificationPushforward_pullbackComparison_comp_inv F G W.unop.hom y]
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

/-- Helper for Lemma 8.12.11: the Hom-presheaf map attached to a composite of fibred-category
morphisms is the composite of the two Hom-presheaf maps. -/
private theorem stackificationPushforward_fibredMorphismPresheafMap_comp
    {X₁ X₂ X₃ : FibredCategoryOver D}
    (F : X₁ ⟶ X₂)
    (G : X₂ ⟶ X₃)
    {U : D} (x y : X₁.p.Fiber U) :
    FibredCategoryMor.fibredMorphismPresheafMap (F ≫ G) x y =
      FibredCategoryMor.fibredMorphismPresheafMap F x y ≫
        FibredCategoryMor.fibredMorphismPresheafMap G
          ((FibredCategoryMor.fiberFunctor F U).obj x)
          ((FibredCategoryMor.fiberFunctor F U).obj y) := by
  -- Prove equality of natural transformations at each object and section of the source Hom
  -- presheaf; the app-level lemma keeps the kernel from unfolding the whole comparison shell.
  ext W δ
  exact stackificationPushforward_fibredMorphismPresheafMap_comp_app F G x y W δ

/-- Helper for Lemma 8.12.11: the Hom-presheaf `W` condition is stable under composition of
fibred-category morphisms. -/
private theorem morphismPresheafMap_W_comp
    {X Y Z : FibredCategoryOver D}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (hF : ∀ (U : D) (x y : X.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y))
    (hG : ∀ (U : D) (x y : Y.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap G x y)) :
    ∀ (U : D) (x y : X.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap (F ≫ G) x y) := by
  intro U x y
  -- Rewrite the composite map to the categorical composite of Hom-presheaf maps, then use
  -- closure of the localization class under composition.
  rw [stackificationPushforward_fibredMorphismPresheafMap_comp F G x y]
  exact (K.over U).W.comp_mem _ _ (hF U x y)
    (hG U ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y))

/-- Helper for Lemma 8.12.11: two local essential-image isomorphisms compose after replacing
the iterated chosen pullback by the chosen pullback along the composite base arrow. -/
private noncomputable def compLocalEssentialImageIso
    {X Y Z : FibredCategoryOver D}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    {U V W : D} (f : V ⟶ U) (g : W ⟶ V)
    (z : Z.p.Fiber U) (y : Y.p.Fiber V) (x : X.p.Fiber W)
    (ηF : (FibredCategoryMor.fiberFunctor F W).obj x ≅
      g ^*[canonicalPullbackChoice Y.p] y)
    (ηG : (FibredCategoryMor.fiberFunctor G V).obj y ≅
      f ^*[canonicalPullbackChoice Z.p] z) :
    (FibredCategoryMor.fiberFunctor (F ≫ G) W).obj x ≅
      (g ≫ f) ^*[canonicalPullbackChoice Z.p] z :=
  Iso.trans
    (Iso.trans
      (Functor.mapIso (FibredCategoryMor.fiberFunctor G W) ηF)
      (FibredCategoryMor.pullbackComparison G g y).symm)
    (Iso.trans
      (((canonicalPullbackChoice Z.p).pullbackFunctor g).mapIso ηG)
      ((canonicalPullbackChoice Z.p).pullbackCompComponentIso f g z).symm)

/-- Helper for Lemma 8.12.11: local essential surjectivity on objects is stable under
composition of fibred-category morphisms. -/
private theorem locallyEssentiallySurjectiveOnObjects_comp
    {X Y Z : FibredCategoryOver D}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (hF : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K F)
    (hG : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K G) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K (F ≫ G) := by
  classical
  intro U z
  -- First lift the target object locally through `G`, then lift each chosen local model
  -- through `F` on a bound refinement of the cover.
  obtain ⟨S, hS⟩ := hG U z
  choose y hy using hS
  let T : ∀ I : S.Arrow, K.Cover I.Y := fun I => Classical.choose (hF I.Y (y I))
  have hT : ∀ I : S.Arrow, ∀ R : (T I).Arrow,
      ∃ x : X.p.Fiber R.Y,
        Nonempty (((FibredCategoryMor.fiberFunctor F R.Y).obj x) ≅
          R.f ^*[canonicalPullbackChoice Y.p] (y I)) := by
    intro I
    exact Classical.choose_spec (hF I.Y (y I))
  refine ⟨S.bind T, ?_⟩
  intro A
  -- An arrow of the bound cover is a second-stage arrow followed by a first-stage arrow; the
  -- composed local image isomorphism is then transported along `A.middle_spec`.
  let I : S.Arrow := A.fromMiddle
  let R : (T I).Arrow := A.toMiddle
  obtain ⟨x, hx⟩ := hT I R
  obtain ⟨ηF⟩ := hx
  obtain ⟨ηG⟩ := hy I
  refine ⟨x, ?_⟩
  rw [← A.middle_spec]
  refine ⟨?_⟩
  simpa [I, R, BasedFunctor.comp] using
    compLocalEssentialImageIso F G I.f R.f z (y I) x ηF ηG

/-- Helper for Lemma 8.12.11: fieldwise stackification data for the first morphism composes
with a stackification morphism on the target. -/
private theorem isStackification_comp_of_stackificationData
    {X Y : FibredCategoryOver D} {Z : StackOver K}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (hFW : ∀ (U : D) (x y : X.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y))
    (hFess : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K F)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (F ≫ G) := by
  constructor
  · -- Compose the two Hom-presheaf `W` conditions.
    exact morphismPresheafMap_W_comp F G hFW hG.morphismPresheafMap_W
  · -- Compose the two local essential-image conditions using cover binding.
    exact locallyEssentiallySurjectiveOnObjects_comp F G hFess
      hG.locallyEssentiallySurjectiveOnObjects

-- Proof sketch: apply the localized pushforward construction to the stackification morphism
-- `G : X ⟶ Y`, obtaining the canonical morphism `uₚ X ⟶ uₚ Y`. Composing with the chosen
-- stackification morphism `i : uₚ Y ⟶ Yinv` gives the desired canonical
-- comparison map. The stackification properties are checked on morphism presheaves and local
-- essential surjectivity exactly as in the Stacks Project argument.
/-- Lemma 8.12.11: if `G : X ⟶ Y` exhibits the stack `Y` as a stackification of the fibred
category `X` over `(C, J)`, then for any stackification `i : uₚ Y ⟶ Yinv` representing an
inverse-image stack of `Y` along `u`, the canonical comparison morphism `uₚ X ⟶ Yinv` is a
stackification of `uₚ X`. -/
@[stacks 04WR]
theorem inverseImageStackAlong_isStackification_of_stackification
    (u : C ⥤ D) [Functor.IsContinuous u J K] [PreservesFiniteNonemptyLimits u]
    {X : FibredCategoryOver C} {Y : StackOver J}
    (G : X ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G)
    {Yinv : StackOver K}
    (iYinv : u ₚ Y ⟶ Yinv)
    (hiYinv : FibredCategoryMor.IsStackification iYinv) :
    FibredCategoryMor.IsStackification (pushforwardFibredCategoryMap u G ≫ iYinv) := by
  -- The composite is checked fieldwise: the pushforward map supplies the source-side local
  -- equivalence data, and `iYinv` supplies the target-side stackification data.
  refine isStackification_comp_of_stackificationData
    (pushforwardFibredCategoryMap u G) iYinv ?_ ?_ hiYinv
  · exact pushforwardFibredCategoryMap_morphismPresheafMap_W_of_stackification u G hG
  · exact pushforwardFibredCategoryMap_locallyEssentiallySurjectiveOnObjects_of_stackification u G hG

end

end CategoryTheory
