import Mathlib
import StacksProject_2024.Chap08.Lemma_8_8_1.Criteria
import StacksProject_2024.Chap08.Lemma_8_8_1.CoverDescent
import StacksProject_2024.Chap08.Lemma_8_8_1.FiberTransport
import StacksProject_2024.Chap08.Lemma_8_8_1.HomPresheafComparison
import StacksProject_2024.Chap08.Lemma_8_8_1.Precomposition

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/- Domain-style sampling for Lemma 8.8.3:
- primary domain: the universal property of stackification in the `2`-category of fibred
  categories over a site, specialized to morphisms into a stack target.
- inspected owner-level declarations:
  `FibredCategoryMor`,
  `FibredCategoryMor.IsStackification`,
  `StackOver.InducedCategory.Hom.toFibredCategoryMor`,
  `SubTwoCategory.Hom.toHom`,
  `FibredCategoryMor.ofBasedFunctor`,
  `FibredCategoryMor.objectProperty`,
  `FibredCategoryMor.ofObjectProperty`,
  `Functor.IsEquivalence`.
- best owner abstraction: the induced precomposition functor
  `stackification_precompose_functor X G : (S' ⟶ X) ⥤ (S ⟶ X)`, together with the owner predicate
  `Functor.IsEquivalence`.
- primitive data: a stackification morphism `G : S ⟶ S'` and a target stack `X`.
- derived API: the induced functor on morphism categories and the canonical equivalence object
  `(stackification_precompose_functor X G).asEquivalence`.

Source/core/bridge triage:
- `source-facing`: the precomposition equivalence expressing the universal property of a
  stackification.
- `core/canonical`: `FibredCategoryMor.IsStackification`,
  `SubTwoCategory.Hom.toHom`, `FibredCategoryMor.ofBasedFunctor`,
  `Functor.IsEquivalence`.
- `bridge/view`: the temporary passage through based functors preserving strongly cartesian
  morphisms. -/

private abbrev forgetToFibredCategoryMor (S' X : StackOver J) :
    (S' ⟶ X) ⥤ FibredCategoryMor S'.toFibredCategoryOver X.toFibredCategoryOver :=
  ((stackOverSubTwoCategory J).hom S' X).inclusion

-- Proof sketch: left whiskering by the based functor underlying `G` leaves identity vertical
-- natural transformations unchanged.
private theorem stackification_precompose_based_map_id
    (G : FibredCategoryMor S S') :
    ∀ F : S'.toBasedCategory ⥤ᵇ X.toBasedCategory,
      BasedCategory.whiskerLeft G.toHom (𝟙 F) =
        𝟙 (BasedFunctor.comp G.toHom F) := by
  -- Normalize to the owner-level precomposition lemma from the Lemma 8.8.1 API.
  intro F
  exact local_stackification_precompose_based_map_id G F

-- Proof sketch: left whiskering by a fixed based functor commutes with vertical composition of
-- based natural transformations.
private theorem stackification_precompose_based_map_comp
    (G : FibredCategoryMor S S') :
    ∀ {F₁ F₂ F₃ : S'.toBasedCategory ⥤ᵇ X.toBasedCategory}
      (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃),
      BasedCategory.whiskerLeft G.toHom (τ ≫ σ) =
        BasedCategory.whiskerLeft G.toHom τ ≫
          BasedCategory.whiskerLeft G.toHom σ := by
  -- Normalize to the owner-level composition law for left whiskering.
  intro F₁ F₂ F₃ τ σ
  exact local_stackification_precompose_based_map_comp G τ σ

private abbrev stackification_precompose_based_functor
    (G : FibredCategoryMor S S') :
    (S'.toBasedCategory ⥤ᵇ X.toBasedCategory) ⥤
      (S.toBasedCategory ⥤ᵇ X.toBasedCategory) where
  obj F := BasedFunctor.comp G.toHom F
  map τ := BasedCategory.whiskerLeft G.toHom τ
  map_id := stackification_precompose_based_map_id G
  map_comp := fun τ σ ↦ stackification_precompose_based_map_comp G τ σ

private abbrev stackification_precompose_stackMor_to_based
    (X : StackOver J)
    (G : FibredCategoryMor S S') :
    (S' ⟶ X) ⥤ (S.toBasedCategory ⥤ᵇ X.toBasedCategory) :=
  forgetToFibredCategoryMor S' X ⋙
    (((fibredCategoryOverSubTwoCategory C).hom S'.toFibredCategoryOver X.toFibredCategoryOver).inclusion) ⋙
    stackification_precompose_based_functor G

-- Proof sketch: both `G` and `H` preserve strongly cartesian morphisms, so their composite over
-- `C` does as well. This is exactly the owner object property
-- `FibredCategoryMor.objectProperty S X`.
private theorem stackification_precompose_preservesStronglyCartesian
    (G : FibredCategoryMor S S')
    (H : S' ⟶ X) :
    BasedFunctor.PreservesStronglyCartesian
      ((stackification_precompose_stackMor_to_based X G).obj H) := by
  -- The local precomposition API proves the same strongly-cartesian preservation statement.
  exact local_stackification_precompose_preservesStronglyCartesian G H

/-- Precomposition with `G : S ⟶ S'` sends a stack morphism `S' ⟶ X` to the induced owner
morphism `S ⟶ X`. -/
abbrev stackification_precompose_functor
    (X : StackOver J)
    (G : S ⟶ S') :
    (S' ⟶ X) ⥤ (S ⟶ X) :=
  (FibredCategoryMor.objectProperty S X).lift
      (stackification_precompose_stackMor_to_based X G)
      (fun H ↦ stackification_precompose_preservesStronglyCartesian G H) ⋙
    FibredCategoryMor.ofObjectProperty S X

/-- Helper for Chap08 Lemma 8 8 3: the item-local precomposition functor is definitionally the
owner precomposition functor from the Lemma 8.8.1 API. -/
private theorem stackification_precompose_functor_eq_local
    (X : StackOver J)
    (G : S ⟶ S') :
    stackification_precompose_functor X G =
      local_stackification_precompose_functor (J := J) (G := G) := by
  -- Both constructions lift the same based-functor precomposition and then forget back to
  -- fibred-category morphisms.
  rfl

/-- Helper for Chap08 Lemma 8 8 3: a morphism in `W` induces an isomorphism after applying the
sheafification-map construction. -/
private theorem isIso_sheafifyMap_of_W
    {D : Type wD} [Category.{vD} D] [HasWeakSheafify J D]
    {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (hf : J.W f) :
    IsIso (sheafifyMap J f) := by
  -- `W_iff` gives an isomorphism in the category of sheaves; applying the forgetful functor
  -- reads it as the presheaf-level morphism `sheafifyMap`.
  have hIsoSheaf : IsIso ((presheafToSheaf J D).map f) := (J.W_iff f).1 hf
  letI : IsIso ((presheafToSheaf J D).map f) := hIsoSheaf
  change IsIso ((sheafToPresheaf J D).map ((presheafToSheaf J D).map f))
  infer_instance

/-- Helper for Chap08 Lemma 8 8 3: precomposition by a `W`-morphism is bijective on maps into
any sheaf-valued presheaf. -/
private theorem W_precomp_bijective_to_sheaf
    {D : Type wD} [Category.{vD} D]
    {P Q R : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (hf : J.W f)
    (hR : Presheaf.IsSheaf J R) :
    Function.Bijective (fun g : Q ⟶ R ↦ (f ≫ g : P ⟶ R)) := by
  -- `J.W` is the left-local class for the sheaf object property, so its defining bijection is
  -- exactly precomposition into any sheaf-valued presheaf.
  exact hf R hR

/-- Helper for Chap08 Lemma 8 8 3: maps from the target of a `W`-morphism into a sheaf are
determined after precomposition by that `W`-morphism. -/
private theorem W_precomp_ext_to_sheaf
    {D : Type wD} [Category.{vD} D]
    {P Q R : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (hf : J.W f)
    (hR : Presheaf.IsSheaf J R)
    {g₁ g₂ : Q ⟶ R}
    (h : f ≫ g₁ = f ≫ g₂) :
    g₁ = g₂ := by
  -- Use only the injective half of the sheaf-valued `W` localization bridge.
  exact (W_precomp_bijective_to_sheaf (J := J) f hf hR).1 h

/-- Helper for Chap08 Lemma 8 8 3: an arbitrary `2`-morphism between fibred-category morphisms
restricts to a morphism between the induced fiber functors over a fixed base object. -/
private noncomputable def basedFiberFunctorHom
    {Y : FibredCategoryOver C} {F G : S ⟶ Y}
    (η : F ⟶ G) (U : C) (x : S.p.Fiber U) :
    ((FibredCategoryMor.fiberFunctor F U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj x) :=
  ⟨(η.hom.hom).toNatTrans.app x.1, (η.hom.hom).isHomLift x.2⟩

/-- Helper for Chap08 Lemma 8 8 3: the fiber component of a `2`-morphism is natural on vertical
morphisms inside a fixed fiber. -/
private theorem basedFiberFunctorHom_naturality
    {Y : FibredCategoryOver C} {F G : S ⟶ Y}
    (η : F ⟶ G) {U : C} {x y : S.p.Fiber U} (φ : x ⟶ y) :
    (FibredCategoryMor.fiberFunctor F U).map φ ≫
        basedFiberFunctorHom η U y =
      basedFiberFunctorHom η U x ≫
        (FibredCategoryMor.fiberFunctor G U).map φ := by
  -- Forget to the underlying based natural transformation; its ordinary naturality is exactly the
  -- desired fiberwise square.
  apply Functor.Fiber.hom_ext
  exact (η.hom.hom).toNatTrans.naturality φ.1

/-- Helper for Chap08 Lemma 8 8 3: the fiber component of a `2`-morphism transports along any
fiber isomorphism by conjugation. -/
private theorem basedFiberFunctorHom_transport_of_fiberIso
    {Y : FibredCategoryOver C} {F G : S ⟶ Y}
    (η : F ⟶ G) {U : C} {x y : S.p.Fiber U} (e : x ≅ y) :
    basedFiberFunctorHom η U y =
      (FibredCategoryMor.fiberFunctor F U).map e.inv ≫
        basedFiberFunctorHom η U x ≫
        (FibredCategoryMor.fiberFunctor G U).map e.hom := by
  -- Move the component at `y` across the isomorphism using naturality, then cancel the inverse
  -- image of the same isomorphism on the left.
  have hnat :
      (FibredCategoryMor.fiberFunctor F U).map e.hom ≫
          basedFiberFunctorHom η U y =
        basedFiberFunctorHom η U x ≫
          (FibredCategoryMor.fiberFunctor G U).map e.hom :=
    basedFiberFunctorHom_naturality η e.hom
  have hcancel :
      (FibredCategoryMor.fiberFunctor F U).map e.inv ≫
        (FibredCategoryMor.fiberFunctor F U).map e.hom =
          𝟙 ((FibredCategoryMor.fiberFunctor F U).obj y) := by
    rw [← Functor.map_comp, e.inv_hom_id, Functor.map_id]
  calc
    basedFiberFunctorHom η U y
        = 𝟙 _ ≫ basedFiberFunctorHom η U y := by
          rw [Category.id_comp]
    _ = ((FibredCategoryMor.fiberFunctor F U).map e.inv ≫
            (FibredCategoryMor.fiberFunctor F U).map e.hom) ≫
          basedFiberFunctorHom η U y := by
          rw [hcancel]
    _ = (FibredCategoryMor.fiberFunctor F U).map e.inv ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.hom ≫
            basedFiberFunctorHom η U y) := by
          rw [Category.assoc]
    _ = (FibredCategoryMor.fiberFunctor F U).map e.inv ≫
          (basedFiberFunctorHom η U x ≫
            (FibredCategoryMor.fiberFunctor G U).map e.hom) := by
          rw [hnat]
    _ = (FibredCategoryMor.fiberFunctor F U).map e.inv ≫
        basedFiberFunctorHom η U x ≫
        (FibredCategoryMor.fiberFunctor G U).map e.hom := rfl

/-- Helper for Chap08 Lemma 8 8 3: pulling back the fiber component of an arbitrary `2`-morphism
is the same as evaluating the component after pullback and conjugating by the two
`pullbackComparison` isomorphisms. -/
private theorem basedFiberFunctorHom_pullback_bridge
    {Y : FibredCategoryOver C} {F G : S ⟶ Y}
    (η : F ⟶ G) {U V : C} (f : V ⟶ U) (x : S.p.Fiber U) :
    ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        (basedFiberFunctorHom η U x) =
      (FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv := by
  -- Compare both candidate vertical arrows after postcomposition with the chosen pullback arrow
  -- for the `G`-side target. The defining naturality square of `η` then supplies the middle step.
  apply Functor.Fiber.hom_ext
  let M := ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor
  have hPullbackMap :
      (M.map (basedFiberFunctorHom η U x)).1 ≫
          (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x) =
        (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) ≫
          (basedFiberFunctorHom η U x).1 := by
    exact FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := Y.p) (f := f)
      (φ := basedFiberFunctorHom η U x)
  have hNat :
      F.toHom.map ((canonicalPullbackChoice S.p).map f x) ≫
          (basedFiberFunctorHom η U x).1 =
        (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1 ≫
          G.toHom.map ((canonicalPullbackChoice S.p).map f x) := by
    change F.toHom.map ((canonicalPullbackChoice S.p).map f x) ≫
        (η.hom.hom).toNatTrans.app x.1 =
      (η.hom.hom).toNatTrans.app (f ^*[canonicalPullbackChoice S.p] x).1 ≫
        G.toHom.map ((canonicalPullbackChoice S.p).map f x)
    exact (η.hom.hom).toNatTrans.naturality ((canonicalPullbackChoice S.p).map f x)
  have hFpost :
      (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice S.p).map f x) =
        (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) :=
    FibredCategoryMor.pullbackComparison_hom_postcompose F f x
  have hGinvpost :
      (FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
          (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x) =
        G.toHom.map ((canonicalPullbackChoice S.p).map f x) :=
    FibredCategoryMor.pullbackComparison_inv_postcompose_owner G f x
  have hTargetCart :
      Y.p.IsStronglyCartesian f
        ((canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) := by
    exact (canonicalPullbackChoice Y.p).isStronglyCartesian f ((G.toHom.fiberFunctor U).obj x)
  have hLeftLift : Y.p.IsHomLift (𝟙 V) (M.map (basedFiberFunctorHom η U x)).1 :=
    (M.map (basedFiberFunctorHom η U x)).2
  have hRightLift : Y.p.IsHomLift (𝟙 V)
      (((FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv).1) :=
    ((FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv).2
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _ f
    ((canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) hTargetCart
    _ _ (𝟙 V) (M.map (basedFiberFunctorHom η U x)).1
    (((FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv).1)
    hLeftLift hRightLift ?_
  refine hPullbackMap.trans ?_
  have h1 :
      (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) ≫
          (basedFiberFunctorHom η U x).1 =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice S.p).map f x)) ≫
          (basedFiberFunctorHom η U x).1 :=
    congrArg (fun m => m ≫ (basedFiberFunctorHom η U x).1) hFpost.symm
  have h2 :
      ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice S.p).map f x)) ≫
          (basedFiberFunctorHom η U x).1 =
        (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (F.toHom.map ((canonicalPullbackChoice S.p).map f x) ≫
            (basedFiberFunctorHom η U x).1) :=
    Category.assoc _ _ _
  have h3 :
      (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (F.toHom.map ((canonicalPullbackChoice S.p).map f x) ≫
            (basedFiberFunctorHom η U x).1) =
        (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          ((basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1 ≫
            G.toHom.map ((canonicalPullbackChoice S.p).map f x)) :=
    congrArg (fun m => (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫ m) hNat
  have h4 :
      (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          ((basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1 ≫
            G.toHom.map ((canonicalPullbackChoice S.p).map f x)) =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1) ≫
          G.toHom.map ((canonicalPullbackChoice S.p).map f x) :=
    (Category.assoc _ _ _).symm
  have h5 :
      ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1) ≫
          G.toHom.map ((canonicalPullbackChoice S.p).map f x) =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1) ≫
          ((FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) :=
    congrArg
      (fun m => ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
        (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1) ≫ m)
      hGinvpost.symm
  have h6 :
      ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1) ≫
          ((FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) =
        (((FibredCategoryMor.pullbackComparison F f x).hom ≫
          basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x) ≫
          (FibredCategoryMor.pullbackComparison G f x).inv).1) ≫
          (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x) := by
    change (((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1) ≫
          ((FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x))) =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          ((basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice S.p] x)).1 ≫
            (FibredCategoryMor.pullbackComparison G f x).inv.1)) ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)
    simp only [Category.assoc]
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- Helper for Chap08 Lemma 8 8 3: postcomposition by a fixed fiber morphism is natural on
the canonical Hom presheaf. -/
private theorem presheafHomPostcompMap_naturality
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (β : N ⟶ P) :
    ∀ ⦃T₁ T₂ : (Over U)ᵒᵖ⦄ (α : T₁ ⟶ T₂),
      ((F.presheafHom M N).map α) ≫
          (fun φ => φ ≫ (F.map T₂.unop.hom.op.toLoc).toFunctor.map β) =
        (fun φ => φ ≫ (F.map T₁.unop.hom.op.toLoc).toFunctor.map β) ≫
          ((F.presheafHom M P).map α) := by
  -- Unfold the restriction maps once, then use the comparison isomorphism's naturality.
  intro T₁ T₂ α
  funext φ
  dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hfg : T₁.unop.hom.op.toLoc ≫ α.unop.left.op.toLoc =
      T₂.unop.hom.op.toLoc := by
    have h := congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op α.unop.w)
    simpa [Quiver.Hom.comp_toLoc] using h
  let e := F.mapComp' T₁.unop.hom.op.toLoc α.unop.left.op.toLoc
    T₂.unop.hom.op.toLoc hfg
  change ((e.hom.toNatTrans.app M ≫
        (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
          e.inv.toNatTrans.app N) ≫
        (F.map T₂.unop.hom.op.toLoc).toFunctor.map β) =
    e.hom.toNatTrans.app M ≫
      (F.map α.unop.left.op.toLoc).toFunctor.map
        (φ ≫ (F.map T₁.unop.hom.op.toLoc).toFunctor.map β) ≫
      e.inv.toNatTrans.app P
  have hnat :
      (F.map α.unop.left.op.toLoc).toFunctor.map
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map β) ≫
          e.inv.toNatTrans.app P =
        e.inv.toNatTrans.app N ≫
          (F.map T₂.unop.hom.op.toLoc).toFunctor.map β := by
    exact e.inv.toNatTrans.naturality β
  have hmap :
      (F.map α.unop.left.op.toLoc).toFunctor.map
          (φ ≫ (F.map T₁.unop.hom.op.toLoc).toFunctor.map β) =
        (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
          (F.map α.unop.left.op.toLoc).toFunctor.map
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map β) := by
    exact (F.map α.unop.left.op.toLoc).toFunctor.map_comp φ
      ((F.map T₁.unop.hom.op.toLoc).toFunctor.map β)
  rw [hmap]
  calc
    (e.hom.toNatTrans.app M ≫ (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
        e.inv.toNatTrans.app N) ≫
        (F.map T₂.unop.hom.op.toLoc).toFunctor.map β =
      e.hom.toNatTrans.app M ≫ (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
        (F.map α.unop.left.op.toLoc).toFunctor.map
          ((F.map T₁.unop.hom.op.toLoc).toFunctor.map β) ≫
        e.inv.toNatTrans.app P := by
        simpa only [Category.assoc] using
          congrArg
            (fun t =>
              e.hom.toNatTrans.app M ≫
                (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫ t)
            hnat.symm
    _ = e.hom.toNatTrans.app M ≫
        ((F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
          (F.map α.unop.left.op.toLoc).toFunctor.map
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map β)) ≫
        e.inv.toNatTrans.app P := by
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom-presheaf map induced by postcomposition
with a fixed fiber morphism. -/
private noncomputable def presheafHomPostcompMap
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (β : N ⟶ P) :
    F.presheafHom M N ⟶ F.presheafHom M P where
  app T φ := φ ≫ (F.map T.unop.hom.op.toLoc).toFunctor.map β
  naturality := presheafHomPostcompMap_naturality β

/-- Helper for Chap08 Lemma 8 8 3: evaluating Hom-presheaf postcomposition at the identity
slice object gives ordinary postcomposition. -/
private theorem presheafHomPostcompMap_app_id
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (β : N ⟶ P) (φ : M ⟶ N) :
    (presheafHomPostcompMap β).app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (φ ≫ β) := by
  -- The identity restriction is encoded by `mapId`; its inverse naturality moves `β` through
  -- the comparison isomorphism.
  dsimp [presheafHomPostcompMap, Pseudofunctor.presheafHomObjHomEquiv, Iso.homCongr]
  let e := F.mapId (.mk (op U))
  change ((e.hom.toNatTrans.app M ≫ φ ≫ e.inv.toNatTrans.app N) ≫
      (F.map (𝟙 (.mk (op U)))).toFunctor.map β) =
    e.hom.toNatTrans.app M ≫ (φ ≫ β) ≫ e.inv.toNatTrans.app P
  have hnat :
      β ≫ e.inv.toNatTrans.app P =
        e.inv.toNatTrans.app N ≫
          (F.map (𝟙 (.mk (op U)))).toFunctor.map β := by
    simpa only using e.inv.toNatTrans.naturality β
  calc
    (e.hom.toNatTrans.app M ≫ φ ≫ e.inv.toNatTrans.app N) ≫
        (F.map (𝟙 (.mk (op U)))).toFunctor.map β =
      e.hom.toNatTrans.app M ≫ φ ≫ (β ≫ e.inv.toNatTrans.app P) := by
        simpa only [Category.assoc] using
          congrArg (fun t => e.hom.toNatTrans.app M ≫ φ ≫ t) hnat.symm
    _ = e.hom.toNatTrans.app M ≫ (φ ≫ β) ≫ e.inv.toNatTrans.app P := by
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: precomposition by a fixed fiber morphism is natural on the
canonical Hom presheaf. -/
private theorem presheafHomPrecompMap_naturality
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (α₀ : M ⟶ N) :
    ∀ ⦃T₁ T₂ : (Over U)ᵒᵖ⦄ (α : T₁ ⟶ T₂),
      ((F.presheafHom N P).map α) ≫
          (fun φ => (F.map T₂.unop.hom.op.toLoc).toFunctor.map α₀ ≫ φ) =
        (fun φ => (F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀ ≫ φ) ≫
          ((F.presheafHom M P).map α) := by
  -- The proof is the precomposition analogue of the postcomposition map naturality.
  intro T₁ T₂ α
  funext φ
  dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hfg : T₁.unop.hom.op.toLoc ≫ α.unop.left.op.toLoc =
      T₂.unop.hom.op.toLoc := by
    have h := congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op α.unop.w)
    simpa [Quiver.Hom.comp_toLoc] using h
  let e := F.mapComp' T₁.unop.hom.op.toLoc α.unop.left.op.toLoc
    T₂.unop.hom.op.toLoc hfg
  change (F.map T₂.unop.hom.op.toLoc).toFunctor.map α₀ ≫
      (e.hom.toNatTrans.app N ≫
        (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
        e.inv.toNatTrans.app P) =
    e.hom.toNatTrans.app M ≫
      (F.map α.unop.left.op.toLoc).toFunctor.map
        ((F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀ ≫ φ) ≫
      e.inv.toNatTrans.app P
  have hnat :
      (F.map T₂.unop.hom.op.toLoc).toFunctor.map α₀ ≫
          e.hom.toNatTrans.app N =
        e.hom.toNatTrans.app M ≫
          (F.map α.unop.left.op.toLoc).toFunctor.map
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀) := by
    exact e.hom.toNatTrans.naturality α₀
  have hmap :
      (F.map α.unop.left.op.toLoc).toFunctor.map
          ((F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀ ≫ φ) =
        (F.map α.unop.left.op.toLoc).toFunctor.map
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀) ≫
          (F.map α.unop.left.op.toLoc).toFunctor.map φ := by
    exact (F.map α.unop.left.op.toLoc).toFunctor.map_comp
      ((F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀) φ
  rw [hmap]
  calc
    (F.map T₂.unop.hom.op.toLoc).toFunctor.map α₀ ≫
        (e.hom.toNatTrans.app N ≫
          (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
          e.inv.toNatTrans.app P) =
      ((F.map T₂.unop.hom.op.toLoc).toFunctor.map α₀ ≫
          e.hom.toNatTrans.app N) ≫
        (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
        e.inv.toNatTrans.app P := by
        simp only [Category.assoc]
    _ = (e.hom.toNatTrans.app M ≫
          (F.map α.unop.left.op.toLoc).toFunctor.map
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀)) ≫
        (F.map α.unop.left.op.toLoc).toFunctor.map φ ≫
        e.inv.toNatTrans.app P := by
        rw [hnat]
        rfl
    _ = e.hom.toNatTrans.app M ≫
        ((F.map α.unop.left.op.toLoc).toFunctor.map
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀) ≫
          (F.map α.unop.left.op.toLoc).toFunctor.map φ) ≫
        e.inv.toNatTrans.app P := by
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom-presheaf map induced by precomposition
with a fixed fiber morphism. -/
private noncomputable def presheafHomPrecompMap
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (α : M ⟶ N) :
    F.presheafHom N P ⟶ F.presheafHom M P where
  app T φ := (F.map T.unop.hom.op.toLoc).toFunctor.map α ≫ φ
  naturality := presheafHomPrecompMap_naturality α

/-- Helper for Chap08 Lemma 8 8 3: evaluating Hom-presheaf precomposition at the identity
slice object gives ordinary precomposition. -/
private theorem presheafHomPrecompMap_app_id
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (α : M ⟶ N) (φ : N ⟶ P) :
    (presheafHomPrecompMap α).app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (α ≫ φ) := by
  -- Use naturality of the identity comparison's hom component to move the precomposed morphism
  -- into the ordinary fiber Hom.
  dsimp [presheafHomPrecompMap, Pseudofunctor.presheafHomObjHomEquiv, Iso.homCongr]
  let e := F.mapId (.mk (op U))
  change (F.map (𝟙 (.mk (op U)))).toFunctor.map α ≫
      (e.hom.toNatTrans.app N ≫ φ ≫ e.inv.toNatTrans.app P) =
    e.hom.toNatTrans.app M ≫ (α ≫ φ) ≫ e.inv.toNatTrans.app P
  have hnat :
      (F.map (𝟙 (.mk (op U)))).toFunctor.map α ≫
          e.hom.toNatTrans.app N =
        e.hom.toNatTrans.app M ≫ α := by
    simpa only using e.hom.toNatTrans.naturality α
  calc
    (F.map (𝟙 (.mk (op U)))).toFunctor.map α ≫
        (e.hom.toNatTrans.app N ≫ φ ≫ e.inv.toNatTrans.app P) =
      ((F.map (𝟙 (.mk (op U)))).toFunctor.map α ≫ e.hom.toNatTrans.app N) ≫
        φ ≫ e.inv.toNatTrans.app P := by
        simp only [Category.assoc]
    _ = (e.hom.toNatTrans.app M ≫ α) ≫ φ ≫ e.inv.toNatTrans.app P := by
        rw [hnat]
        rfl
    _ = e.hom.toNatTrans.app M ≫ (α ≫ φ) ≫ e.inv.toNatTrans.app P := by
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the fiberwise Hom-presheaf map induced by a fibred-category
morphism commutes with postcomposition by a source-fiber morphism. -/
private theorem fibredMorphismPresheafMap_postcomp
    {Y : FibredCategoryOver C}
    (F : S ⟶ Y)
    {U : C} {x y z : S.p.Fiber U} (ψ : y ⟶ z) :
    FibredCategoryMor.fibredMorphismPresheafMap F x y ≫
        presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor F U).map ψ) =
      presheafHomPostcompMap ψ ≫
        FibredCategoryMor.fibredMorphismPresheafMap F x z := by
  apply NatTrans.ext
  funext W δ
  let Mₛ := ((canonicalFiberPseudofunctor S.p).map W.unop.hom.op.toLoc).toFunctor
  let Mᵧ := ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor
  let ex := FibredCategoryMor.pullbackComparison F W.unop.hom x
  let ey := FibredCategoryMor.pullbackComparison F W.unop.hom y
  let ez := FibredCategoryMor.pullbackComparison F W.unop.hom z
  change (ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ey.inv) ≫
      Mᵧ.map ((FibredCategoryMor.fiberFunctor F U).map ψ) =
    ex.hom ≫
      (FibredCategoryMor.fiberFunctor F W.unop.left).map (δ ≫ Mₛ.map ψ) ≫ ez.inv
  have hψ :
      Mᵧ.map ((FibredCategoryMor.fiberFunctor F U).map ψ) =
        ey.hom ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ) ≫
          ez.inv := by
    have h := FibredCategoryMor.pullbackComparison_naturality_over_vertical F W.unop.hom ψ
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 h
  erw [hψ]
  have hmap :
      (FibredCategoryMor.fiberFunctor F W.unop.left).map (δ ≫ Mₛ.map ψ) =
        (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ) :=
    (FibredCategoryMor.fiberFunctor F W.unop.left).map_comp δ (Mₛ.map ψ)
  calc
    (ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ey.inv) ≫
        ey.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ) ≫
        ez.inv =
      ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫
        (ey.inv ≫ ey.hom) ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ) ≫ ez.inv := by
        simp only [Category.assoc]
    _ =
      ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫
        𝟙 _ ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ) ≫ ez.inv := by
        exact
          congrArg
            (fun m ↦ ex.hom ≫
              (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ m ≫
              (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ) ≫ ez.inv)
            ey.inv_hom_id
    _ =
      ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ) ≫ ez.inv := by
        simp only [Category.id_comp]
    _ = (ex.hom ≫
        ((FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map ψ))) ≫ ez.inv := by
        simp only [Category.assoc]
    _ = (ex.hom ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (δ ≫ Mₛ.map ψ)) ≫ ez.inv := by
        exact
          congrArg
            (fun m ↦ (ex.hom ≫ m) ≫ ez.inv)
            hmap.symm
    _ = ex.hom ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (δ ≫ Mₛ.map ψ) ≫ ez.inv := by
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the fiberwise Hom-presheaf map induced by a fibred-category
morphism commutes with precomposition by a source-fiber morphism. -/
private theorem fibredMorphismPresheafMap_precomp
    {Y : FibredCategoryOver C}
    (F : S ⟶ Y)
    {U : C} {x y z : S.p.Fiber U} (φ : x ⟶ y) :
    FibredCategoryMor.fibredMorphismPresheafMap F y z ≫
        presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor F U).map φ) =
      presheafHomPrecompMap φ ≫
        FibredCategoryMor.fibredMorphismPresheafMap F x z := by
  apply NatTrans.ext
  funext W δ
  let Mₛ := ((canonicalFiberPseudofunctor S.p).map W.unop.hom.op.toLoc).toFunctor
  let Mᵧ := ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor
  let ex := FibredCategoryMor.pullbackComparison F W.unop.hom x
  let ey := FibredCategoryMor.pullbackComparison F W.unop.hom y
  let ez := FibredCategoryMor.pullbackComparison F W.unop.hom z
  change Mᵧ.map ((FibredCategoryMor.fiberFunctor F U).map φ) ≫
      (ey.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ez.inv) =
    ex.hom ≫
      (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ ≫ δ) ≫ ez.inv
  have hφ :
      Mᵧ.map ((FibredCategoryMor.fiberFunctor F U).map φ) =
        ex.hom ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫
          ey.inv := by
    have h := FibredCategoryMor.pullbackComparison_naturality_over_vertical F W.unop.hom φ
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 h
  erw [hφ]
  have hmap :
      (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ ≫ δ) =
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map δ :=
    (FibredCategoryMor.fiberFunctor F W.unop.left).map_comp (Mₛ.map φ) δ
  calc
    (ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫ ey.inv) ≫
        ey.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ez.inv =
      ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫
        (ey.inv ≫ ey.hom) ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ez.inv := by
        simp only [Category.assoc]
    _ =
      ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫
        𝟙 _ ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ez.inv := by
        exact
          congrArg
            (fun m ↦ ex.hom ≫
              (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫ m ≫
              (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ez.inv)
            ey.inv_hom_id
    _ =
      ex.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ez.inv := by
        simp only [Category.id_comp]
    _ = (ex.hom ≫
        ((FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ) ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map δ)) ≫ ez.inv := by
        simp only [Category.assoc]
    _ = (ex.hom ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ ≫ δ)) ≫ ez.inv := by
        exact
          congrArg
            (fun m ↦ (ex.hom ≫ m) ≫ ez.inv)
            hmap.symm
    _ = ex.hom ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map (Mₛ.map φ ≫ δ) ≫ ez.inv := by
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: an inverse-then-hom pair in the middle of a composite
cancels after reassociation. -/
private theorem comp_inv_hom_assoc
    {D : Type*} [Category D] {A B C' E : D}
    (a : A ⟶ B) (e : C' ≅ B) (b : B ⟶ E) :
    (a ≫ e.inv) ≫ e.hom ≫ b = a ≫ b := by
  -- Package the associativity/cancellation pattern used in the two-morphism square below.
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun t => a ≫ t ≫ b) e.inv_hom_id

/-- Helper for Chap08 Lemma 8 8 3: the Hom-presheaf comparison map is natural with respect to a
`2`-morphism, expressed as postcomposition on one side and precomposition on the other. -/
private theorem fibredMorphismPresheafMap_twoHom_naturality
    {Y : FibredCategoryOver C} {F K : S ⟶ Y}
    (η : F ⟶ K) {U : C} (x x' : S.p.Fiber U) :
    FibredCategoryMor.fibredMorphismPresheafMap F x x' ≫
        presheafHomPostcompMap (basedFiberFunctorHom η U x') =
      FibredCategoryMor.fibredMorphismPresheafMap K x x' ≫
        presheafHomPrecompMap (basedFiberFunctorHom η U x) := by
  -- Check the equality on each slice object. After expanding the comparison shells, the two
  -- pullback-comparison pairs cancel and the middle square is fiberwise naturality of `η`.
  apply NatTrans.ext
  funext W φ
  let U₀ : C := (Functor.fromPUnit U).obj W.unop.right
  change (FibredCategoryMor.fibredMorphismPresheafMap F x x').app W φ ≫
      ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor.map
        (basedFiberFunctorHom η U₀ x') =
    ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor.map
        (basedFiberFunctorHom η U₀ x) ≫
      (FibredCategoryMor.fibredMorphismPresheafMap K x x').app W φ
  change (((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
        (FibredCategoryMor.fiberFunctor F W.unop.left).map φ ≫
        (FibredCategoryMor.pullbackComparison F W.unop.hom x').inv) ≫
      ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor.map
        (basedFiberFunctorHom η U₀ x')) =
    (((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor.map
        (basedFiberFunctorHom η U₀ x) ≫
      ((FibredCategoryMor.pullbackComparison K W.unop.hom x).hom ≫
        (FibredCategoryMor.fiberFunctor K W.unop.left).map φ ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv))
  have hpullx' :
      ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor.map
          (basedFiberFunctorHom η U₀ x') =
        (FibredCategoryMor.pullbackComparison F W.unop.hom x').hom ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice S.p] x') ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
    exact basedFiberFunctorHom_pullback_bridge η W.unop.hom x'
  have hpullx :
      ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor.map
          (basedFiberFunctorHom η U₀ x) =
        (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice S.p] x) ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x).inv := by
    exact basedFiberFunctorHom_pullback_bridge η W.unop.hom x
  have hnat :
      (FibredCategoryMor.fiberFunctor F W.unop.left).map φ ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice S.p] x') =
        basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice S.p] x) ≫
          (FibredCategoryMor.fiberFunctor K W.unop.left).map φ := by
    exact basedFiberFunctorHom_naturality η φ
  conv_lhs => rhs; rw [hpullx']
  conv_rhs => lhs; rw [hpullx]
  have hleft := comp_inv_hom_assoc
    ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
      (FibredCategoryMor.fiberFunctor F W.unop.left).map φ)
    (FibredCategoryMor.pullbackComparison F W.unop.hom x')
    (basedFiberFunctorHom η W.unop.left
      (W.unop.hom ^*[canonicalPullbackChoice S.p] x') ≫
      (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv)
  have hright := comp_inv_hom_assoc
    ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
      basedFiberFunctorHom η W.unop.left
        (W.unop.hom ^*[canonicalPullbackChoice S.p] x))
    (FibredCategoryMor.pullbackComparison K W.unop.hom x)
    ((FibredCategoryMor.fiberFunctor K W.unop.left).map φ ≫
      (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv)
  calc
    _ = ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map φ) ≫
        basedFiberFunctorHom η W.unop.left
          (W.unop.hom ^*[canonicalPullbackChoice S.p] x') ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
        simpa only [Category.assoc] using hleft
    _ = (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
        (((FibredCategoryMor.fiberFunctor F W.unop.left).map φ ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice S.p] x')) ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv) := by
        simp only [Category.assoc]
    _ = (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
        ((basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice S.p] x) ≫
          (FibredCategoryMor.fiberFunctor K W.unop.left).map φ) ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv) := by
        exact congrArg
          (fun t =>
            (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫ t ≫
              (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv)
          hnat
    _ = ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice S.p] x)) ≫
        (FibredCategoryMor.fiberFunctor K W.unop.left).map φ ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
        simp only [Category.assoc]
    _ = (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
        basedFiberFunctorHom η W.unop.left
          (W.unop.hom ^*[canonicalPullbackChoice S.p] x) ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x).inv ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x).hom ≫
        (FibredCategoryMor.fiberFunctor K W.unop.left).map φ ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
        simpa only [Category.assoc] using hright.symm
    _ = _ := by
        simp only [← Category.assoc]
        rfl

/-- Helper for Chap08 Lemma 8 8 3: a `2`-morphism after precomposition forces a fiber morphism
on any target object once a local source model for that object has been chosen. -/
private noncomputable def precomposeForcedFiberHom
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y) :
    ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) :=
  (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx.inv ≫
    basedFiberFunctorHom τ U x ≫
    (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map cx.hom

/-- Helper for Chap08 Lemma 8 8 3: if two local source models of the same target object differ by
a source morphism whose `G`-image is the discrepancy between the two model isomorphisms, then the
forced local `2`-morphism component is independent of the chosen model. -/
private theorem precomposeForcedFiberHom_eq_of_imageDiscrepancy
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y)
    (x' : S.p.Fiber U)
    (cx' : ((FibredCategoryMor.fiberFunctor G U).obj x') ≅ y)
    (γ : x ⟶ x')
    (hγ : (FibredCategoryMor.fiberFunctor G U).map γ = cx.hom ≫ cx'.inv) :
    precomposeForcedFiberHom G τ y x cx =
      precomposeForcedFiberHom G τ y x' cx' := by
  -- Naturality of `τ` across `γ` gives the middle square; the two `cx` isomorphisms cancel the
  -- discrepancy on the source and target sides.
  dsimp only [precomposeForcedFiberHom]
  have hnat :
      (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map
            ((FibredCategoryMor.fiberFunctor G U).map γ) ≫ basedFiberFunctorHom τ U x' =
        basedFiberFunctorHom τ U x ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            ((FibredCategoryMor.fiberFunctor G U).map γ) := by
    exact basedFiberFunctorHom_naturality τ γ
  rw [hγ, Functor.map_comp, Functor.map_comp] at hnat
  have hKcancel :
      (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map cx.hom =
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map cx.hom ≫
            (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
              cx'.inv) ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            cx'.hom := by
    -- Insert the inverse of the second model isomorphism on the target side.
    rw [Category.assoc, ← Functor.map_comp, cx'.inv_hom_id, Functor.map_id, Category.comp_id]
  rw [hKcancel]
  have hnatStep :=
    congrArg
      (fun t =>
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map
            cx.inv ≫ t ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            cx'.hom)
      hnat.symm
  have hcollapse :
      (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx.inv ≫
          (((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map
                cx.hom ≫
              (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map
                cx'.inv) ≫
            basedFiberFunctorHom τ U x') ≫
            (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
              cx'.hom =
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx'.inv ≫
          basedFiberFunctorHom τ U x' ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            cx'.hom := by
    -- The leading source-side factors reduce from `cx.inv ≫ cx.hom ≫ cx'.inv` to `cx'.inv`.
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, cx.inv_hom_id, Category.id_comp]
  calc
    (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx.inv ≫
        basedFiberFunctorHom τ U x ≫
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
              cx.hom ≫
            (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
              cx'.inv) ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            cx'.hom =
      (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx.inv ≫
        (basedFiberFunctorHom τ U x ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map cx.hom ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            cx'.inv) ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
          cx'.hom := by
        simp only [Category.assoc]
    _ =
      (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx.inv ≫
        (((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map
              cx.hom ≫
            (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map
              cx'.inv) ≫
          basedFiberFunctorHom τ U x') ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
          cx'.hom := hnatStep
    _ =
      (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx'.inv ≫
        basedFiberFunctorHom τ U x' ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
          cx'.hom := hcollapse

/-- Helper for Chap08 Lemma 8 8 3: on a literal source-image object, the forced component is the
given precomposed fiber component. -/
private theorem precomposeForcedFiberHom_on_image
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (x : S.p.Fiber U) :
    precomposeForcedFiberHom G τ
        ((FibredCategoryMor.fiberFunctor G U).obj x) x (Iso.refl _) =
      basedFiberFunctorHom τ U x := by
  -- The two outer isomorphism maps are identities for the trivial source model.
  simp only [precomposeForcedFiberHom, Iso.refl_inv, Iso.refl_hom, Functor.map_id,
    Category.id_comp]
  exact Category.comp_id (basedFiberFunctorHom τ U x)

/-- Helper for Chap08 Lemma 8 8 3: changing the represented target object by a fiber isomorphism
conjugates the forced component by the target stack morphisms. -/
private theorem precomposeForcedFiberHom_transport_of_fiberIso
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} {y y' : S'.p.Fiber U} (e : y ≅ y')
    (x' : S.p.Fiber U)
    (cx' : ((FibredCategoryMor.fiberFunctor G U).obj x') ≅ y') :
    (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map e.hom ≫
        precomposeForcedFiberHom G τ y' x' cx' ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map e.inv =
      precomposeForcedFiberHom G τ y x' (cx' ≪≫ e.symm) := by
  -- Expanding the forced components exposes the composed model isomorphism; functoriality then
  -- reassociates the outer transports into the right normal form.
  dsimp only [precomposeForcedFiberHom]
  have hinv : (cx' ≪≫ e.symm).inv = e.hom ≫ cx'.inv := rfl
  have hhom : (cx' ≪≫ e.symm).hom = cx'.hom ≫ e.inv := rfl
  rw [hinv, hhom, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rfl

/-- Helper for Chap08 Lemma 8 8 3: cancel two inverse-then-hom isomorphism blocks inside a
long categorical composite. -/
private theorem cancel_two_iso_blocks
    {Cat : Type*} [Category Cat] {A B C D E F G H I L : Cat}
    (a : A ⟶ B) (b : B ⟶ C) (e : D ≅ C)
    (c : C ⟶ E) (d : E ⟶ F) (g : F ⟶ G)
    (f : H ≅ G) (h : G ⟶ I) (i : I ⟶ L) :
    ((a ≫ b ≫ e.inv) ≫ (((e.hom ≫ c) ≫ d ≫ g ≫ f.inv) ≫ f.hom ≫ h ≫ i)) =
      a ≫ b ≫ c ≫ d ≫ ((g ≫ h) ≫ i) := by
  -- Normalize associativity once, then remove the two adjacent `inv ≫ hom` pairs.
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Helper for Chap08 Lemma 8 8 3: cancel one `inv ≫ hom` block in the middle of an
associated categorical composite. -/
private theorem comp_inv_hom_assoc_cancel
    {Cat : Type*} [Category Cat] {A B C D : Cat}
    (a : A ⟶ B) (e : C ≅ B) (b : B ⟶ D) :
    (a ≫ e.inv) ≫ (e.hom ≫ b) = a ≫ b := by
  -- Reassociate to expose the inverse pair, cancel it, and remove the identity.
  calc
    (a ≫ e.inv) ≫ (e.hom ≫ b) = a ≫ (e.inv ≫ e.hom) ≫ b := by
      simp only [Category.assoc]
    _ = a ≫ 𝟙 _ ≫ b := by
      rw [e.inv_hom_id]
    _ = a ≫ b := by
      simp only [Category.id_comp]

/-- Helper for Chap08 Lemma 8 8 3: cancel a `hom ≫ inv` block after a prefix. -/
private theorem comp_hom_inv_assoc_cancel
    {Cat : Type*} [Category Cat] {A B C : Cat}
    (a : A ⟶ B) (e : B ≅ C) :
    (a ≫ e.hom) ≫ e.inv = a := by
  calc
    (a ≫ e.hom) ≫ e.inv = a ≫ (e.hom ≫ e.inv) := by
      simp only [Category.assoc]
    _ = a ≫ 𝟙 _ := by
      rw [e.hom_inv_id]
    _ = a := Category.comp_id a

/-- Helper for Chap08 Lemma 8 8 3: cancel a leading `hom ≫ inv` block. -/
private theorem hom_inv_comp_assoc_cancel
    {Cat : Type*} [Category Cat] {A B D : Cat}
    (e : A ≅ B) (b : A ⟶ D) :
    (e.hom ≫ e.inv) ≫ b = b := by
  calc
    (e.hom ≫ e.inv) ≫ b = 𝟙 _ ≫ b := by
      rw [e.hom_inv_id]
    _ = b := Category.id_comp b

/-- Helper for Chap08 Lemma 8 8 3: combine two outer cocycle normalizations with one middle
transport normalization in a long categorical sandwich. -/
private theorem composeCocycleSandwich
    {Cat : Type*} [Category Cat]
    {A B C D E F G H I J : Cat}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : A ⟶ E) (e : E ⟶ D)
    (f : D ⟶ F) (g : F ⟶ G) (h : G ⟶ H)
    (i : H ⟶ I) (j : F ⟶ J) (k : J ⟶ I)
    (n : E ⟶ J)
    (hL : a ≫ b ≫ c = d ≫ e)
    (hR : g ≫ h ≫ i = j ≫ k)
    (hM : e ≫ f ≫ j = n) :
    a ≫ (b ≫ (c ≫ f ≫ g) ≫ h) ≫ i = d ≫ n ≫ k := by
  -- First expose the two cocycle blocks, then rewrite the middle transported block.
  calc
    a ≫ (b ≫ (c ≫ f ≫ g) ≫ h) ≫ i = (a ≫ b ≫ c) ≫ f ≫ (g ≫ h ≫ i) := by
      simp only [Category.assoc]
    _ = (d ≫ e) ≫ f ≫ (j ≫ k) := by
      rw [hL, hR]
    _ = d ≫ (e ≫ f ≫ j) ≫ k := by
      simp only [Category.assoc]
    _ = d ≫ n ≫ k := by
      rw [hM]

/-- Helper for Chap08 Lemma 8 8 3: cancel a common conjugation shell from both sides of a
categorical equality. -/
private theorem eqOfConjugationShell
    {Cat : Type*} [Category Cat]
    {A B C D : Cat}
    (αinv : B ⟶ A) (α : A ⟶ B)
    (l r : B ⟶ C)
    (β : C ⟶ D) (βhom : D ⟶ C)
    (hα : αinv ≫ α = 𝟙 B)
    (hβ : β ≫ βhom = 𝟙 C)
    (h : α ≫ l ≫ β = α ≫ r ≫ β) :
    l = r := by
  -- Multiply the shell equality by the inverse shell on both sides and cancel the two identities.
  calc
    l = 𝟙 _ ≫ l ≫ 𝟙 _ := by
      simp only [Category.id_comp, Category.comp_id]
    _ = (αinv ≫ α) ≫ l ≫ (β ≫ βhom) := by
      rw [hα, hβ]
    _ = αinv ≫ (α ≫ l ≫ β) ≫ βhom := by
      simp only [Category.assoc]
    _ = αinv ≫ (α ≫ r ≫ β) ≫ βhom := by
      rw [h]
    _ = (αinv ≫ α) ≫ r ≫ (β ≫ βhom) := by
      simp only [Category.assoc]
    _ = r := by
      rw [hα, hβ]
      simp only [Category.id_comp, Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 3: the forced local component is compatible with pullback, with
the expected conjugation by the pullback-comparison isomorphisms for the two target stack
morphisms. -/
private theorem precomposeForcedFiberHom_pullback
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y) :
    ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (precomposeForcedFiberHom G τ y x cx) =
      (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) f y).hom ≫
        precomposeForcedFiberHom G τ (f ^*[canonicalPullbackChoice S'.p] y)
          (f ^*[canonicalPullbackChoice S.p] x)
    ((FibredCategoryMor.pullbackComparison G f x).symm ≪≫
      (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.mapIso cx)) ≫
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f y).inv := by
  -- Expand both forced components, then split the pullback of the threefold composite on the
  -- left. The explicit `change` fixes the association Lean needs for `Functor.map_comp`.
  simp only [precomposeForcedFiberHom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv]
  change ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cx.inv ≫
        (basedFiberFunctorHom τ U x ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            cx.hom)) = _
  rw [Functor.map_comp, Functor.map_comp]
  -- The two outer factors are exactly naturality of the target morphisms' pullback-comparison
  -- isomorphisms across the vertical arrows `cx.inv` and `cx.hom`.
  have hB :
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map
            cx.inv) =
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) f y).hom ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) V).map
            (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map cx.inv) ≫
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) f
            ((FibredCategoryMor.fiberFunctor G U).obj x)).inv := by
    have h := FibredCategoryMor.pullbackComparison_naturality_over_vertical
      (stack_morphism_toFibredCategoryMor H) f cx.inv
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 h
  have hC :
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map
            cx.hom) =
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f
            ((FibredCategoryMor.fiberFunctor G U).obj x)).hom ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) V).map
            (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map cx.hom) ≫
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f y).inv := by
    have h := FibredCategoryMor.pullbackComparison_naturality_over_vertical
      (stack_morphism_toFibredCategoryMor K) f cx.hom
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 h
  -- Normalize the middle component from the composite morphism spelling `(G ≫ H)` / `(G ≫ K)`
  -- to the explicit spelling needed to cancel with the two outer factors.
  have hHcomp :
      (FibredCategoryMor.pullbackComparison (G ≫ stack_morphism_toFibredCategoryMor H) f x).hom =
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) f
            ((FibredCategoryMor.fiberFunctor G U).obj x)).hom ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) V).map
            (FibredCategoryMor.pullbackComparison G f x).hom :=
    pullbackComparison_comp_hom G (stack_morphism_toFibredCategoryMor H) f x
  have hKcomp :
      (FibredCategoryMor.pullbackComparison (G ≫ stack_morphism_toFibredCategoryMor K) f x).inv =
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) V).map
            (FibredCategoryMor.pullbackComparison G f x).inv ≫
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f
            ((FibredCategoryMor.fiberFunctor G U).obj x)).inv := by
    have hiso :
        FibredCategoryMor.pullbackComparison (G ≫ stack_morphism_toFibredCategoryMor K) f x =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f
              ((FibredCategoryMor.fiberFunctor G U).obj x) ≪≫
            (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) V).mapIso
              (FibredCategoryMor.pullbackComparison G f x)) := by
      apply Iso.ext
      simp only [Iso.trans_hom, Functor.mapIso_hom]
      exact pullbackComparison_comp_hom G (stack_morphism_toFibredCategoryMor K) f x
    rw [hiso]
    simp only [Iso.trans_inv, Functor.mapIso_inv]
  have hA := basedFiberFunctorHom_pullback_bridge τ f x
  rw [hHcomp, hKcomp] at hA
  -- Substitute the three bridges and cancel the adjacent pullback-comparison isomorphisms.
  erw [hB, hA, hC]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  exact
    cancel_two_iso_blocks
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) f y).hom
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) V).map
          (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map cx.inv))
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) f
          ((FibredCategoryMor.fiberFunctor G U).obj x))
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) V).map
          (FibredCategoryMor.pullbackComparison G f x).hom)
        (basedFiberFunctorHom τ V (f ^*[canonicalPullbackChoice S.p] x))
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) V).map
          (FibredCategoryMor.pullbackComparison G f x).inv)
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f
          ((FibredCategoryMor.fiberFunctor G U).obj x))
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) V).map
          (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map cx.hom))
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f y).inv

/-- Helper for Chap08 Lemma 8 8 3: the identity `pullHom` restriction of a forced local cover
component is the component itself. -/
private theorem precomposeForcedFiberHom_component_pullHom_id
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) (x : S.p.Fiber V)
    (cx : ((FibredCategoryMor.fiberFunctor G V).obj x) ≅
      f ^*[canonicalPullbackChoice S'.p] y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        ((FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor H) f y).hom ≫
          precomposeForcedFiberHom G τ
            (f ^*[canonicalPullbackChoice S'.p] y) x cx ≫
          (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor K) f y).inv)
        (𝟙 V) f f =
      (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor H) f y).hom ≫
        precomposeForcedFiberHom G τ
          (f ^*[canonicalPullbackChoice S'.p] y) x cx ≫
        (FibredCategoryMor.pullbackComparison
            (stack_morphism_toFibredCategoryMor K) f y).inv := by
  -- The plan lowers the compatibility problem to `pullHom`; in the identity-overlap case,
  -- mathlib's `pullHom_id` gives the required normalization directly.
  exact
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id
      (F := canonicalFiberPseudofunctor X.p)
      ((FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor H) f y).hom ≫
        precomposeForcedFiberHom G τ
          (f ^*[canonicalPullbackChoice S'.p] y) x cx ≫
        (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor K) f y).inv)

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the pullback-comparison cocycle for a composite base arrow
holds after applying a fibred morphism. -/
theorem pullbackComparison_mapComp_hom_cocycle
    {Y₀ Z₀ : FibredCategoryOver C} (K : Y₀ ⟶ Z₀)
    {W Z Wmid : C} (i_f : Wmid ⟶ W) (fi : Z ⟶ Wmid) (q : Z ⟶ W)
    (hq : fi ≫ i_f = q)
    (y : Y₀.p.Fiber W) :
    ((canonicalFiberPseudofunctor Z₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
      ((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison K i_f y).hom ≫
        (FibredCategoryMor.pullbackComparison K fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y)).hom =
      (FibredCategoryMor.pullbackComparison K q y).hom ≫
        (FibredCategoryMor.fiberFunctor K Z).map
          ((((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app y)) := by
  -- Compare the two vertical arrows after postcomposition with the chosen cartesian arrow over
  -- the composite base arrow `q`; this is the stable normal form needed for non-identity overlaps.
  apply Functor.Fiber.hom_ext
  set Kf := FibredCategoryMor.fiberFunctor K W with hKf
  set θ : ((FibredCategoryMor.fiberFunctor K Z).obj
        (fi ^*[canonicalPullbackChoice Y₀.p] (i_f ^*[canonicalPullbackChoice Y₀.p] y))).1 ⟶
      (Kf.obj y).1 :=
    K.toHom.map ((canonicalPullbackChoice Y₀.p).map fi
        (i_f ^*[canonicalPullbackChoice Y₀.p] y)) ≫
      K.toHom.map ((canonicalPullbackChoice Y₀.p).map i_f y) with hθ
  have hθcart : Z₀.p.IsStronglyCartesian q θ := by
    letI hcart_fi : Z₀.p.IsStronglyCartesian fi
        (K.toHom.map ((canonicalPullbackChoice Y₀.p).map fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y))) :=
      FibredCategoryMor.map_stronglyCartesian_of_lift K fi
        ((canonicalPullbackChoice Y₀.p).map fi (i_f ^*[canonicalPullbackChoice Y₀.p] y))
        ((canonicalPullbackChoice Y₀.p).isStronglyCartesian fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y))
    letI hcart_if : Z₀.p.IsStronglyCartesian i_f
        (K.toHom.map ((canonicalPullbackChoice Y₀.p).map i_f y)) :=
      FibredCategoryMor.map_stronglyCartesian_of_lift K i_f
        ((canonicalPullbackChoice Y₀.p).map i_f y)
        ((canonicalPullbackChoice Y₀.p).isStronglyCartesian i_f y)
    have hcomp : Z₀.p.IsStronglyCartesian (fi ≫ i_f) θ := by
      rw [hθ]
      infer_instance
    rwa [hq] at hcomp
  letI : Z₀.p.IsStronglyCartesian q θ := hθcart
  set Ahom := ((canonicalFiberPseudofunctor Z₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app (Kf.obj y)
    with hAhom
  set cI_Y₀ := (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc
      q.op.toLoc (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app y)
    with hcI_Y₀
  refine Functor.IsStronglyCartesian.ext Z₀.p q θ (𝟙 Z) ?_
  change (Ahom.1 ≫
        (((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison K i_f y).hom).1 ≫
          (FibredCategoryMor.pullbackComparison K fi
            (i_f ^*[canonicalPullbackChoice Y₀.p] y)).hom.1) ≫ θ =
      ((FibredCategoryMor.pullbackComparison K q y).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor K Z).map cI_Y₀).1) ≫ θ
  -- Both postcomposites are the same chosen pullback arrow over `q`.
  have hY₀fac : cI_Y₀.1 ≫
        (canonicalPullbackChoice Y₀.p).map fi (i_f ^*[canonicalPullbackChoice Y₀.p] y) ≫
        (canonicalPullbackChoice Y₀.p).map i_f y =
      (canonicalPullbackChoice Y₀.p).map q y := by
    have := FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      Y₀.p i_f fi q hq y
    simpa only [hcI_Y₀] using this
  have hZ₀fac : Ahom.1 ≫
        (canonicalPullbackChoice Z₀.p).map fi
          (((canonicalFiberPseudofunctor Z₀.p).map i_f.op.toLoc).toFunctor.obj (Kf.obj y)) ≫
        (canonicalPullbackChoice Z₀.p).map i_f (Kf.obj y) =
      (canonicalPullbackChoice Z₀.p).map q (Kf.obj y) := by
    have := FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      Z₀.p i_f fi q hq (Kf.obj y)
    simpa only [hAhom] using this
  have hθ1 : θ =
      K.toHom.map ((canonicalPullbackChoice Y₀.p).map fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y)) ≫
        K.toHom.map ((canonicalPullbackChoice Y₀.p).map i_f y) := hθ
  have hKZ : ((FibredCategoryMor.fiberFunctor K Z).map cI_Y₀).1 = K.toHom.map cI_Y₀.1 := rfl
  have hMfi := FibredCategoryMor.canonical_pullbackFunctor_map_fac Z₀.p fi
      (FibredCategoryMor.pullbackComparison K i_f y).hom
  have hRHS : ((FibredCategoryMor.pullbackComparison K q y).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor K Z).map cI_Y₀).1) ≫ θ =
      (canonicalPullbackChoice Z₀.p).map q (Kf.obj y) := by
    rw [hKZ, hθ1]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [hY₀fac]
    exact FibredCategoryMor.pullbackComparison_hom_postcompose K q y
  have hpost_fi := FibredCategoryMor.pullbackComparison_hom_postcompose K fi
    (i_f ^*[canonicalPullbackChoice Y₀.p] y)
  have hpost_if := FibredCategoryMor.pullbackComparison_hom_postcompose K i_f y
  have hLHS : (Ahom.1 ≫
        (((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison K i_f y).hom).1 ≫
          (FibredCategoryMor.pullbackComparison K fi
            (i_f ^*[canonicalPullbackChoice Y₀.p] y)).hom.1) ≫ θ =
      (canonicalPullbackChoice Z₀.p).map q (Kf.obj y) := by
    rw [hθ1]
    rw [Category.assoc, Category.assoc]
    rw [reassoc_of% hpost_fi]
    rw [reassoc_of% hMfi]
    rw [hpost_if]
    exact hZ₀fac
  rw [hLHS, hRHS]

/-- Helper for Chap08 Lemma 8 8 3: if a threefold composite of isomorphism-like arrows equals a
twofold composite, then the formal inverse threefold composite equals the formal inverse twofold
composite. -/
private theorem threeCompInverse_eq_twoCompInverse_of_comp_eq
    {Cat : Type*} [Category Cat]
    {A B D E F : Cat}
    (a : A ⟶ B) (ai : B ⟶ A)
    (b : B ⟶ D) (bi : D ⟶ B)
    (c : D ⟶ E) (ci : E ⟶ D)
    (d : A ⟶ F) (di : F ⟶ A)
    (e : F ⟶ E) (ei : E ⟶ F)
    (hd : d ≫ di = 𝟙 A) (he : e ≫ ei = 𝟙 F)
    (ha : ai ≫ a = 𝟙 B) (hb : bi ≫ b = 𝟙 D) (hc : ci ≫ c = 𝟙 E)
    (hcomp : a ≫ b ≫ c = d ≫ e) :
    ci ≫ bi ≫ ai = ei ≫ di := by
  -- Insert the inverse of the right-hand composite, rewrite the middle by `hcomp`, and cancel the
  -- three inverse pairs in order.
  have hright : (d ≫ e) ≫ ei ≫ di = 𝟙 A := by
    slice_lhs 2 3 => rw [he]
    simpa using hd
  calc
    ci ≫ bi ≫ ai = (ci ≫ bi ≫ ai) ≫ ((d ≫ e) ≫ ei ≫ di) := by
      rw [hright, Category.comp_id]
    _ = (ci ≫ bi ≫ ai) ≫ ((a ≫ b ≫ c) ≫ ei ≫ di) := by
      rw [hcomp]
    _ = ei ≫ di := by
      slice_lhs 3 4 => rw [ha]
      simp only [Category.id_comp]
      slice_lhs 2 3 => rw [hb]
      simp only [Category.id_comp]
      slice_lhs 1 2 => rw [hc]
      simp only [Category.id_comp]

/-- Helper for Chap08 Lemma 8 8 3: the inverse pullback-comparison cocycle for a composite
base arrow follows by inverting the hom-side cocycle. -/
theorem pullbackComparison_mapComp_inv_cocycle
    {Y₀ Z₀ : FibredCategoryOver C} (K : Y₀ ⟶ Z₀)
    {W Z Wmid : C} (i_f : Wmid ⟶ W) (fi : Z ⟶ Wmid) (q : Z ⟶ W)
    (hq : fi ≫ i_f = q)
    (y : Y₀.p.Fiber W) :
    (FibredCategoryMor.pullbackComparison K fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y)).inv ≫
      ((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison K i_f y).inv ≫
        ((canonicalFiberPseudofunctor Z₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y) =
      (FibredCategoryMor.fiberFunctor K Z).map
          (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).inv.toNatTrans.app y) ≫
        (FibredCategoryMor.pullbackComparison K q y).inv := by
  -- The hom-side cocycle identifies the forward composite; the rest of the proof supplies the
  -- five inverse identities needed by the raw categorical cancellation lemma above.
  have hcomp := pullbackComparison_mapComp_hom_cocycle K i_f fi q hq y
  have hd :
      (FibredCategoryMor.pullbackComparison K q y).hom ≫
          (FibredCategoryMor.pullbackComparison K q y).inv =
        𝟙 _ := by
    exact (FibredCategoryMor.pullbackComparison K q y).hom_inv_id
  have he :
      (FibredCategoryMor.fiberFunctor K Z).map
          (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app y) ≫
        (FibredCategoryMor.fiberFunctor K Z).map
          (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).inv.toNatTrans.app y) =
        𝟙 _ := by
    have hY :
        (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app y) ≫
          (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).inv.toNatTrans.app y) =
          𝟙 _ :=
      Cat.Hom.hom_inv_id_toNatTrans_app
        ((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)) y
    rw [← Functor.map_comp]
    exact (congrArg ((FibredCategoryMor.fiberFunctor K Z).map) hY).trans (Functor.map_id _ _)
  have ha :
      ((canonicalFiberPseudofunctor Z₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
        ((canonicalFiberPseudofunctor Z₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) =
        𝟙 _ := by
    exact Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hb :
      ((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison K i_f y).inv ≫
        ((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison K i_f y).hom =
        𝟙 _ := by
    have hPull :
        (FibredCategoryMor.pullbackComparison K i_f y).inv ≫
          (FibredCategoryMor.pullbackComparison K i_f y).hom =
        𝟙 _ :=
      (FibredCategoryMor.pullbackComparison K i_f y).inv_hom_id
    rw [← Functor.map_comp]
    exact
      (congrArg
        (((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map) hPull).trans
        (Functor.map_id _ _)
  have hc :
      (FibredCategoryMor.pullbackComparison K fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y)).inv ≫
        (FibredCategoryMor.pullbackComparison K fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y)).hom =
        𝟙 _ := by
    exact (FibredCategoryMor.pullbackComparison K fi
      (i_f ^*[canonicalPullbackChoice Y₀.p] y)).inv_hom_id
  exact
    threeCompInverse_eq_twoCompInverse_of_comp_eq
      (((canonicalFiberPseudofunctor Z₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y))
      (((canonicalFiberPseudofunctor Z₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y))
      (((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison K i_f y).hom)
      (((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison K i_f y).inv)
      (FibredCategoryMor.pullbackComparison K fi
        (i_f ^*[canonicalPullbackChoice Y₀.p] y)).hom
      (FibredCategoryMor.pullbackComparison K fi
        (i_f ^*[canonicalPullbackChoice Y₀.p] y)).inv
      (FibredCategoryMor.pullbackComparison K q y).hom
      (FibredCategoryMor.pullbackComparison K q y).inv
      ((FibredCategoryMor.fiberFunctor K Z).map
        (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).hom.toNatTrans.app y))
      ((FibredCategoryMor.fiberFunctor K Z).map
        (((canonicalFiberPseudofunctor Y₀.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)).inv.toNatTrans.app y))
      hd he ha hb hc hcomp

/-- Helper for Chap08 Lemma 8 8 3: the sieve underlying a cover of the identity slice object
pushes forward to a covering sieve on the base. -/
private theorem sieveOverEquiv_mem_of_identitySliceCover
    {W : C} (T : (J.over W).Cover (Over.mk (𝟙 W))) :
    Sieve.overEquiv (Over.mk (𝟙 W)) T.1 ∈ J W := by
  -- The slice topology was defined so covers of the identity slice object are exactly base covers.
  have hT : T.1 ∈ (J.over W) (Over.mk (𝟙 W)) := T.2
  rw [J.mem_over_iff] at hT
  exact hT

/-- Helper for Chap08 Lemma 8 8 3: push a cover of the identity slice object back down to the
base site. -/
private noncomputable def baseCoverOfIdentitySliceCover
    {W : C} (T : (J.over W).Cover (Over.mk (𝟙 W))) :
    J.Cover W :=
  ⟨Sieve.overEquiv (Over.mk (𝟙 W)) T.1, sieveOverEquiv_mem_of_identitySliceCover (J := J) T⟩

/-- Helper for Chap08 Lemma 8 8 3: membership in the pushed-down base cover is membership of the
corresponding identity-slice arrow upstairs. -/
private theorem baseCoverOfIdentitySliceCover_arrow_mem
    {W : C} (T : (J.over W).Cover (Over.mk (𝟙 W)))
    (I : (baseCoverOfIdentitySliceCover (J := J) T).Arrow) :
    T.1 (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)) :=
  -- The base cover was defined through `Sieve.overEquiv`, so this is the defining equivalence.
  (Sieve.overEquiv_iff (Y := Over.mk (𝟙 W)) T.1 I.f).1 I.hf

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: over the identity slice object, the Hom-presheaf restriction
is the canonical pullback-functor action on a fiber morphism. -/
private theorem identitySlicePresheafHom_map_hom
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g : Over.mk (g ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map (g ≫ 𝟙 W).op.toLoc).toFunctor.map φ := by
  -- Expand the presheaf restriction once and collapse the identity-slice `mapId` conjugation.
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫
          φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  rw [hmid]
  -- The rest is the naturality square for `mapComp'` specialized to the identity slice object.
  rw [(canonicalFiberPseudofunctor p).mapComp'_naturality_2]
  rfl

/-- Helper for Chap08 Lemma 8 8 3: a pullback-comparison conjugate is unchanged when the base
arrow is replaced by an equal arrow, up to the evident `eqToHom` casts. -/
private theorem pullbackComparison_conjugate_eqToHom_cast
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y.toFibredCategoryOver)
    {W V : C} {b b' : V ⟶ W} (hbb : b = b')
    (x x' : S₀.p.Fiber W)
    (φ : ((FibredCategoryMor.fiberFunctor G W).obj x) ⟶
        ((FibredCategoryMor.fiberFunctor G W).obj x'))
    (h₁ : ((FibredCategoryMor.fiberFunctor G V).obj (b' ^*[canonicalPullbackChoice S₀.p] x)) =
        ((FibredCategoryMor.fiberFunctor G V).obj (b ^*[canonicalPullbackChoice S₀.p] x)))
    (h₂ : ((FibredCategoryMor.fiberFunctor G V).obj (b ^*[canonicalPullbackChoice S₀.p] x')) =
        ((FibredCategoryMor.fiberFunctor G V).obj (b' ^*[canonicalPullbackChoice S₀.p] x'))) :
    eqToHom h₁ ≫
        (FibredCategoryMor.pullbackComparison G b x).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map b.op.toLoc).toFunctor.map φ ≫
          (FibredCategoryMor.pullbackComparison G b x').hom ≫
        eqToHom h₂ =
      (FibredCategoryMor.pullbackComparison G b' x).inv ≫
        ((canonicalFiberPseudofunctor Y.p).map b'.op.toLoc).toFunctor.map φ ≫
        (FibredCategoryMor.pullbackComparison G b' x').hom := by
  -- After substituting the equal base arrows, both casts are identities.
  subst hbb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 3: the image sieve of a locally surjective presheaf map is a
cover, with the value universe left arbitrary. -/
private theorem imageSieve_mem_anyType
    {D : Type uS} [Category.{vS} D] (K : GrothendieckTopology D)
    {F G : Dᵒᵖ ⥤ Type w} (f : F ⟶ G) [Presheaf.IsLocallySurjective K f]
    {T : D} (s : G.obj (op T)) :
    Presheaf.imageSieve f s ∈ K T :=
  Presheaf.imageSieve_mem K f s

/-- Helper for Chap08 Lemma 8 8 3: choose the local preimage supplied by a presheaf image
sieve, with the value universe left arbitrary. -/
private noncomputable def localPreimage_anyType
    {D : Type uS} [Category.{vS} D]
    {F G : Dᵒᵖ ⥤ Type w} (f : F ⟶ G)
    {T : D} (s : G.obj (op T)) {V : D} (g : V ⟶ T)
    (hg : Presheaf.imageSieve f s g) :
    F.obj (op V) :=
  Presheaf.localPreimage f s g hg

/-- Helper for Chap08 Lemma 8 8 3: the chosen local preimage maps to the prescribed restricted
section. -/
private theorem app_localPreimage_anyType
    {D : Type uS} [Category.{vS} D]
    {F G : Dᵒᵖ ⥤ Type w} (f : F ⟶ G)
    {T : D} (s : G.obj (op T)) {V : D} (g : V ⟶ T)
    (hg : Presheaf.imageSieve f s g) :
    f.app (op V) (localPreimage_anyType f s g hg) = G.map g.op s := by
  simpa using Presheaf.app_localPreimage f s g hg

/-- Helper for Chap08 Lemma 8 8 3: the local-surjectivity part of the stackification condition
gives the image cover for a Hom-presheaf section, without saturating the stack universe. -/
private noncomputable abbrev stackificationHomImageCover
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {U : C} {x y : S₀.p.Fiber U}
    [(J.over U).WEqualsLocallyBijective (Type vS)]
    (β :
      ((canonicalFiberPseudofunctor Y.p).presheafHom
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        ((FibredCategoryMor.fiberFunctor G U).obj y)).obj
          (op (Over.mk (𝟙 U)))) :
    (J.over U).Cover (Over.mk (𝟙 U)) :=
  haveI := (hG.morphismPresheafMap_W U x y).isLocallySurjective
  ⟨Presheaf.imageSieve (FibredCategoryMor.fibredMorphismPresheafMap G x y) β,
    imageSieve_mem_anyType (J.over U)
      (FibredCategoryMor.fibredMorphismPresheafMap G x y) β⟩

/-- Helper for Chap08 Lemma 8 8 3: over the image cover, a target Hom-presheaf section has a
source-side local preimage. -/
private theorem stackificationCoverwiseHomLift
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {U : C} {x y : S₀.p.Fiber U}
    [(J.over U).WEqualsLocallyBijective (Type vS)]
    (β :
      ((canonicalFiberPseudofunctor Y.p).presheafHom
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        ((FibredCategoryMor.fiberFunctor G U).obj y)).obj
          (op (Over.mk (𝟙 U))))
    (I : (stackificationHomImageCover (J := J) G hG (x := x) (y := y) β).Arrow) :
    ∃ γI :
        ((canonicalFiberPseudofunctor S₀.p).presheafHom x y).obj (op I.Y),
      (FibredCategoryMor.fibredMorphismPresheafMap G x y).app (op I.Y) γI =
        (((canonicalFiberPseudofunctor Y.p).presheafHom
          ((FibredCategoryMor.fiberFunctor G U).obj x)
          ((FibredCategoryMor.fiberFunctor G U).obj y)).map I.f.op) β := by
  -- The cover is the image sieve, so the local preimage and its defining equation solve the
  -- coverwise lifting obligation.
  haveI := (hG.morphismPresheafMap_W U x y).isLocallySurjective
  exact
    ⟨localPreimage_anyType (FibredCategoryMor.fibredMorphismPresheafMap G x y) β I.f I.hf,
      app_localPreimage_anyType
        (FibredCategoryMor.fibredMorphismPresheafMap G x y) β I.f I.hf⟩

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: on the base cover attached to the image sieve of a
discrepancy morphism, the discrepancy has a source-side lift with the expected pullback
comparison formula. -/
private theorem stackification_baseCover_hom_lift_image
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {W : C} (x x' : S₀.p.Fiber W)
    [(J.over W).WEqualsLocallyBijective (Type _)]
    (d : ((FibredCategoryMor.fiberFunctor G W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G W).obj x'))
    (I : (baseCoverOfIdentitySliceCover (J := J)
      (stackificationHomImageCover (J := J) G hG (x := x) (y := x')
        ((canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv d.hom))).Arrow) :
    ∃ γ : (I.f ^*[canonicalPullbackChoice S₀.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice S₀.p] x'),
      (FibredCategoryMor.fiberFunctor G I.Y).map γ =
        (FibredCategoryMor.pullbackComparison G I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison G I.f x').hom := by
  -- Work upstairs on the identity slice cover, where local surjectivity of the Hom presheaf
  -- supplies a raw lift; then cast it back to the base-cover pullback objects.
  let β : ((canonicalFiberPseudofunctor Y.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G W).obj x)
      ((FibredCategoryMor.fiberFunctor G W).obj x')).obj (op (Over.mk (𝟙 W))) :=
    (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv d.hom
  let Sslice : (J.over W).Cover (Over.mk (𝟙 W)) :=
    stackificationHomImageCover (J := J) G hG (x := x) (y := x') β
  let Islice : Sslice.Arrow :=
    ⟨Over.mk (I.f ≫ 𝟙 W), Over.homMk I.f,
      baseCoverOfIdentitySliceCover_arrow_mem (J := J) Sslice I⟩
  obtain ⟨γRaw, hγRaw⟩ :=
    stackificationCoverwiseHomLift (J := J) G hG (x := x) (y := x') β Islice
  have hfeq : I.f ≫ 𝟙 W = I.f := Category.comp_id _
  refine ⟨(eqToHom ?_) ≫ γRaw ≫ (eqToHom ?_), ?_⟩
  · simp only [Islice, Over.mk_hom, hfeq]
    rfl
  · simp only [Islice, Over.mk_hom, hfeq]
    rfl
  · have hγRawApp :
        (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x).hom ≫
            (FibredCategoryMor.fiberFunctor G Islice.Y.left).map γRaw ≫
            (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x').inv =
          (((canonicalFiberPseudofunctor Y.p).presheafHom
              ((FibredCategoryMor.fiberFunctor G W).obj x)
              ((FibredCategoryMor.fiberFunctor G W).obj x')).map Islice.f.op) β := by
      rw [← hγRaw]
      rfl
    rw [identitySlicePresheafHom_map_hom] at hγRawApp
    have hγRawMap :
        (FibredCategoryMor.fiberFunctor G I.Y).map γRaw =
          (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x).inv ≫
            ((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 W).op.toLoc).toFunctor.map d.hom ≫
            (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x').hom := by
      have h1 :=
        (Iso.eq_inv_comp (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x)).2
          hγRawApp
      have h2 :=
        (Iso.comp_inv_eq (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x')).1 h1
      rw [Category.assoc] at h2
      exact h2
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, hγRawMap]
    simpa only [Functor.map_comp, Category.assoc] using
      pullbackComparison_conjugate_eqToHom_cast G hfeq x x' d.hom
        (by simp only [hfeq])
        (by simp only [hfeq])

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: on the base cover attached to the image sieve of an
arbitrary target fiber morphism, the morphism has a source-side lift with the expected pullback
comparison formula. This is the non-isomorphism variant of
`stackification_baseCover_hom_lift_image`. -/
private theorem stackification_baseCover_hom_lift_image_hom
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {W : C} (x x' : S₀.p.Fiber W)
    [(J.over W).WEqualsLocallyBijective (Type _)]
    (d : ((FibredCategoryMor.fiberFunctor G W).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G W).obj x'))
    (I : (baseCoverOfIdentitySliceCover (J := J)
      (stackificationHomImageCover (J := J) G hG (x := x) (y := x')
        ((canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv d))).Arrow) :
    ∃ γ : (I.f ^*[canonicalPullbackChoice S₀.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice S₀.p] x'),
      (FibredCategoryMor.fiberFunctor G I.Y).map γ =
        (FibredCategoryMor.pullbackComparison G I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.map d ≫
          (FibredCategoryMor.pullbackComparison G I.f x').hom := by
  -- Work upstairs on the identity slice cover, where local surjectivity of the Hom presheaf
  -- supplies a raw lift; then cast it back to the base-cover pullback objects.
  let β : ((canonicalFiberPseudofunctor Y.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G W).obj x)
      ((FibredCategoryMor.fiberFunctor G W).obj x')).obj (op (Over.mk (𝟙 W))) :=
    (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv d
  let Sslice : (J.over W).Cover (Over.mk (𝟙 W)) :=
    stackificationHomImageCover (J := J) G hG (x := x) (y := x') β
  let Islice : Sslice.Arrow :=
    ⟨Over.mk (I.f ≫ 𝟙 W), Over.homMk I.f,
      baseCoverOfIdentitySliceCover_arrow_mem (J := J) Sslice I⟩
  obtain ⟨γRaw, hγRaw⟩ :=
    stackificationCoverwiseHomLift (J := J) G hG (x := x) (y := x') β Islice
  have hfeq : I.f ≫ 𝟙 W = I.f := Category.comp_id _
  refine ⟨(eqToHom ?_) ≫ γRaw ≫ (eqToHom ?_), ?_⟩
  · simp only [Islice, Over.mk_hom, hfeq]
    rfl
  · simp only [Islice, Over.mk_hom, hfeq]
    rfl
  · have hγRawApp :
        (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x).hom ≫
            (FibredCategoryMor.fiberFunctor G Islice.Y.left).map γRaw ≫
            (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x').inv =
          (((canonicalFiberPseudofunctor Y.p).presheafHom
              ((FibredCategoryMor.fiberFunctor G W).obj x)
              ((FibredCategoryMor.fiberFunctor G W).obj x')).map Islice.f.op) β := by
      rw [← hγRaw]
      rfl
    rw [identitySlicePresheafHom_map_hom] at hγRawApp
    have hγRawMap :
        (FibredCategoryMor.fiberFunctor G I.Y).map γRaw =
          (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x).inv ≫
            ((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 W).op.toLoc).toFunctor.map d ≫
            (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x').hom := by
      have h1 :=
        (Iso.eq_inv_comp (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x)).2
          hγRawApp
      have h2 :=
        (Iso.comp_inv_eq (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x')).1 h1
      rw [Category.assoc] at h2
      exact h2
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, hγRawMap]
    simpa only [Functor.map_comp, Category.assoc] using
      pullbackComparison_conjugate_eqToHom_cast G hfeq x x' d
        (by simp only [hfeq])
        (by simp only [hfeq])

/-- Helper for Chap08 Lemma 8 8 3: the base cover on which a discrepancy between two
`G`-image models is represented by a source-side morphism. -/
private noncomputable abbrev stackification_discrepancyImageBaseCover
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {W : C} (x x' : S₀.p.Fiber W)
    [(J.over W).WEqualsLocallyBijective (Type _)]
    (d : ((FibredCategoryMor.fiberFunctor G W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G W).obj x')) :
    J.Cover W :=
  baseCoverOfIdentitySliceCover (J := J)
    (stackificationHomImageCover (J := J) G hG (x := x) (y := x')
      ((canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv d.hom))

/-- Helper for Chap08 Lemma 8 8 3: on the discrepancy image base cover, the discrepancy has a
source-side lift with the pullback-comparison formula. -/
private theorem stackification_discrepancyImageBaseCover_hom_lift
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y.toFibredCategoryOver)
    (hG : FibredCategoryMor.IsStackification G)
    {W : C} (x x' : S₀.p.Fiber W)
    [(J.over W).WEqualsLocallyBijective (Type vS)]
    (d : ((FibredCategoryMor.fiberFunctor G W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G W).obj x'))
    (I : (stackification_discrepancyImageBaseCover (J := J) G hG x x' d).Arrow) :
    ∃ γ : (I.f ^*[canonicalPullbackChoice S₀.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice S₀.p] x'),
      (FibredCategoryMor.fiberFunctor G I.Y).map γ =
        (FibredCategoryMor.pullbackComparison G I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison G I.f x').hom := by
  exact stackification_baseCover_hom_lift_image (J := J) G hG x x' d I

/-- Helper for Chap08 Lemma 8 8 3: after refining to the discrepancy image cover, the forced
fiber component is independent of the chosen source model of the target fiber object. -/
private theorem precomposeForcedFiberHom_model_indep_of_locallyBijective
    {S₀ : FibredCategoryOver.{u, v, uS, vS} C}
    {Y Xtarget : StackOver.{u, v, uS, vS} J}
    (G : S₀ ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G)
    {H K : Y ⟶ Xtarget}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : Y.p.Fiber U) (x : S₀.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y)
    (x' : S₀.p.Fiber U)
    (cx' : ((FibredCategoryMor.fiberFunctor G U).obj x') ≅ y)
    [(J.over U).WEqualsLocallyBijective (Type vS)] :
    precomposeForcedFiberHom G τ y x cx =
      precomposeForcedFiberHom G τ y x' cx' := by
  -- Compare the two candidates after pulling back to the cover where the discrepancy between
  -- the two `G`-models has a source-side representative.
  let d : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G U).obj x') :=
    cx ≪≫ cx'.symm
  apply stack_cover_hom_ext (J := J) Xtarget
    (stackification_discrepancyImageBaseCover (J := J) G hG x x' d)
  intro I
  obtain ⟨γ, hγ⟩ := stackification_discrepancyImageBaseCover_hom_lift
    (J := J) G hG x x' d I
  rw [precomposeForcedFiberHom_pullback G τ I.f y x cx,
    precomposeForcedFiberHom_pullback G τ I.f y x' cx']
  -- The lifted source morphism realizes exactly the pulled-back discrepancy of the two models.
  have hγ' :
      (FibredCategoryMor.fiberFunctor G I.Y).map γ =
        (((FibredCategoryMor.pullbackComparison G I.f x).symm ≪≫
            (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.mapIso cx)).hom) ≫
          (((FibredCategoryMor.pullbackComparison G I.f x').symm ≪≫
            (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.mapIso cx')).inv) := by
    rw [hγ]
    simp only [d, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    let Mf := ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor
    let a := (FibredCategoryMor.pullbackComparison G I.f x).inv
    let b := Mf.map cx.hom
    let cMap := Mf.map cx'.inv
    let dMap := (FibredCategoryMor.pullbackComparison G I.f x').hom
    change a ≫ (Mf.map (cx.hom ≫ cx'.inv) ≫ dMap) =
      a ≫ (b ≫ (cMap ≫ dMap))
    have hmap :
        Mf.map (cx.hom ≫ cx'.inv) = b ≫ cMap := by
      exact Mf.map_comp cx.hom cx'.inv
    rw [hmap]
    exact congrArg (fun φ => a ≫ φ) (Category.assoc b cMap dMap)
  -- With the discrepancy represented by `γ`, the cover-free independence lemma applies on this
  -- cover member.
  rw [precomposeForcedFiberHom_eq_of_imageDiscrepancy G τ
    (I.f ^*[canonicalPullbackChoice Y.p] y)
    (I.f ^*[canonicalPullbackChoice S₀.p] x)
    ((FibredCategoryMor.pullbackComparison G I.f x).symm ≪≫
      (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.mapIso cx))
    (I.f ^*[canonicalPullbackChoice S₀.p] x')
    ((FibredCategoryMor.pullbackComparison G I.f x').symm ≪≫
      (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.mapIso cx'))
    γ hγ']

/-- Helper for Chap08 Lemma 8 8 3: forced components on literal `G`-image objects are natural
with respect to every target-side morphism between those image objects. -/
private theorem precomposeForcedFiberHom_image_naturality
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (x x' : S.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj x')) :
    (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map d ≫
        precomposeForcedFiberHom G τ
          ((FibredCategoryMor.fiberFunctor G U).obj x') x' (Iso.refl _) =
      precomposeForcedFiberHom G τ
          ((FibredCategoryMor.fiberFunctor G U).obj x) x (Iso.refl _) ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map d := by
  -- First compare the two canonical maps out of the target Hom presheaf.  They agree after
  -- precomposition with the `G` Hom-presheaf map, so the stackification `W` condition and
  -- sheafness of the target Hom presheaf identify them.
  have hMap :
      FibredCategoryMor.fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
          ((FibredCategoryMor.fiberFunctor G U).obj x)
          ((FibredCategoryMor.fiberFunctor G U).obj x') ≫
        presheafHomPostcompMap (basedFiberFunctorHom τ U x') =
      FibredCategoryMor.fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor K)
          ((FibredCategoryMor.fiberFunctor G U).obj x)
          ((FibredCategoryMor.fiberFunctor G U).obj x') ≫
        presheafHomPrecompMap (basedFiberFunctorHom τ U x) := by
    apply W_precomp_ext_to_sheaf (J := J.over U)
      (FibredCategoryMor.fibredMorphismPresheafMap G x x')
      (hG.morphismPresheafMap_W U x x')
    · exact
        Pseudofunctor.IsPrestack.isSheaf
          (F := canonicalFiberPseudofunctor X.p) (J := J) (S := U)
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj
            ((FibredCategoryMor.fiberFunctor G U).obj x))
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj
            ((FibredCategoryMor.fiberFunctor G U).obj x'))
    ·
      have hLeft :
          FibredCategoryMor.fibredMorphismPresheafMap G x x' ≫
              (FibredCategoryMor.fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor H)
                  ((FibredCategoryMor.fiberFunctor G U).obj x)
                  ((FibredCategoryMor.fiberFunctor G U).obj x') ≫
                presheafHomPostcompMap (basedFiberFunctorHom τ U x')) =
            FibredCategoryMor.fibredMorphismPresheafMap
                (G ≫ stack_morphism_toFibredCategoryMor H) x x' ≫
              presheafHomPostcompMap (basedFiberFunctorHom τ U x') := by
        rw [← Category.assoc]
        rw [← fibredMorphismPresheafMap_comp G (stack_morphism_toFibredCategoryMor H) x x']
        rfl
      have hRight :
          FibredCategoryMor.fibredMorphismPresheafMap G x x' ≫
              (FibredCategoryMor.fibredMorphismPresheafMap (stack_morphism_toFibredCategoryMor K)
                ((FibredCategoryMor.fiberFunctor G U).obj x)
                ((FibredCategoryMor.fiberFunctor G U).obj x') ≫
                presheafHomPrecompMap (basedFiberFunctorHom τ U x)) =
            FibredCategoryMor.fibredMorphismPresheafMap
                (G ≫ stack_morphism_toFibredCategoryMor K) x x' ≫
              presheafHomPrecompMap (basedFiberFunctorHom τ U x) := by
        rw [← Category.assoc]
        rw [← fibredMorphismPresheafMap_comp G (stack_morphism_toFibredCategoryMor K) x x']
        rfl
      exact hLeft.trans
        ((fibredMorphismPresheafMap_twoHom_naturality τ x x').trans hRight.symm)
  -- Evaluate the presheaf-map equality on the identity slice and translate the result through
  -- the identity-slice computation lemmas to obtain the ordinary fiberwise naturality square.
  have hEval :=
    congrArg
      (fun η =>
        η.app (op (Over.mk (𝟙 U)))
          ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv d))
      hMap
  have hPresheaf :
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map d ≫
            basedFiberFunctorHom τ U x') =
        (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
          (basedFiberFunctorHom τ U x ≫
            (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map d) := by
    simpa only [NatTrans.comp_app, fibredMorphismPresheafMap_app_id_local,
      presheafHomPostcompMap_app_id, presheafHomPrecompMap_app_id,
      types_comp_apply] using hEval
  have hFiber :
      (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map d ≫
          basedFiberFunctorHom τ U x' =
        basedFiberFunctorHom τ U x ≫
          (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map d :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv.injective hPresheaf
  rw [precomposeForcedFiberHom_on_image G τ x,
    precomposeForcedFiberHom_on_image G τ x']
  exact hFiber

/-- Helper for Chap08 Lemma 8 8 3: the forced component is independent of the chosen source
model once image-object naturality has been globalized from the Hom-presheaf `W` condition. -/
private theorem precomposeForcedFiberHom_model_indep
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y)
    (x' : S.p.Fiber U)
    (cx' : ((FibredCategoryMor.fiberFunctor G U).obj x') ≅ y) :
    precomposeForcedFiberHom G τ y x cx =
      precomposeForcedFiberHom G τ y x' cx' := by
  -- Compare the two source models through their target-side discrepancy and use the just-isolated
  -- image naturality square for that discrepancy.
  let Hf := FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U
  let Kf := FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U
  let d : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj x') :=
    cx.hom ≫ cx'.inv
  have hnat :=
    precomposeForcedFiberHom_image_naturality
      (J := J) (X := X) (G := G) hG τ x x' d
  rw [precomposeForcedFiberHom_on_image G τ x,
    precomposeForcedFiberHom_on_image G τ x'] at hnat
  -- Insert the inverse of `cx'` on the right, rewrite by naturality, and cancel the remaining
  -- isomorphism blocks.
  dsimp only [precomposeForcedFiberHom]
  have hKsplit :
      Kf.map cx.hom =
        Kf.map d ≫ Kf.map cx'.hom := by
    dsimp [d]
    rw [Functor.map_comp, Category.assoc, ← Functor.map_comp, cx'.inv_hom_id,
      Functor.map_id, Category.comp_id]
  have hHcollapse :
      Hf.map cx.inv ≫ Hf.map d = Hf.map cx'.inv := by
    have hsrc : cx.inv ≫ d = cx'.inv := by
      dsimp [d]
      rw [← Category.assoc, cx.inv_hom_id, Category.id_comp]
    rw [← Functor.map_comp]
    exact congrArg Hf.map hsrc
  have hnat' :
      Hf.map d ≫ basedFiberFunctorHom τ U x' =
        basedFiberFunctorHom τ U x ≫ Kf.map d := hnat
  rw [hKsplit]
  calc
    Hf.map cx.inv ≫ basedFiberFunctorHom τ U x ≫ Kf.map d ≫ Kf.map cx'.hom =
        Hf.map cx.inv ≫ (basedFiberFunctorHom τ U x ≫ Kf.map d) ≫
          Kf.map cx'.hom := by
          simp only [Category.assoc]
    _ = Hf.map cx.inv ≫ (Hf.map d ≫ basedFiberFunctorHom τ U x') ≫
          Kf.map cx'.hom := by
          exact
            congrArg (fun m ↦ Hf.map cx.inv ≫ m ≫ Kf.map cx'.hom) hnat'.symm
    _ = (Hf.map cx.inv ≫ Hf.map d) ≫ basedFiberFunctorHom τ U x' ≫
          Kf.map cx'.hom := by
          simp only [Category.assoc]
    _ = Hf.map cx'.inv ≫ basedFiberFunctorHom τ U x' ≫ Kf.map cx'.hom := by
          rw [hHcollapse]

/-- Helper for Chap08 Lemma 8 8 3: fixed-cover Hom descent can be consumed through its
componentwise characterization, avoiding repeated descent-data extensionality at gluing sites. -/
theorem stack_cover_hom_map_eq_of_componentwise
    (Z : StackOver J)
    {U : C} (S : J.Cover U)
    {x y : Z.p.Fiber U}
    (f : x ⟶ y)
    (δ :
      (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj x) ⟶
        (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj y))
    (hf :
      ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor Z.p).map I.f.op.toLoc).toFunctor.map f) = δ.hom I) :
    ((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).map f = δ := by
  -- A morphism of descent data is determined by its components on the chosen cover.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  exact hf I

/-- Helper for Chap08 Lemma 8 8 3: fixed-cover Hom descent gives a unique global morphism with a
prescribed componentwise description. -/
theorem stack_cover_hom_glue_existsUnique_componentwise
    (Z : StackOver J)
    {U : C} (S : J.Cover U)
    {x y : Z.p.Fiber U}
    (δ :
      (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj x) ⟶
        (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj y)) :
    ∃! f : x ⟶ y,
      ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor Z.p).map I.f.op.toLoc).toFunctor.map f) = δ.hom I := by
  -- Start from the fully faithful descent preimage, then read its equality componentwise on the
  -- fixed cover.
  obtain ⟨f, hf, _huniq⟩ := stack_cover_hom_glue (J := J) Z S δ
  refine ⟨f, ?_, ?_⟩
  · intro I
    have hI := congrArg (fun η ↦ η.hom I) hf
    simpa using hI
  · intro g hg
    -- Any other morphism with the same coverwise components is equal by stack Hom separation.
    apply stack_cover_hom_ext (J := J) Z S
    intro I
    have hfI := congrArg (fun η ↦ η.hom I) hf
    exact (hg I).trans (by simpa using hfI.symm)

/-- Helper for Chap08 Lemma 8 8 3: once the forced local components form a morphism of
descent data on a fixed cover, they glue to a unique global fiber component. -/
private theorem precomposeForcedFiberHom_globalComponent_existsUnique_of_descentDataHom
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (δ :
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)) ⟶
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)))
    (hδ :
      ∀ I : Scover.Arrow,
        δ.hom I =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv) :
    ∃! ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y),
      ∀ I : Scover.Arrow,
        (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map ηy) =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- The generic componentwise Hom-gluing lemma produces the global component from `δ`.
  obtain ⟨ηy, hηy, huniq⟩ :=
    stack_cover_hom_glue_existsUnique_componentwise (J := J) X Scover δ
  refine ⟨ηy, ?_, ?_⟩
  · intro I
    exact (hηy I).trans (hδ I)
  · intro μ hμ
    -- Uniqueness is reduced back to the same componentwise description of the descent morphism.
    apply huniq
    intro I
    exact (hμ I).trans (hδ I).symm

/-- Helper for Chap08 Lemma 8 8 3: a coverwise commutativity proof packages the forced local
components into a fixed-cover morphism of descent data. -/
private theorem precomposeForcedFiberHom_descentDataHom_of_comm
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hcomm :
      ∀ ⦃V : C⦄ (q : V ⟶ U) ⦃I₁ I₂ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q),
        ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor H) I₁.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I₁.f ^*[canonicalPullbackChoice S'.p] y) (model I₁).1
                (model I₁).2 ≫
              (FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor K) I₁.f y).inv) ≫
          (((canonicalFiberPseudofunctor X.p).toDescentData
              (fun I : Scover.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor
                (stack_morphism_toFibredCategoryMor K) U).obj y)).hom q f₁ f₂ hf₁ hf₂ =
        (((canonicalFiberPseudofunctor X.p).toDescentData
            (fun I : Scover.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor
              (stack_morphism_toFibredCategoryMor H) U).obj y)).hom q f₁ f₂ hf₁ hf₂ ≫
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor H) I₂.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I₂.f ^*[canonicalPullbackChoice S'.p] y) (model I₂).1
                (model I₂).2 ≫
              (FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor K) I₂.f y).inv)) :
    ∃ δ :
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)) ⟶
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)),
      ∀ I : Scover.Arrow,
        δ.hom I =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- The only content is the descent-data compatibility; once supplied, the component formula is
  -- the defining projection of the packaged morphism.
  let δ :
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)) ⟶
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)) :=
    { hom := fun I ↦
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
          precomposeForcedFiberHom G τ
            (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv
      comm := hcomm }
  refine ⟨δ, ?_⟩
  intro I
  rfl

/-- Helper for Chap08 Lemma 8 8 3: a coverwise commutativity proof is enough to glue the forced
local components to a unique global fiber component. -/
private theorem precomposeForcedFiberHom_globalComponent_existsUnique_of_comm
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hcomm :
      ∀ ⦃V : C⦄ (q : V ⟶ U) ⦃I₁ I₂ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q),
        ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor H) I₁.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I₁.f ^*[canonicalPullbackChoice S'.p] y) (model I₁).1
                (model I₁).2 ≫
              (FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor K) I₁.f y).inv) ≫
          (((canonicalFiberPseudofunctor X.p).toDescentData
              (fun I : Scover.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor
                (stack_morphism_toFibredCategoryMor K) U).obj y)).hom q f₁ f₂ hf₁ hf₂ =
        (((canonicalFiberPseudofunctor X.p).toDescentData
            (fun I : Scover.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor
              (stack_morphism_toFibredCategoryMor H) U).obj y)).hom q f₁ f₂ hf₁ hf₂ ≫
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor H) I₂.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I₂.f ^*[canonicalPullbackChoice S'.p] y) (model I₂).1
                (model I₂).2 ≫
              (FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor K) I₂.f y).inv)) :
    ∃! ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y),
      ∀ I : Scover.Arrow,
        (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map ηy) =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- First package the overlap compatibility as a descent-data morphism, then reuse the already
  -- proved componentwise Hom-gluing theorem.
  obtain ⟨δ, hδ⟩ :=
    precomposeForcedFiberHom_descentDataHom_of_comm
      (J := J) G τ y Scover model hcomm
  exact
    precomposeForcedFiberHom_globalComponent_existsUnique_of_descentDataHom
      (J := J) G τ y Scover model δ hδ

/-- Helper for Chap08 Lemma 8 8 3: a glued forced component is characterized by any abstract
model-independence theorem for the forced local components. -/
private theorem precomposeForcedFiberHom_globalComponent_eq_forced_of_modelIndep
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y))
    (hηy :
      ∀ I : Scover.Arrow,
        (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map ηy) =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv)
    (hmodelIndep :
      ∀ ⦃V : C⦄ (z : S'.p.Fiber V)
        (x₁ : S.p.Fiber V)
        (cx₁ : ((FibredCategoryMor.fiberFunctor G V).obj x₁) ≅ z)
        (x₂ : S.p.Fiber V)
        (cx₂ : ((FibredCategoryMor.fiberFunctor G V).obj x₂) ≅ z),
        precomposeForcedFiberHom G τ z x₁ cx₁ =
          precomposeForcedFiberHom G τ z x₂ cx₂)
    (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y) :
    ηy = precomposeForcedFiberHom G τ y x cx := by
  -- Test the glued global component on the cover used for gluing.
  apply stack_cover_hom_ext (J := J) X Scover
  intro I
  rw [hηy I, precomposeForcedFiberHom_pullback G τ I.f y x cx]
  -- The abstract model-independence input identifies the chosen cover model with the pulled-back
  -- arbitrary model of `y`.
  have hmodel :
      precomposeForcedFiberHom G τ
          (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 =
        precomposeForcedFiberHom G τ
          (I.f ^*[canonicalPullbackChoice S'.p] y)
          (I.f ^*[canonicalPullbackChoice S.p] x)
          ((FibredCategoryMor.pullbackComparison G I.f x).symm ≪≫
            (((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.mapIso cx)) :=
    hmodelIndep
      (I.f ^*[canonicalPullbackChoice S'.p] y)
      (model I).1 (model I).2
      (I.f ^*[canonicalPullbackChoice S.p] x)
      ((FibredCategoryMor.pullbackComparison G I.f x).symm ≪≫
        (((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.mapIso cx))
  rw [hmodel]

/-- Helper for Chap08 Lemma 8 8 3: a globally glued forced component is independent of the
chosen cover model and equals the forced component attached to any source model of the same
target fiber object. -/
private theorem precomposeForcedFiberHom_globalComponent_eq_forced
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y))
    (hηy :
      ∀ I : Scover.Arrow,
        (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map ηy) =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv)
    (hW : ∀ V : C, (J.over V).WEqualsLocallyBijective (Type vS))
    (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y) :
    ηy = precomposeForcedFiberHom G τ y x cx := by
  -- This wrapper supplies the local-bijectivity side condition to the abstract characterization
  -- lemma; the refactored descent helper below can later consume a no-side-condition replacement.
  refine
    precomposeForcedFiberHom_globalComponent_eq_forced_of_modelIndep
      (J := J) G τ y Scover model ηy hηy ?_ x cx
  intro V z x₁ cx₁ x₂ cx₂
  letI : (J.over V).WEqualsLocallyBijective (Type vS) := hW V
  exact
    precomposeForcedFiberHom_model_indep_of_locallyBijective
      (J := J) (S₀ := S) (Y := S') (Xtarget := X) (U := V)
      G hG τ z x₁ cx₁ x₂ cx₂

/-- Helper for Chap08 Lemma 8 8 3: the remaining fixed-cover Hom descent obligation is exactly the
existence of a descent-data morphism with the forced local components. -/
private theorem precomposeForcedFiberHom_globalComponent_existsUnique_of_descentDataHom_exists
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hdesc :
      ∃ δ :
        (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)) ⟶
        (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)),
        ∀ I : Scover.Arrow,
          δ.hom I =
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
              (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv) :
    ∃! ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y),
      ∀ I : Scover.Arrow,
        (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map ηy) =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- Unpack the descent-data morphism and apply the component-gluing bridge above.
  obtain ⟨δ, hδ⟩ := hdesc
  exact
    precomposeForcedFiberHom_globalComponent_existsUnique_of_descentDataHom
      (J := J) G τ y Scover model δ hδ

/-- Helper for Chap08 Lemma 8 8 3: a compatible family in the Hom presheaf gives the fixed-cover
descent-data morphism with the same forced local components. -/
private theorem precomposeForcedFiberHom_descentDataHom_exists_viaCompatible
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hcompat : Presieve.Arrows.Compatible
      ((canonicalFiberPseudofunctor X.p).presheafHom
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y))
      (X := fun I : Scover.Arrow ↦ Over.mk I.f)
      (B := Over.mk (𝟙 U))
      (fun I : Scover.Arrow ↦ Over.homMk I.f)
      (fun I : Scover.Arrow ↦
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
          precomposeForcedFiberHom G τ
            (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv)) :
    ∃ δ :
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)) ⟶
      (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)),
      ∀ I : Scover.Arrow,
        δ.hom I =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- Convert the compatible presheaf section through mathlib's canonical equivalence between
  -- compatible Hom sections and morphisms of fixed-cover descent data.
  refine ⟨Pseudofunctor.DescentData.subtypeCompatibleHomEquiv
      (canonicalFiberPseudofunctor X.p) (fun I : Scover.Arrow ↦ I.f) ?compatibleSection, ?_⟩
  · constructor
    · exact hcompat
  · -- The equivalence stores the compatible family as the component field of the descent morphism.
    intro I
    rfl

/-- Helper for Chap08 Lemma 8 8 3: compatible forced local components glue to a unique global
fiber component. -/
private theorem precomposeForcedFiberHom_globalComponent_existsUnique_of_compatible
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hcompat : Presieve.Arrows.Compatible
      ((canonicalFiberPseudofunctor X.p).presheafHom
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y))
      (X := fun I : Scover.Arrow ↦ Over.mk I.f)
      (B := Over.mk (𝟙 U))
      (fun I : Scover.Arrow ↦ Over.homMk I.f)
      (fun I : Scover.Arrow ↦
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
          precomposeForcedFiberHom G τ
            (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv)) :
    ∃! ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y),
      ∀ I : Scover.Arrow,
        (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map ηy) =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- First package compatibility as a descent-data morphism, then reuse the already proved
  -- componentwise fixed-cover Hom gluing theorem.
  have hdesc :=
    precomposeForcedFiberHom_descentDataHom_exists_viaCompatible
      (J := J) G τ y Scover model hcompat
  exact
    precomposeForcedFiberHom_globalComponent_existsUnique_of_descentDataHom_exists
      (J := J) G τ y Scover model hdesc

/-- Helper for Chap08 Lemma 8 8 3: the component of a pseudofunctorial composition comparison,
viewed as an isomorphism between the two chosen pullback objects. -/
noncomputable def mapCompAppIso
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc) (x : p.Fiber D) :
    (gf ^*[canonicalPullbackChoice p] x) ≅
      (g ^*[canonicalPullbackChoice p] (f ^*[canonicalPullbackChoice p] x)) where
  hom := ((canonicalFiberPseudofunctor p).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc hgf).hom.toNatTrans.app x
  inv := ((canonicalFiberPseudofunctor p).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc hgf).inv.toNatTrans.app x
  hom_inv_id := Cat.Hom.hom_inv_id_toNatTrans_app
    ((canonicalFiberPseudofunctor p).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc hgf) x
  inv_hom_id := Cat.Hom.inv_hom_id_toNatTrans_app
    ((canonicalFiberPseudofunctor p).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc hgf) x

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the pullback-comparison cocycle can be consumed as an
identity of isomorphisms. -/
private theorem pullbackComparison_mapComp_cocycle_iso
    {Y₀ Z₀ : FibredCategoryOver C} (K : Y₀ ⟶ Z₀)
    {W Z Wmid : C} (i_f : Wmid ⟶ W) (fi : Z ⟶ Wmid) (q : Z ⟶ W)
    (hq : fi ≫ i_f = q)
    (y : Y₀.p.Fiber W) :
    (mapCompAppIso Z₀.p i_f fi q (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)
        ((FibredCategoryMor.fiberFunctor K W).obj y) ≪≫
      ((canonicalFiberPseudofunctor Z₀.p).map fi.op.toLoc).toFunctor.mapIso
          (FibredCategoryMor.pullbackComparison K i_f y) ≪≫
        (FibredCategoryMor.pullbackComparison K fi
          (i_f ^*[canonicalPullbackChoice Y₀.p] y))) =
      (FibredCategoryMor.pullbackComparison K q y) ≪≫
        (FibredCategoryMor.fiberFunctor K Z).mapIso
          (mapCompAppIso Y₀.p i_f fi q (FibredCategoryMor.comp_toLoc_eq i_f fi q hq) y) := by
  -- The hom component is the raw cocycle already proved above; isomorphism extensionality then
  -- packages the same normal form for later one-leg rewrites.
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, mapCompAppIso]
  exact pullbackComparison_mapComp_hom_cocycle K i_f fi q hq y

/-- Helper for Chap08 Lemma 8 8 3: changing the base object of a forced component by a fiber
isomorphism only conjugates the two outer target transports. -/
private theorem precomposeForcedFiberHom_base_transport
    (G : S ⟶ S') {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} {y y' : S'.p.Fiber U} (cI : y ≅ y')
    (x' : S.p.Fiber U)
    (cx' : ((FibredCategoryMor.fiberFunctor G U).obj x') ≅ y') :
    (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map cI.hom ≫
        precomposeForcedFiberHom G τ y' x' cx' ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map cI.inv =
      precomposeForcedFiberHom G τ y x' (cx' ≪≫ cI.symm) := by
  -- This is the existing fiber-isomorphism transport lemma with the source and target names
  -- specialized to the stackification precomposition situation.
  exact precomposeForcedFiberHom_transport_of_fiberIso G τ cI x' cx'

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: one leg of a fixed-cover forced component, followed by a
pseudofunctorial composition comparison, normalizes to the forced component over the composite
base arrow. -/
private theorem precomposeForcedFiberHom_coverLeg_mapComp_normalized
    (G : S ⟶ S')
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) (I : Scover.Arrow) (fi : V ⟶ I.Y)
    (hfi : fi ≫ I.f = q) :
    ((canonicalFiberPseudofunctor X.p).mapComp' I.f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
        ((canonicalFiberPseudofunctor X.p).map fi.op.toLoc).toFunctor.map
          ((FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor K) I.f y).inv) ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' I.f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
      (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) q y).hom ≫
        precomposeForcedFiberHom G τ (q ^*[canonicalPullbackChoice S'.p] y)
          (fi ^*[canonicalPullbackChoice S.p] (model I).1)
          (((FibredCategoryMor.pullbackComparison G fi (model I).1).symm ≪≫
              (((canonicalFiberPseudofunctor S'.p).map fi.op.toLoc).toFunctor.mapIso
                (model I).2)) ≪≫
            (mapCompAppIso S'.p I.f fi q
              (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi) y).symm) ≫
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) q y).inv := by
  -- Pull back the local forced component, rewrite both outer comparison isomorphisms by the
  -- composite-base cocycle, and transport the middle forced component across the source-side
  -- `mapCompAppIso`.
  rw [Functor.map_comp, Functor.map_comp]
  rw [precomposeForcedFiberHom_pullback G τ fi
    (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2]
  have hBH := congrArg (fun (t : _ ≅ _) => t.hom)
    (pullbackComparison_mapComp_cocycle_iso
      (stack_morphism_toFibredCategoryMor H) I.f fi q hfi y)
  have hBK := congrArg (fun (t : _ ≅ _) => t.inv)
    (pullbackComparison_mapComp_cocycle_iso
      (stack_morphism_toFibredCategoryMor K) I.f fi q hfi y)
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, mapCompAppIso] at hBH hBK
  simp only [Category.assoc]
  rw [reassoc_of% hBH]
  rw [hBK]
  have hmid := precomposeForcedFiberHom_base_transport G τ
    (mapCompAppIso S'.p I.f fi q (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi) y)
    (fi ^*[canonicalPullbackChoice S.p] (model I).1)
    ((FibredCategoryMor.pullbackComparison G fi (model I).1).symm ≪≫
      (((canonicalFiberPseudofunctor S'.p).map fi.op.toLoc).toFunctor.mapIso (model I).2))
  have hS'hom :
      (((canonicalFiberPseudofunctor S'.p).mapComp' I.f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)).hom.toNatTrans.app y) =
        (mapCompAppIso S'.p I.f fi q (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)
          y).hom := rfl
  have hS'inv :
      (((canonicalFiberPseudofunctor S'.p).mapComp' I.f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)).inv.toNatTrans.app y) =
        (mapCompAppIso S'.p I.f fi q (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)
          y).inv := rfl
  rw [hS'hom, hS'inv]
  rw [reassoc_of% hmid]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the fixed-cover forced components satisfy the descent-data
commutativity condition after normalizing both overlap legs to the same common refinement. -/
private theorem precomposeForcedFiberHom_descentDataComm_of_modelIndep
    (G : S ⟶ S')
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hmodelIndep :
      ∀ ⦃V : C⦄ (z : S'.p.Fiber V)
        (x₁ : S.p.Fiber V)
        (cx₁ : ((FibredCategoryMor.fiberFunctor G V).obj x₁) ≅ z)
        (x₂ : S.p.Fiber V)
        (cx₂ : ((FibredCategoryMor.fiberFunctor G V).obj x₂) ≅ z),
        precomposeForcedFiberHom G τ z x₁ cx₁ =
          precomposeForcedFiberHom G τ z x₂ cx₂) :
    ∀ ⦃V : C⦄
      (q : V ⟶ U) ⦃I₁ I₂ : Scover.Arrow⦄
      (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q),
      ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
          ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) I₁.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I₁.f ^*[canonicalPullbackChoice S'.p] y) (model I₁).1
              (model I₁).2 ≫
            (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) I₁.f y).inv) ≫
        (((canonicalFiberPseudofunctor X.p).toDescentData
            (fun I : Scover.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor
              (stack_morphism_toFibredCategoryMor K) U).obj y)).hom q f₁ f₂ hf₁ hf₂ =
      (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : Scover.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor
            (stack_morphism_toFibredCategoryMor H) U).obj y)).hom q f₁ f₂ hf₁ hf₂ ≫
        ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
          ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) I₂.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I₂.f ^*[canonicalPullbackChoice S'.p] y) (model I₂).1
              (model I₂).2 ≫
            (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) I₂.f y).inv) := by
  -- Normalize both overlap legs to the same `q`-pullback forced component, then use local
  -- model independence over that common refinement and cancel the outer descent transition
  -- isomorphisms.
  intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
  -- Normalize a single cover leg to the common `q`-pullback forced component. This is the exact
  -- `mapComp.hom ≫ map fi(component) ≫ mapComp.inv` shell used by `ofObj.hom`.
  have key : ∀ (I : Scover.Arrow) (fi : V ⟶ I.Y) (hfi : fi ≫ I.f = q),
      ((canonicalFiberPseudofunctor X.p).mapComp' I.f.op.toLoc fi.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map fi.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
              (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) I.f y).inv) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' I.f.op.toLoc fi.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) q y).hom ≫
          precomposeForcedFiberHom G τ (q ^*[canonicalPullbackChoice S'.p] y)
            (fi ^*[canonicalPullbackChoice S.p] (model I).1)
            (((FibredCategoryMor.pullbackComparison G fi (model I).1).symm ≪≫
                (((canonicalFiberPseudofunctor S'.p).map fi.op.toLoc).toFunctor.mapIso
                  (model I).2)) ≪≫
              (mapCompAppIso S'.p I.f fi q
                (FibredCategoryMor.comp_toLoc_eq I.f fi q hfi) y).symm) ≫
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) q y).inv := by
    intro I fi hfi
    -- Consume the extracted one-leg normal form instead of repeating the transport proof here.
    exact
      precomposeForcedFiberHom_coverLeg_mapComp_normalized
        (J := J) (X := X) G τ y Scover model q I fi hfi
  -- The two normalized middle components are the same forced component, by local model
  -- independence over the common refinement object `q ^* y`.
  have hTeq :
      ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) I₁.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I₁.f ^*[canonicalPullbackChoice S'.p] y) (model I₁).1
                (model I₁).2 ≫
              (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) I₁.f y).inv) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) I₂.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I₂.f ^*[canonicalPullbackChoice S'.p] y) (model I₂).1
                (model I₂).2 ≫
              (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) I₂.f y).inv) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) := by
    rw [key I₁ f₁ hf₁, key I₂ f₂ hf₂]
    rw [hmodelIndep
      (q ^*[canonicalPullbackChoice S'.p] y)
      (f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1) _
      (f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1) _]
  -- Unfold the fixed-cover transition morphisms and cancel the extra `mapComp` factors on the
  -- outside of the normalized equality.
  dsimp only [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  have hcancel_H₁ :
      ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) =
        𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hcancel_K₂ :
      ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hA1 :
      ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
          ((FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor H) I₁.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I₁.f ^*[canonicalPullbackChoice S'.p] y) (model I₁).1
              (model I₁).2 ≫
            (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor K) I₁.f y).inv) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          (((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
            ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor H) I₁.f y).hom ≫
                precomposeForcedFiberHom G τ
                  (I₁.f ^*[canonicalPullbackChoice S'.p] y) (model I₁).1
                  (model I₁).2 ≫
                (FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor K) I₁.f y).inv) ≫
            ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)) := by
    calc
      _ = 𝟙 _ ≫ _ := by rw [Category.id_comp]
      _ =
          (((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
            ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)) ≫ _ := by
            rw [hcancel_H₁]
      _ = _ := by simp only [Category.assoc]
  have hA2 :
      ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) I₂.f y).hom ≫
              precomposeForcedFiberHom G τ
                (I₂.f ^*[canonicalPullbackChoice S'.p] y) (model I₂).1
                (model I₂).2 ≫
              (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) I₂.f y).inv) =
        (((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
            ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
              ((FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor H) I₂.f y).hom ≫
                precomposeForcedFiberHom G τ
                  (I₂.f ^*[canonicalPullbackChoice S'.p] y) (model I₂).1
                  (model I₂).2 ≫
                (FibredCategoryMor.pullbackComparison
                  (stack_morphism_toFibredCategoryMor K) I₂.f y).inv) ≫
            ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) := by
    calc
      _ = _ ≫ 𝟙 _ := by rw [Category.comp_id]
      _ =
          _ ≫
            (((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).inv.toNatTrans.app
                ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) ≫
              ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
                ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y)) := by
            rw [hcancel_K₂]
      _ = _ := by simp only [Category.assoc]
  rw [reassoc_of% hA1]
  conv_rhs => rw [Category.assoc, hA2]
  rw [reassoc_of% hTeq]
  simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: model-independent fixed-cover forced components glue to a
unique global forced fiber component. -/
private theorem precomposeForcedFiberHom_globalComponent_existsUnique_of_modelIndep
    (G : S ⟶ S')
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hmodelIndep :
      ∀ ⦃V : C⦄ (z : S'.p.Fiber V)
        (x₁ : S.p.Fiber V)
        (cx₁ : ((FibredCategoryMor.fiberFunctor G V).obj x₁) ≅ z)
        (x₂ : S.p.Fiber V)
        (cx₂ : ((FibredCategoryMor.fiberFunctor G V).obj x₂) ≅ z),
        precomposeForcedFiberHom G τ z x₁ cx₁ =
          precomposeForcedFiberHom G τ z x₂ cx₂) :
    ∃! ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y),
      ∀ I : Scover.Arrow,
        (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map ηy) =
          (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p] y) (model I).1 (model I).2 ≫
            (FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- First turn model independence into descent-data commutativity, then use stack Hom descent to
  -- glue the local forced components.
  exact
    precomposeForcedFiberHom_globalComponent_existsUnique_of_comm
      (J := J) G τ y Scover model
      (precomposeForcedFiberHom_descentDataComm_of_modelIndep
        (J := J) G τ y Scover model hmodelIndep)

/-- Helper for Chap08 Lemma 8 8 3: assuming model independence, the stackification cover over a
target object produces a global forced component characterized on every global source model. -/
private theorem precomposeForcedFiberHom_globalComponent_exists_of_modelIndep
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    (hmodelIndep :
      ∀ ⦃V : C⦄ (z : S'.p.Fiber V)
        (x₁ : S.p.Fiber V)
        (cx₁ : ((FibredCategoryMor.fiberFunctor G V).obj x₁) ≅ z)
        (x₂ : S.p.Fiber V)
        (cx₂ : ((FibredCategoryMor.fiberFunctor G V).obj x₂) ≅ z),
        precomposeForcedFiberHom G τ z x₁ cx₁ =
          precomposeForcedFiberHom G τ z x₂ cx₂)
    {U : C} (y : S'.p.Fiber U) :
    ∃ ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y),
      ∀ (x : S.p.Fiber U)
        (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y),
        ηy = precomposeForcedFiberHom G τ y x cx := by
  classical
  -- Choose the local source models supplied by stackification and glue their forced components.
  obtain ⟨Scover, hScover⟩ := hG.locallyEssentiallySurjectiveOnObjects U y
  let model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y :=
    fun I ↦ ⟨Classical.choose (hScover I),
      Classical.choice (Classical.choose_spec (hScover I))⟩
  obtain ⟨ηy, hηy, _huniq⟩ :=
    precomposeForcedFiberHom_globalComponent_existsUnique_of_modelIndep
      (J := J) G τ y Scover model hmodelIndep
  refine ⟨ηy, ?_⟩
  intro x cx
  -- The same model-independence hypothesis identifies the glued component with any chosen global
  -- source model of the target object.
  exact
    precomposeForcedFiberHom_globalComponent_eq_forced_of_modelIndep
      (J := J) G τ y Scover model ηy hηy hmodelIndep x cx

/-- Helper for Chap08 Lemma 8 8 3: a stackification morphism supplies a global forced component
for every target fiber object, using the no-side-condition model-independence theorem. -/
private theorem precomposeForcedFiberHom_globalComponent_exists
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) :
    ∃ ηy :
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y),
      ∀ (x : S.p.Fiber U)
        (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y),
        ηy = precomposeForcedFiberHom G τ y x cx := by
  -- The fixed-cover gluing helper only needs model independence; the previous theorem supplies it
  -- from image naturality and categorical cancellation.
  exact
    precomposeForcedFiberHom_globalComponent_exists_of_modelIndep
      (J := J) G hG τ
      (fun ⦃V : C⦄ z x₁ cx₁ x₂ cx₂ ↦
        precomposeForcedFiberHom_model_indep (J := J) G hG τ z x₁ cx₁ x₂ cx₂) y

/-- Helper for Chap08 Lemma 8 8 3: the fixed cover chosen from local essential surjectivity for
a target fiber object. -/
private noncomputable def precomposeForcedFiberHom_chosenComponentCover
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y : S'.p.Fiber U) :
    J.Cover U :=
  Classical.choose (hG.locallyEssentiallySurjectiveOnObjects U y)

/-- Helper for Chap08 Lemma 8 8 3: the chosen cover represents the target object locally by
source-fiber objects. -/
private theorem precomposeForcedFiberHom_chosenComponentCover_spec
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y : S'.p.Fiber U) :
    ∀ I : (precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y).Arrow,
      ∃ xI : S.p.Fiber I.Y,
        Nonempty
          (((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
            I.f ^*[canonicalPullbackChoice S'.p] y) := by
  -- This is exactly the witness property bundled with the chosen local-essential-image cover.
  exact Classical.choose_spec (hG.locallyEssentiallySurjectiveOnObjects U y)

/-- Helper for Chap08 Lemma 8 8 3: the fixed source model chosen on an arrow of the chosen
local-essential-image cover. -/
private noncomputable def precomposeForcedFiberHom_chosenComponentModel
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y : S'.p.Fiber U)
    (I : (precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y).Arrow) :
    Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y :=
  ⟨Classical.choose
      (precomposeForcedFiberHom_chosenComponentCover_spec (J := J) G hG y I),
    Classical.choice
      (Classical.choose_spec
        (precomposeForcedFiberHom_chosenComponentCover_spec (J := J) G hG y I))⟩

/-- Helper for Chap08 Lemma 8 8 3: choose the global forced component attached to a target
fiber object. -/
private noncomputable def precomposeForcedFiberHom_chosenComponent
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) :
    ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ⟶
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) :=
  Classical.choose
    (precomposeForcedFiberHom_globalComponent_existsUnique_of_modelIndep
      (J := J) G τ y
      (precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y)
      (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y)
      (fun ⦃_V : C⦄ z x₁ cx₁ x₂ cx₂ ↦
        precomposeForcedFiberHom_model_indep (J := J) G hG τ z x₁ cx₁ x₂ cx₂))

/-- Helper for Chap08 Lemma 8 8 3: on the chosen local cover, the chosen global forced component
restricts to the forced component attached to the chosen source model. -/
private theorem precomposeForcedFiberHom_chosenComponent_cover_pullback
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U)
    (I : (precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y).Arrow) :
    (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
        (precomposeForcedFiberHom_chosenComponent G hG τ y)) =
      (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor H) I.f y).hom ≫
        precomposeForcedFiberHom G τ
          (I.f ^*[canonicalPullbackChoice S'.p] y)
          (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y I).1
          (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y I).2 ≫
        (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor K) I.f y).inv := by
  -- Unpack the defining unique gluing theorem for the chosen global component.
  exact
    (Classical.choose_spec
      (precomposeForcedFiberHom_globalComponent_existsUnique_of_modelIndep
        (J := J) G τ y
        (precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y)
        (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y)
        (fun ⦃_V : C⦄ z x₁ cx₁ x₂ cx₂ ↦
          precomposeForcedFiberHom_model_indep (J := J) G hG τ z x₁ cx₁ x₂ cx₂))).1 I

/-- Helper for Chap08 Lemma 8 8 3: the chosen global forced component is the forced component
for every source model of the target fiber object. -/
private theorem precomposeForcedFiberHom_chosenComponent_eq_forced
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (y : S'.p.Fiber U) (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y) :
    precomposeForcedFiberHom_chosenComponent G hG τ y =
      precomposeForcedFiberHom G τ y x cx := by
  -- The stronger chosen component is still characterized by every global source model; apply the
  -- fixed-cover model-independence gluing theorem to the chosen cover and model.
  exact
    precomposeForcedFiberHom_globalComponent_eq_forced_of_modelIndep
      (J := J) G τ y
      (precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y)
      (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y)
      (precomposeForcedFiberHom_chosenComponent G hG τ y)
      (precomposeForcedFiberHom_chosenComponent_cover_pullback
        (J := J) (X := X) G hG τ y)
      (fun ⦃_V : C⦄ z x₁ cx₁ x₂ cx₂ ↦
        precomposeForcedFiberHom_model_indep (J := J) G hG τ z x₁ cx₁ x₂ cx₂)
      x cx

/-- Helper for Chap08 Lemma 8 8 3: on a literal source-image object, the chosen global forced
component is the original precomposed fiber component. -/
private theorem precomposeForcedFiberHom_chosenComponent_on_image
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} (x : S.p.Fiber U) :
    precomposeForcedFiberHom_chosenComponent G hG τ
        ((FibredCategoryMor.fiberFunctor G U).obj x) =
      basedFiberFunctorHom τ U x := by
  -- Specialize the source-model characterization to the tautological model and remove the
  -- identity transports.
  rw [precomposeForcedFiberHom_chosenComponent_eq_forced G hG τ
    ((FibredCategoryMor.fiberFunctor G U).obj x) x (Iso.refl _)]
  exact precomposeForcedFiberHom_on_image G τ x

/-- Helper for Chap08 Lemma 8 8 3: at a literal source object, the chosen global forced
component has underlying total morphism equal to the original precomposed `2`-morphism component. -/
private theorem precomposeForcedFiberHom_chosenComponent_source_app
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ :
      (stackification_precompose_functor X G).obj H ⟶
        (stackification_precompose_functor X G).obj K)
    (T : S.S) :
    (precomposeForcedFiberHom_chosenComponent G hG τ
        (⟨G.toHom.obj T, rfl⟩ : S'.p.Fiber (S'.p.obj (G.toHom.obj T)))).1 =
      τ.hom.hom.app T := by
  -- Reduce the source-object component to the already proved literal-image computation and then
  -- forget the fiber morphism to its underlying total-category arrow.
  let x : S.p.Fiber (S'.p.obj (G.toHom.obj T)) :=
    ⟨T, (G.toHom.w_obj T).symm⟩
  have h := congrArg (fun m => m.1)
    (precomposeForcedFiberHom_chosenComponent_on_image G hG τ x)
  exact h

/-- Helper for Chap08 Lemma 8 8 3: every total arrow factors through the chosen cartesian
pullback of its codomain by a vertical arrow in the source fiber. -/
theorem canonicalPullback_verticalFactor_exists
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {A B : T} (φ : A ⟶ B) :
    ∃ v : (Functor.Fiber.mk (p := p) (a := A) rfl : p.Fiber (p.obj A)) ⟶
        (p.map φ ^*[canonicalPullbackChoice p]
          (Functor.Fiber.mk (p := p) (a := B) rfl : p.Fiber (p.obj B))),
      v.1 ≫
        (canonicalPullbackChoice p).map (p.map φ)
          (Functor.Fiber.mk (p := p) (a := B) rfl : p.Fiber (p.obj B)) = φ := by
  -- Factor the arrow through the strongly cartesian chosen pullback; the universal property
  -- returns exactly the required vertical morphism and its factorization identity.
  let y : p.Fiber (p.obj B) := Functor.Fiber.mk (p := p) (a := B) rfl
  let cart := (canonicalPullbackChoice p).map (p.map φ) y
  have hcart : p.IsStronglyCartesian (p.map φ) cart :=
    (canonicalPullbackChoice p).isStronglyCartesian (p.map φ) y
  have hφ : p.IsHomLift (𝟙 (p.obj A) ≫ p.map φ) φ := by
    refine IsHomLift.of_fac p (𝟙 (p.obj A) ≫ p.map φ) φ rfl rfl ?_
    simp
  obtain ⟨χ, hχ, _⟩ :=
    @Functor.IsStronglyCartesian.universal_property' _ _ _ _ p _ _ _ _ (p.map φ) cart hcart A
      (𝟙 (p.obj A)) φ hφ
  refine ⟨⟨χ, hχ.1⟩, hχ.2⟩

/-- Helper for Chap08 Lemma 8 8 3: the pseudofunctorial composition shell around a pulled-back
chosen forced component collapses to the single composite-base pullback. -/
private theorem precomposeForcedFiberHom_chosenComponent_mapComp_naturality
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (q : W ⟶ U)
    (hgq : g ≫ f = q) (y : S'.p.Fiber U) :
    ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g q hgq)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
        ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            (precomposeForcedFiberHom_chosenComponent G hG τ y)) ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g q hgq)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
      ((canonicalFiberPseudofunctor X.p).map q.op.toLoc).toFunctor.map
        (precomposeForcedFiberHom_chosenComponent G hG τ y) := by
  -- This is exactly the naturality square for the composition comparison of the canonical
  -- fiber pseudofunctor, specialized to the chosen forced component.
  exact
    (canonicalFiberPseudofunctor X.p).mapComp'_naturality_2
      f.op.toLoc g.op.toLoc q.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq f g q hgq)
      (precomposeForcedFiberHom_chosenComponent G hG τ y)

/-- Helper for Chap08 Lemma 8 8 3: the chosen forced component commutes with pullback at the
fiber level, before converting the identity into total-category cartesian naturality. -/
private theorem precomposeForcedFiberHom_chosenComponent_pullback_factor_hom_core
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (precomposeForcedFiberHom_chosenComponent G hG τ y) =
      (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor H) f y).hom ≫
        precomposeForcedFiberHom_chosenComponent G hG τ
          (f ^*[canonicalPullbackChoice S'.p] y) ≫
        (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor K) f y).inv := by
  -- Route correction: the old proof used only the pullback of the cover chosen for `y`, which
  -- exposed the left component but left the chosen component of `f^* y` opaque. Work instead on
  -- the common refinement where both chosen-component formulas are available.
  apply stack_cover_hom_ext (J := J) X
    (((precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y).pullback f) ⊓
      precomposeForcedFiberHom_chosenComponentCover (J := J) G hG
        (f ^*[canonicalPullbackChoice S'.p] y))
  intro I
  let Ileft :=
    I.map (homOfLE inf_le_left :
      (((precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y).pullback f) ⊓
        precomposeForcedFiberHom_chosenComponentCover (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y)) ⟶
        (precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y).pullback f)
  let Ibase := Ileft.base
  let Iright :=
    I.map (homOfLE inf_le_right :
      (((precomposeForcedFiberHom_chosenComponentCover (J := J) G hG y).pullback f) ⊓
        precomposeForcedFiberHom_chosenComponentCover (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y)) ⟶
        precomposeForcedFiberHom_chosenComponentCover (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y))
  let q : I.Y ⟶ U := I.f ≫ f
  -- The left projection of the refinement is already a source model for the composite pullback
  -- `q^* y`; the shell naturality lemma converts the iterated pullback into this cover formula.
  have hLeftShell :
      ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
              (precomposeForcedFiberHom_chosenComponent G hG τ y)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        (FibredCategoryMor.pullbackComparison
            (stack_morphism_toFibredCategoryMor H) q y).hom ≫
          precomposeForcedFiberHom G τ
            (q ^*[canonicalPullbackChoice S'.p] y)
            (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y Ibase).1
            (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y Ibase).2 ≫
          (FibredCategoryMor.pullbackComparison
            (stack_morphism_toFibredCategoryMor K) q y).inv := by
    have hShell :=
      precomposeForcedFiberHom_chosenComponent_mapComp_naturality
        (J := J) (X := X) G hG τ f I.f q rfl y
    have hCover :=
      precomposeForcedFiberHom_chosenComponent_cover_pullback
        (J := J) (X := X) G hG τ y Ibase
    calc
      ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
              (precomposeForcedFiberHom_chosenComponent G hG τ y)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
          ((canonicalFiberPseudofunctor X.p).map q.op.toLoc).toFunctor.map
            (precomposeForcedFiberHom_chosenComponent G hG τ y) := hShell
      _ =
          (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor H) q y).hom ≫
            precomposeForcedFiberHom G τ
              (q ^*[canonicalPullbackChoice S'.p] y)
              (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y Ibase).1
              (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y Ibase).2 ≫
            (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor K) q y).inv := by
          exact hCover
  -- The right projection supplies the chosen-cover formula for the component at `f^* y`; the
  -- outer pullback comparisons are then combined by the cocycle isomorphism.
  have hRightShell :
      ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) f y).hom ≫
              precomposeForcedFiberHom_chosenComponent G hG τ
                (f ^*[canonicalPullbackChoice S'.p] y) ≫
              (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) f y).inv) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        (FibredCategoryMor.pullbackComparison
            (stack_morphism_toFibredCategoryMor H) q y).hom ≫
          precomposeForcedFiberHom G τ
            (q ^*[canonicalPullbackChoice S'.p] y)
            (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
              (f ^*[canonicalPullbackChoice S'.p] y) Iright).1
            ((precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
                (f ^*[canonicalPullbackChoice S'.p] y) Iright).2 ≪≫
              (mapCompAppIso S'.p f I.f q
                (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) y).symm) ≫
          (FibredCategoryMor.pullbackComparison
            (stack_morphism_toFibredCategoryMor K) q y).inv := by
    have hCoverRight :=
      precomposeForcedFiberHom_chosenComponent_cover_pullback
        (J := J) (X := X) G hG τ
        (f ^*[canonicalPullbackChoice S'.p] y) Iright
    have hCoverRightI :
        ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
            (precomposeForcedFiberHom_chosenComponent G hG τ
              (f ^*[canonicalPullbackChoice S'.p] y)) =
          (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor H) I.f
              (f ^*[canonicalPullbackChoice S'.p] y)).hom ≫
            precomposeForcedFiberHom G τ
              (I.f ^*[canonicalPullbackChoice S'.p]
                (f ^*[canonicalPullbackChoice S'.p] y))
              (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
                (f ^*[canonicalPullbackChoice S'.p] y) Iright).1
              (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
                (f ^*[canonicalPullbackChoice S'.p] y) Iright).2 ≫
            (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor K) I.f
              (f ^*[canonicalPullbackChoice S'.p] y)).inv := by
      exact hCoverRight
    have hBH :=
      pullbackComparison_mapComp_hom_cocycle
        (stack_morphism_toFibredCategoryMor H) f I.f q rfl y
    have hBK :=
      pullbackComparison_mapComp_inv_cocycle
        (stack_morphism_toFibredCategoryMor K) f I.f q rfl y
    rw [Functor.map_comp, Functor.map_comp]
    rw [hCoverRightI]
    have hmid := precomposeForcedFiberHom_base_transport
      (J := J) (X := X) G τ
      (mapCompAppIso S'.p f I.f q
        (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) y)
      (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
        (f ^*[canonicalPullbackChoice S'.p] y) Iright).1
      (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
        (f ^*[canonicalPullbackChoice S'.p] y) Iright).2
    -- The right shell is a categorical sandwich: the two outer cocycles expose the same
    -- composite-base comparison, and the middle transport lemma changes the source model.
    exact
      composeCocycleSandwich
        _ _ _ _ _ _ _ _ _ _ _ _
        hBH hBK hmid
  -- After both sides have the same shell, model independence identifies the two source models
  -- over the composite pullback `q^* y`.
  have hShellEq :
      ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
              (precomposeForcedFiberHom_chosenComponent G hG τ y)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
          ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor H) f y).hom ≫
              precomposeForcedFiberHom_chosenComponent G hG τ
                (f ^*[canonicalPullbackChoice S'.p] y) ≫
              (FibredCategoryMor.pullbackComparison
                (stack_morphism_toFibredCategoryMor K) f y).inv) ≫
            ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) := by
    have hModel :=
      precomposeForcedFiberHom_model_indep
        (J := J) (X := X) G hG τ
        (q ^*[canonicalPullbackChoice S'.p] y)
        (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y Ibase).1
        (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG y Ibase).2
        (precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y) Iright).1
        ((precomposeForcedFiberHom_chosenComponentModel (J := J) G hG
            (f ^*[canonicalPullbackChoice S'.p] y) Iright).2 ≪≫
          (mapCompAppIso S'.p f I.f q
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) y).symm)
    have hMiddle :=
      congrArg
        (fun m =>
          (FibredCategoryMor.pullbackComparison
            (stack_morphism_toFibredCategoryMor H) q y).hom ≫ m ≫
            (FibredCategoryMor.pullbackComparison
              (stack_morphism_toFibredCategoryMor K) q y).inv)
        hModel
    exact hLeftShell.trans (hMiddle.trans hRightShell.symm)
  -- Cancel the common composition-comparison shell, leaving the coverwise equality required by
  -- `stack_cover_hom_ext`.
  have hcancelH :
      ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y) =
        𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hcancelK :
      ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).obj y) =
        𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  -- The previous shell equality has the same comparison isomorphism on both sides; cancel it.
  exact
    eqOfConjugationShell
      _ _ _ _ _ _
      hcancelH hcancelK hShellEq

/-- Helper for Chap08 Lemma 8 8 3: the chosen forced components are natural along the canonical
cartesian pullback arrow of a target fiber object. -/
private theorem precomposeForcedFiberHom_chosenComponent_cartesian_naturality
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map
        ((canonicalPullbackChoice S'.p).map f y) ≫
        (precomposeForcedFiberHom_chosenComponent G hG τ y).1 =
      (precomposeForcedFiberHom_chosenComponent G hG τ
          (f ^*[canonicalPullbackChoice S'.p] y)).1 ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map
          ((canonicalPullbackChoice S'.p).map f y) := by
  -- Convert the fiber-level pullback factor into a total-category square by postcomposing with
  -- the chosen cartesian arrow over the target object `K(y)`.
  let H₀ := stack_morphism_toFibredCategoryMor H
  let K₀ := stack_morphism_toFibredCategoryMor K
  let ηy := precomposeForcedFiberHom_chosenComponent G hG τ y
  let ηfy :=
    precomposeForcedFiberHom_chosenComponent G hG τ
      (f ^*[canonicalPullbackChoice S'.p] y)
  let M := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  let cH := FibredCategoryMor.pullbackComparison H₀ f y
  let cK := FibredCategoryMor.pullbackComparison K₀ f y
  let cartK :=
    (canonicalPullbackChoice X.p).map f
      ((FibredCategoryMor.fiberFunctor K₀ U).obj y)
  have hCore : M.map ηy = cH.hom ≫ ηfy ≫ cK.inv := by
    exact
      precomposeForcedFiberHom_chosenComponent_pullback_factor_hom_core
        (J := J) (X := X) G hG τ f y
  have hFactor : cH.inv ≫ M.map ηy = ηfy ≫ cK.inv := by
    -- Cancel the source pullback-comparison isomorphism from the core factor identity.
    calc
      cH.inv ≫ M.map ηy = cH.inv ≫ (cH.hom ≫ ηfy ≫ cK.inv) := by
        exact congrArg (fun m ↦ cH.inv ≫ m) hCore
      _ = (cH.inv ≫ cH.hom) ≫ (ηfy ≫ cK.inv) := by
        simp only [Category.assoc]
      _ = ηfy ≫ cK.inv := by
        rw [cH.inv_hom_id]
        simp only [Category.id_comp]
  have hPost :
      ((cH.inv ≫ M.map ηy).1) ≫ cartK =
        ((ηfy ≫ cK.inv).1) ≫ cartK := by
    exact congrArg (fun m ↦ m.1 ≫ cartK) hFactor
  have hMap :
      (M.map ηy).1 ≫ cartK =
        (canonicalPullbackChoice X.p).map f
            ((FibredCategoryMor.fiberFunctor H₀ U).obj y) ≫ ηy.1 := by
    exact FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := X.p) (f := f)
      (φ := ηy)
  have hHpost :
      cH.inv.1 ≫
          (canonicalPullbackChoice X.p).map f
            ((FibredCategoryMor.fiberFunctor H₀ U).obj y) =
        (FibredCategoryMor.toFunctor H₀).map ((canonicalPullbackChoice S'.p).map f y) :=
    FibredCategoryMor.pullbackComparison_inv_postcompose_owner H₀ f y
  have hKpost :
      cK.inv.1 ≫ cartK =
        (FibredCategoryMor.toFunctor K₀).map ((canonicalPullbackChoice S'.p).map f y) :=
    FibredCategoryMor.pullbackComparison_inv_postcompose_owner K₀ f y
  have hStart :
      ((cH.inv ≫ M.map ηy).1) ≫ cartK =
        (FibredCategoryMor.toFunctor H₀).map ((canonicalPullbackChoice S'.p).map f y) ≫
          ηy.1 := by
    calc
      ((cH.inv ≫ M.map ηy).1) ≫ cartK =
          cH.inv.1 ≫ ((M.map ηy).1 ≫ cartK) := by
            change (cH.inv.1 ≫ (M.map ηy).1) ≫ cartK =
              cH.inv.1 ≫ ((M.map ηy).1 ≫ cartK)
            rw [Category.assoc]
      _ = cH.inv.1 ≫
            ((canonicalPullbackChoice X.p).map f
              ((FibredCategoryMor.fiberFunctor H₀ U).obj y) ≫ ηy.1) := by
            exact congrArg (fun m ↦ cH.inv.1 ≫ m) hMap
      _ = (cH.inv.1 ≫
            (canonicalPullbackChoice X.p).map f
              ((FibredCategoryMor.fiberFunctor H₀ U).obj y)) ≫ ηy.1 := by
            rw [← Category.assoc]
      _ = (FibredCategoryMor.toFunctor H₀).map ((canonicalPullbackChoice S'.p).map f y) ≫
            ηy.1 := by
            exact congrArg (fun m ↦ m ≫ ηy.1) hHpost
  have hEnd :
      ηfy.1 ≫
          (FibredCategoryMor.toFunctor K₀).map ((canonicalPullbackChoice S'.p).map f y) =
        ((ηfy ≫ cK.inv).1) ≫ cartK := by
    calc
      ηfy.1 ≫
          (FibredCategoryMor.toFunctor K₀).map ((canonicalPullbackChoice S'.p).map f y) =
          ηfy.1 ≫ (cK.inv.1 ≫ cartK) := by
            exact congrArg (fun m ↦ ηfy.1 ≫ m) hKpost.symm
      _ = ((ηfy ≫ cK.inv).1) ≫ cartK := by
            change ηfy.1 ≫ (cK.inv.1 ≫ cartK) = (ηfy.1 ≫ cK.inv.1) ≫ cartK
            rw [Category.assoc]
  exact hStart.symm.trans (hPost.trans hEnd.symm)

/-- Helper for Chap08 Lemma 8 8 3: cartesian naturality gives the corresponding equality of
vertical factors after pulling back a chosen forced component. -/
private theorem precomposeForcedFiberHom_chosenComponent_pullback_factor
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison
        (stack_morphism_toFibredCategoryMor H) f y).inv ≫
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (precomposeForcedFiberHom_chosenComponent G hG τ y) =
      precomposeForcedFiberHom_chosenComponent G hG τ
          (f ^*[canonicalPullbackChoice S'.p] y) ≫
        (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor K) f y).inv := by
  -- The inverse-comparison factor is the core pullback identity with the source comparison
  -- isomorphism canceled on the left.
  let M := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  let ηy := precomposeForcedFiberHom_chosenComponent G hG τ y
  let ηfy :=
    precomposeForcedFiberHom_chosenComponent G hG τ
      (f ^*[canonicalPullbackChoice S'.p] y)
  let cH := FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor H) f y
  let cK := FibredCategoryMor.pullbackComparison (stack_morphism_toFibredCategoryMor K) f y
  have hCore :=
    precomposeForcedFiberHom_chosenComponent_pullback_factor_hom_core
      (J := J) (X := X) G hG τ f y
  change cH.inv ≫ M.map ηy = ηfy ≫ cK.inv
  calc
    cH.inv ≫ M.map ηy = cH.inv ≫ (cH.hom ≫ ηfy ≫ cK.inv) := by
      exact congrArg (fun m ↦ cH.inv ≫ m) hCore
    _ = (cH.inv ≫ cH.hom) ≫ (ηfy ≫ cK.inv) := by
      simp only [Category.assoc]
    _ = ηfy ≫ cK.inv := by
      rw [cH.inv_hom_id]
      simp only [Category.id_comp]

/-- Helper for Chap08 Lemma 8 8 3: vertical morphisms transported by a pullback functor are
the `pullbackComparison` conjugate of the fiberwise transported morphism. -/
private theorem pullbackComparison_map_vertical_eq_hom_comp
    {Y Z : FibredCategoryOver C} (F : Y ⟶ Z)
    {U V : C} (f : V ⟶ U) {y y' : Y.p.Fiber U} (d : y ⟶ y') :
    ((canonicalFiberPseudofunctor Z.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor F U).map d) =
      (FibredCategoryMor.pullbackComparison F f y).hom ≫
        (FibredCategoryMor.fiberFunctor F V).map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map d) ≫
        (FibredCategoryMor.pullbackComparison F f y').inv := by
  -- Move the standard naturality square across the target comparison isomorphism so it can be
  -- consumed as a left-to-right normalization lemma.
  have h :=
    FibredCategoryMor.pullbackComparison_naturality_over_vertical F f d
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).2 h

/-- Helper for Chap08 Lemma 8 8 3: the pullback of a chosen forced component rewrites as a
`pullbackComparison` conjugate of the chosen component at the pulled-back object. -/
private theorem precomposeForcedFiberHom_chosenComponent_pullback_factor_hom
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (precomposeForcedFiberHom_chosenComponent G hG τ y) =
      (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor H) f y).hom ≫
        precomposeForcedFiberHom_chosenComponent G hG τ
          (f ^*[canonicalPullbackChoice S'.p] y) ≫
        (FibredCategoryMor.pullbackComparison
          (stack_morphism_toFibredCategoryMor K) f y).inv := by
  -- The stored factor lemma has an initial inverse comparison; multiply it by the comparison
  -- isomorphism to expose the pulled-back chosen component directly.
  have h :=
    precomposeForcedFiberHom_chosenComponent_pullback_factor
      (J := J) (X := X) G hG τ f y
  have h' :=
    ((Iso.eq_inv_comp
      (FibredCategoryMor.pullbackComparison
        (stack_morphism_toFibredCategoryMor H) f y)).1 h.symm).symm
  simpa only [Category.assoc] using h'

/-- Helper for Chap08 Lemma 8 8 3: forced components attached to arbitrary source models are
natural with respect to any vertical target morphism between the modeled objects. -/
private theorem precomposeForcedFiberHom_model_naturality
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} {y y' : S'.p.Fiber U}
    (x : S.p.Fiber U)
    (cx : ((FibredCategoryMor.fiberFunctor G U).obj x) ≅ y)
    (x' : S.p.Fiber U)
    (cx' : ((FibredCategoryMor.fiberFunctor G U).obj x') ≅ y')
    (d : y ⟶ y') :
    (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map d ≫
        precomposeForcedFiberHom G τ y' x' cx' =
      precomposeForcedFiberHom G τ y x cx ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map d := by
  -- Conjugate `d` to a morphism between literal `G`-image objects, apply image naturality there,
  -- and cancel the two model isomorphisms.
  let Hf := FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U
  let Kf := FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U
  let dG : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj x') :=
    cx.hom ≫ d ≫ cx'.inv
  have hnat :=
    precomposeForcedFiberHom_image_naturality
      (J := J) (X := X) G hG τ x x' dG
  rw [precomposeForcedFiberHom_on_image G τ x,
    precomposeForcedFiberHom_on_image G τ x'] at hnat
  dsimp only [precomposeForcedFiberHom]
  have hLeftCollapse :
      Hf.map d ≫ Hf.map cx'.inv =
        Hf.map cx.inv ≫ Hf.map dG := by
    have hsrc : cx.inv ≫ dG = d ≫ cx'.inv := by
      dsimp [dG]
      simp only [Iso.inv_hom_id_assoc]
    calc
      Hf.map d ≫ Hf.map cx'.inv = Hf.map (d ≫ cx'.inv) := by
        exact (Hf.map_comp d cx'.inv).symm
      _ = Hf.map (cx.inv ≫ dG) := by
        rw [hsrc]
      _ = Hf.map cx.inv ≫ Hf.map dG := by
        exact Hf.map_comp cx.inv dG
  have hRightCollapse :
      Kf.map dG ≫ Kf.map cx'.hom =
        Kf.map cx.hom ≫ Kf.map d := by
    have htgt : dG ≫ cx'.hom = cx.hom ≫ d := by
      dsimp [dG]
      simp only [Category.assoc]
      rw [cx'.inv_hom_id, Category.comp_id]
    calc
      Kf.map dG ≫ Kf.map cx'.hom = Kf.map (dG ≫ cx'.hom) := by
        exact (Kf.map_comp dG cx'.hom).symm
      _ = Kf.map (cx.hom ≫ d) := by
        rw [htgt]
      _ = Kf.map cx.hom ≫ Kf.map d := by
        exact Kf.map_comp cx.hom d
  calc
    Hf.map d ≫ Hf.map cx'.inv ≫ basedFiberFunctorHom τ U x' ≫ Kf.map cx'.hom =
        Hf.map cx.inv ≫ Hf.map dG ≫ basedFiberFunctorHom τ U x' ≫ Kf.map cx'.hom := by
          simpa only [← Category.assoc] using congrArg
            (fun m ↦ m ≫ (basedFiberFunctorHom τ U x' ≫ Kf.map cx'.hom))
            hLeftCollapse
    _ = Hf.map cx.inv ≫ (Hf.map dG ≫ basedFiberFunctorHom τ U x') ≫ Kf.map cx'.hom := by
          simp only [Category.assoc]
    _ = Hf.map cx.inv ≫ (basedFiberFunctorHom τ U x ≫ Kf.map dG) ≫
          Kf.map cx'.hom := by
          exact congrArg (fun m ↦ Hf.map cx.inv ≫ m ≫ Kf.map cx'.hom) hnat
    _ = Hf.map cx.inv ≫ basedFiberFunctorHom τ U x ≫
          (Kf.map dG ≫ Kf.map cx'.hom) := by
          simp only [Category.assoc]
    _ = Hf.map cx.inv ≫ basedFiberFunctorHom τ U x ≫
          (Kf.map cx.hom ≫ Kf.map d) := by
          exact congrArg
            (fun m ↦ Hf.map cx.inv ≫ (basedFiberFunctorHom τ U x ≫ m))
            hRightCollapse
    _ = (Hf.map cx.inv ≫ basedFiberFunctorHom τ U x ≫ Kf.map cx.hom) ≫
          Kf.map d := by
          simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the chosen forced components are natural for vertical arrows
inside a fixed target fiber. -/
private theorem precomposeForcedFiberHom_chosenComponent_vertical_naturality
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y') :
    (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).map d ≫
        precomposeForcedFiberHom_chosenComponent G hG τ y' =
      precomposeForcedFiberHom_chosenComponent G hG τ y ≫
        (FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor K) U).map d := by
  -- Restrict to a common cover where both endpoint fibers are represented by source objects.
  -- The remaining local square should be normalized with the pullback-factor bridge and closed
  -- by `precomposeForcedFiberHom_model_naturality`.
  obtain ⟨Scover, hScover⟩ := stackification_common_local_models (J := J) G hG y y'
  apply stack_cover_hom_ext (J := J) X Scover
  intro I
  obtain ⟨xI, xI', ⟨cxI⟩, ⟨cxI'⟩⟩ := hScover I
  -- Normalize each restricted composite into the same pullback-comparison shell, then use
  -- source-model naturality for the middle forced component.
  let FX := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
  let H₀ := stack_morphism_toFibredCategoryMor H
  let K₀ := stack_morphism_toFibredCategoryMor K
  let HfU := FibredCategoryMor.fiberFunctor H₀ U
  let KfU := FibredCategoryMor.fiberFunctor K₀ U
  let HfV := FibredCategoryMor.fiberFunctor H₀ I.Y
  let KfV := FibredCategoryMor.fiberFunctor K₀ I.Y
  let dI := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d
  let ηy := precomposeForcedFiberHom_chosenComponent G hG τ y
  let ηy' := precomposeForcedFiberHom_chosenComponent G hG τ y'
  let ηfy := precomposeForcedFiberHom_chosenComponent G hG τ
    (I.f ^*[canonicalPullbackChoice S'.p] y)
  let ηfy' := precomposeForcedFiberHom_chosenComponent G hG τ
    (I.f ^*[canonicalPullbackChoice S'.p] y')
  let cHy := FibredCategoryMor.pullbackComparison H₀ I.f y
  let cHy' := FibredCategoryMor.pullbackComparison H₀ I.f y'
  let cKy := FibredCategoryMor.pullbackComparison K₀ I.f y
  let cKy' := FibredCategoryMor.pullbackComparison K₀ I.f y'
  have hLeftMap :
      FX.map (HfU.map d ≫ ηy') = FX.map (HfU.map d) ≫ FX.map ηy' := by
    exact FX.map_comp (HfU.map d) ηy'
  have hRightMap :
      FX.map (ηy ≫ KfU.map d) = FX.map ηy ≫ FX.map (KfU.map d) := by
    exact FX.map_comp ηy (KfU.map d)
  have hH :
      FX.map (HfU.map d) = cHy.hom ≫ HfV.map dI ≫ cHy'.inv := by
    exact pullbackComparison_map_vertical_eq_hom_comp H₀ I.f d
  have hK :
      FX.map (KfU.map d) = cKy.hom ≫ KfV.map dI ≫ cKy'.inv := by
    exact pullbackComparison_map_vertical_eq_hom_comp K₀ I.f d
  have hηy :
      FX.map ηy = cHy.hom ≫ ηfy ≫ cKy.inv := by
    exact
      precomposeForcedFiberHom_chosenComponent_pullback_factor_hom
        (J := J) (X := X) G hG τ I.f y
  have hηy' :
      FX.map ηy' = cHy'.hom ≫ ηfy' ≫ cKy'.inv := by
    exact
      precomposeForcedFiberHom_chosenComponent_pullback_factor_hom
        (J := J) (X := X) G hG τ I.f y'
  have hModelChosen : HfV.map dI ≫ ηfy' = ηfy ≫ KfV.map dI := by
    change HfV.map dI ≫
        precomposeForcedFiberHom_chosenComponent G hG τ
          (I.f ^*[canonicalPullbackChoice S'.p] y') =
      precomposeForcedFiberHom_chosenComponent G hG τ
          (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
        KfV.map dI
    rw [precomposeForcedFiberHom_chosenComponent_eq_forced
      (J := J) (X := X) G hG τ
      (I.f ^*[canonicalPullbackChoice S'.p] y') xI' cxI']
    rw [precomposeForcedFiberHom_chosenComponent_eq_forced
      (J := J) (X := X) G hG τ
      (I.f ^*[canonicalPullbackChoice S'.p] y) xI cxI]
    exact
      precomposeForcedFiberHom_model_naturality
        (J := J) (X := X) G hG τ xI cxI xI' cxI' dI
  change FX.map (HfU.map d ≫ ηy') = FX.map (ηy ≫ KfU.map d)
  have hLeftNormalized :
      FX.map (HfU.map d ≫ ηy') =
        cHy.hom ≫ (ηfy ≫ KfV.map dI) ≫ cKy'.inv := by
    calc
      FX.map (HfU.map d ≫ ηy') = FX.map (HfU.map d) ≫ FX.map ηy' := hLeftMap
      _ = (cHy.hom ≫ HfV.map dI ≫ cHy'.inv) ≫
            (cHy'.hom ≫ ηfy' ≫ cKy'.inv) := by
            rw [hH, hηy']
            rfl
      _ = cHy.hom ≫ (HfV.map dI ≫ ηfy') ≫ cKy'.inv := by
            simpa only [Category.assoc] using
              comp_inv_hom_assoc_cancel (cHy.hom ≫ HfV.map dI) cHy'
                (ηfy' ≫ cKy'.inv)
      _ = cHy.hom ≫ (ηfy ≫ KfV.map dI) ≫ cKy'.inv := by
            exact congrArg (fun m ↦ cHy.hom ≫ m ≫ cKy'.inv) hModelChosen
  have hRightNormalized :
      FX.map (ηy ≫ KfU.map d) =
        cHy.hom ≫ (ηfy ≫ KfV.map dI) ≫ cKy'.inv := by
    calc
      FX.map (ηy ≫ KfU.map d) = FX.map ηy ≫ FX.map (KfU.map d) := hRightMap
      _ = (cHy.hom ≫ ηfy ≫ cKy.inv) ≫
            (cKy.hom ≫ KfV.map dI ≫ cKy'.inv) := by
            rw [hηy, hK]
            rfl
      _ = cHy.hom ≫ (ηfy ≫ KfV.map dI) ≫ cKy'.inv := by
            simpa only [Category.assoc] using
              comp_inv_hom_assoc_cancel (cHy.hom ≫ ηfy) cKy
                (KfV.map dI ≫ cKy'.inv)
  exact hLeftNormalized.trans hRightNormalized.symm

/-- Helper for Chap08 Lemma 8 8 3: the chosen global forced components are natural for arbitrary
arrows in the target total category. -/
private theorem precomposeForcedFiberHom_chosenComponent_naturality
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {H K : S' ⟶ X}
    (τ : (G ≫ stack_morphism_toFibredCategoryMor H) ⟶
      (G ≫ stack_morphism_toFibredCategoryMor K))
    {T T' : S'.S} (φ : T ⟶ T') :
    (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map φ ≫
        (precomposeForcedFiberHom_chosenComponent G hG τ
          (⟨T', rfl⟩ : S'.p.Fiber (S'.p.obj T'))).1 =
      (precomposeForcedFiberHom_chosenComponent G hG τ
          (⟨T, rfl⟩ : S'.p.Fiber (S'.p.obj T))).1 ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map φ := by
  -- Factor the arbitrary total arrow into a vertical arrow followed by the chosen cartesian
  -- pullback arrow, then compose the vertical and cartesian naturality squares.
  let yT : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let yT' : S'.p.Fiber (S'.p.obj T') :=
    Functor.Fiber.mk (p := S'.p) (a := T') rfl
  let yPull : S'.p.Fiber (S'.p.obj T) :=
    S'.p.map φ ^*[canonicalPullbackChoice S'.p] yT'
  let cart : yPull.1 ⟶ T' := (canonicalPullbackChoice S'.p).map (S'.p.map φ) yT'
  obtain ⟨v, hv⟩ := canonicalPullback_verticalFactor_exists S'.p φ
  have hcart :=
    precomposeForcedFiberHom_chosenComponent_cartesian_naturality
      (J := J) (X := X) G hG τ (S'.p.map φ) yT'
  have hvertFiber :=
    precomposeForcedFiberHom_chosenComponent_vertical_naturality
      (J := J) (X := X) G hG τ v
  have hvert :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yPull).1 =
        (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map v.1 := by
    -- Forget the fiberwise vertical naturality square to the ambient total category.
    exact congrArg (fun m => m.1) hvertFiber
  have hvcart : v.1 ≫ cart = φ := by
    -- Restate the cartesian factorization using the local aliases that occur below.
    simpa [cart, yT'] using hv
  have hcartTotal :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map cart ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1 =
        (precomposeForcedFiberHom_chosenComponent G hG τ yPull).1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart := by
    -- Restate cartesian naturality with the same `cart` and `yPull` aliases used in the
    -- factorization calculation.
    exact hcart
  have hmapH :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map (v.1 ≫ cart) =
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map cart := by
    -- Cache functoriality for this composite so later rewrites do not have to match through
    -- coercions from the fiber morphism.
    exact (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map_comp v.1 cart
  have hmapK :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map (v.1 ≫ cart) =
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map v.1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart := by
    -- The same cached functoriality identity is needed on the target side.
    exact (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map_comp v.1 cart
  change
    (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map φ ≫
        (precomposeForcedFiberHom_chosenComponent G hG τ yT').1 =
      (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map φ
  have hstepStart :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map φ ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1 =
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map (v.1 ≫ cart) ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1 := by
    -- Replace the original arrow by its vertical/cartesian factorization.
    exact congrArg
      (fun m ↦
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map m ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1)
      hvcart.symm
  have hstepMapH :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map (v.1 ≫ cart) ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1 =
        ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
            (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map cart) ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1 := by
    -- Apply functoriality on the source side under postcomposition by the chosen component.
    exact congrArg
      (fun m ↦ m ≫ (precomposeForcedFiberHom_chosenComponent G hG τ yT').1) hmapH
  have hstepAssocLeft :
      ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map cart) ≫
        (precomposeForcedFiberHom_chosenComponent G hG τ yT').1 =
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
        ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map cart ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1) := by
    -- Reassociate to expose the cartesian naturality square as an inner composite.
    rw [Category.assoc]
  have hstepCart :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
        ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map cart ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yT').1) =
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
        ((precomposeForcedFiberHom_chosenComponent G hG τ yPull).1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart) := by
    -- Insert the cartesian naturality square for the chosen component.
    exact congrArg
      (fun m ↦
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫ m)
      hcartTotal
  have hstepAssocMiddle :
      (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
        ((precomposeForcedFiberHom_chosenComponent G hG τ yPull).1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart) =
      ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yPull).1) ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart := by
    -- Reassociate again so the vertical naturality square is the leading factor.
    rw [← Category.assoc]
  have hstepVertical :
      ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor H)).map v.1 ≫
          (precomposeForcedFiberHom_chosenComponent G hG τ yPull).1) ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart =
      ((precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map v.1) ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart := by
    -- Insert vertical naturality for the fiber morphism part of the factorization.
    exact congrArg
      (fun m ↦ m ≫ (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart)
      hvert
  have hstepAssocRight :
      ((precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map v.1) ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart =
      (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
        ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map v.1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart) := by
    -- Reassociate the target-side maps so functoriality can combine them.
    rw [Category.assoc]
  have hstepMapK :
      (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
        ((FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map v.1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map cart) =
      (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map (v.1 ≫ cart) := by
    -- Combine the two target-side functor images back into the image of the composite.
    exact congrArg
      (fun m ↦ (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫ m) hmapK.symm
  have hstepEnd :
      (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map (v.1 ≫ cart) =
      (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
        (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map φ := by
    -- Return from the factorized arrow to the original arrow.
    exact congrArg
      (fun m ↦
        (precomposeForcedFiberHom_chosenComponent G hG τ yT).1 ≫
          (FibredCategoryMor.toFunctor (stack_morphism_toFibredCategoryMor K)).map m)
      hvcart
  exact
    hstepStart.trans
      (hstepMapH.trans
        (hstepAssocLeft.trans
          (hstepCart.trans
            (hstepAssocMiddle.trans
              (hstepVertical.trans
                (hstepAssocRight.trans (hstepMapK.trans hstepEnd)))))))

/-- Helper for Chap08 Lemma 8 8 3: precomposition by a stackification morphism is injective on
all `2`-morphism sets into a stack target. -/
private theorem stackificationPrecomposeMapInjective
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (H K : S' ⟶ X) :
    Function.Injective
      ((stackification_precompose_functor X G).map :
        (H ⟶ K) →
          ((stackification_precompose_functor X G).obj H ⟶
            (stackification_precompose_functor X G).obj K)) := by
  intro η θ hηθ
  -- Reduce equality of stack `2`-morphisms to equality of the underlying based natural
  -- transformation at every object of the total source category.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext T
  let U : C := S'.p.obj T
  let y : S'.p.Fiber U := ⟨T, rfl⟩
  let η₀ : stack_morphism_toFibredCategoryMor H ⟶ stack_morphism_toFibredCategoryMor K :=
    ((stackOverSubTwoCategory J).hom S' X).inclusion.map η
  let θ₀ : stack_morphism_toFibredCategoryMor H ⟶ stack_morphism_toFibredCategoryMor K :=
    ((stackOverSubTwoCategory J).hom S' X).inclusion.map θ
  have hFiber :
      basedFiberFunctorHom η₀ U y =
        basedFiberFunctorHom θ₀ U y := by
    -- The local essential-image cover supplied by the stackification lets us test the fiber
    -- component after pullback to source-model objects.
    obtain ⟨Scover, hScover⟩ := hG.locallyEssentiallySurjectiveOnObjects U y
    apply stack_cover_hom_ext (J := J) X Scover
    intro I
    obtain ⟨xI, ⟨cxI⟩⟩ := hScover I
    rw [basedFiberFunctorHom_pullback_bridge η₀ I.f y,
      basedFiberFunctorHom_pullback_bridge θ₀ I.f y,
      basedFiberFunctorHom_transport_of_fiberIso η₀ cxI,
      basedFiberFunctorHom_transport_of_fiberIso θ₀ cxI]
    -- On a `G`-image object the desired component equality is exactly the equality of the
    -- precomposed `2`-morphisms.
    have hImage :
        basedFiberFunctorHom η₀ I.Y ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) =
          basedFiberFunctorHom θ₀ I.Y ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) := by
      apply Functor.Fiber.hom_ext
      have hComp :=
        congrArg
          (fun m =>
            m.hom.hom.toNatTrans.app xI.1)
          hηθ
      exact hComp
    rw [hImage]
  exact congrArg (fun φ ↦ φ.1) hFiber

/-- Helper for Chap08 Lemma 8 8 3: any `2`-morphism after precomposition by a stackification
descends to a `2`-morphism before precomposition. -/
private theorem precomposeForcedFiberHom_gluedBasedNatTrans
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (H K : S' ⟶ X)
    (τ :
      (stackification_precompose_functor X G).obj H ⟶
        (stackification_precompose_functor X G).obj K) :
    ∃ η : H ⟶ K, (stackification_precompose_functor X G).map η = τ := by
  -- Route correction: fullness is packaged from the chosen global forced components. The only
  -- structural input still isolated separately is their total-category naturality, together with
  -- the small wrapper bridge identifying the precomposed component at a source object `T` with
  -- the chosen component at the target fiber object represented by `G.obj T`.
  -- Build the based natural transformation from those components, use the isolated naturality
  -- lemma for the naturality field, and close the precomposition equality componentwise by the
  -- source-object bridge.
  refine ⟨⟨⟨⟨
    { app := fun T =>
        (precomposeForcedFiberHom_chosenComponent G hG τ
          (⟨T, rfl⟩ : S'.p.Fiber (S'.p.obj T))).1
      naturality := by
        intro T T' φ
        exact precomposeForcedFiberHom_chosenComponent_naturality G hG τ φ },
    ?_⟩, trivial⟩, trivial⟩, ?_⟩
  · -- Each chosen component is a vertical fiber morphism, hence satisfies the based-naturality
    -- lift condition required to package it as a based natural transformation.
    intro T
    exact (precomposeForcedFiberHom_chosenComponent G hG τ
      (⟨T, rfl⟩ : S'.p.Fiber (S'.p.obj T))).2
  · -- Compare the precomposed candidate and `τ` by underlying components on every source object.
    repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext T
    -- The functorial precomposition wrapper evaluates the constructed component at `G(T)`;
    -- the source-object bridge identifies this with the original component of `τ`.
    change
      (precomposeForcedFiberHom_chosenComponent G hG τ
          (⟨G.toHom.obj T, rfl⟩ : S'.p.Fiber (S'.p.obj (G.toHom.obj T)))).1 =
        τ.hom.hom.app T
    exact precomposeForcedFiberHom_chosenComponent_source_app G hG τ T

/-- Helper for Chap08 Lemma 8 8 3: precomposition by a stackification morphism is bijective on
all `2`-morphism sets into a stack target. -/
theorem stackification_precompose_map_bijective
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (H K : S' ⟶ X) :
    Function.Bijective
      ((stackification_precompose_functor X G).map :
        (H ⟶ K) →
          ((stackification_precompose_functor X G).obj H ⟶
            (stackification_precompose_functor X G).obj K)) := by
  constructor
  · -- Faithfulness is now separated: coverwise extensionality reduces to source-image components.
    exact stackificationPrecomposeMapInjective X G hG H K
  · -- Fullness is isolated in the Hom-descent helper; this wrapper only repackages the witness as
    -- ordinary surjectivity of the functorial Hom map.
    intro τ
    exact precomposeForcedFiberHom_gluedBasedNatTrans X G hG H K τ

/-- Helper for Chap08 Lemma 8 8 3: the owner-level precomposition functor is essentially
surjective once every stack morphism out of `S` has a descended lift along the item-local
precomposition functor. -/
theorem local_stackification_precompose_functor_essSurj_of_lift
    (X : StackOver J)
    (G : S ⟶ S')
    (hLift :
      ∀ F : S ⟶ X,
        ∃ H : S' ⟶ X, Nonempty ((stackification_precompose_functor X G).obj H ≅ F)) :
    (local_stackification_precompose_functor (J := J) (G := G) :
      (S' ⟶ X) ⥤ (S ⟶ X)).EssSurj := by
  -- Convert the concrete lift witness for the item-local precomposition functor into the
  -- canonical `Functor.EssSurj` API for the owner spelling.
  constructor
  intro F
  obtain ⟨H, hH⟩ := hLift F
  refine ⟨H, ?_⟩
  simpa [stackification_precompose_functor_eq_local X G] using hH

/-- Helper for Chap08 Lemma 8 8 3: the stackification Hom-presheaf map has a unique extension
to the Hom presheaf of a fixed stack-valued source morphism. -/
private theorem stackificationLiftHomExtension_existsUnique
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x y : S.p.Fiber U) :
    ∃! e :
      ((canonicalFiberPseudofunctor S'.p).presheafHom
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        ((FibredCategoryMor.fiberFunctor G U).obj y)) ⟶
      ((canonicalFiberPseudofunctor X.p).presheafHom
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)),
      FibredCategoryMor.fibredMorphismPresheafMap G x y ≫ e =
        FibredCategoryMor.fibredMorphismPresheafMap F x y := by
  -- The target Hom presheaf is a sheaf because `X` is a stack, so precomposition by the
  -- `W`-morphism supplied by `hG` is bijective.
  let sourceMap := FibredCategoryMor.fibredMorphismPresheafMap G x y
  let targetMap := FibredCategoryMor.fibredMorphismPresheafMap F x y
  have hSheaf :
      Presheaf.IsSheaf (J.over U)
        ((canonicalFiberPseudofunctor X.p).presheafHom
          ((FibredCategoryMor.fiberFunctor F U).obj x)
          ((FibredCategoryMor.fiberFunctor F U).obj y)) :=
    Pseudofunctor.IsPrestack.isSheaf
      (F := canonicalFiberPseudofunctor X.p) (J := J) (S := U)
      ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y)
  have hBij := W_precomp_bijective_to_sheaf (J := J.over U)
    sourceMap (hG.morphismPresheafMap_W U x y) hSheaf
  obtain ⟨e, he⟩ := hBij.2 targetMap
  refine ⟨e, he, ?_⟩
  intro e' he'
  -- Uniqueness is exactly injectivity of precomposition by the same `W`-morphism.
  exact hBij.1 (he'.trans he.symm)

/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom extension attached to a stack-valued source
morphism. -/
noncomputable def stackificationLiftHomExtension
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x y : S.p.Fiber U) :
      ((canonicalFiberPseudofunctor S'.p).presheafHom
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        ((FibredCategoryMor.fiberFunctor G U).obj y)) ⟶
      ((canonicalFiberPseudofunctor X.p).presheafHom
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)) :=
  Classical.choose (stackificationLiftHomExtension_existsUnique X G hG F x y)

/-- Helper for Chap08 Lemma 8 8 3: precomposing the canonical Hom extension with the
stackification Hom map recovers the Hom map of the fixed source morphism. -/
private theorem stackificationLiftHomExtension_comp
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x y : S.p.Fiber U) :
    FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
        stackificationLiftHomExtension X G hG F x y =
      FibredCategoryMor.fibredMorphismPresheafMap F x y :=
  (Classical.choose_spec (stackificationLiftHomExtension_existsUnique X G hG F x y)).1

/-- Helper for Chap08 Lemma 8 8 3: any Hom-presheaf map with the defining precomposition
property is the canonical Hom extension. -/
private theorem stackificationLiftHomExtension_ext
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x y : S.p.Fiber U)
    (e :
      ((canonicalFiberPseudofunctor S'.p).presheafHom
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        ((FibredCategoryMor.fiberFunctor G U).obj y)) ⟶
      ((canonicalFiberPseudofunctor X.p).presheafHom
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)))
    (he :
      FibredCategoryMor.fibredMorphismPresheafMap G x y ≫ e =
        FibredCategoryMor.fibredMorphismPresheafMap F x y) :
    e = stackificationLiftHomExtension X G hG F x y := by
  -- Read uniqueness from the chosen `ExistsUnique` witness.
  exact
    (Classical.choose_spec
      (stackificationLiftHomExtension_existsUnique X G hG F x y)).2 e he

/-- Helper for Chap08 Lemma 8 8 3: evaluating the canonical Hom-presheaf extension at the
identity slice gives an actual fiber morphism in the stack target. -/
noncomputable def stackificationLiftHomExtensionFiberMap
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x y : S.p.Fiber U)
    (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y)) :
    ((FibredCategoryMor.fiberFunctor F U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor F U).obj y) :=
  ((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
    (M := (FibredCategoryMor.fiberFunctor F U).obj x)
    (N := (FibredCategoryMor.fiberFunctor F U).obj y)).symm
    ((stackificationLiftHomExtension X G hG F x y).app (op (Over.mk (𝟙 U)))
      ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
        (M := (FibredCategoryMor.fiberFunctor G U).obj x)
        (N := (FibredCategoryMor.fiberFunctor G U).obj y) α))

/-- Helper for Chap08 Lemma 8 8 3: on a literal `G`-image fiber morphism, the canonical Hom
extension agrees with the fixed source morphism `F`. -/
private theorem stackificationLiftHomExtension_on_image
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y : S.p.Fiber U} (φ : x ⟶ y) :
    (stackificationLiftHomExtension X G hG F x y).app (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
          ((FibredCategoryMor.fiberFunctor G U).map φ)) =
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
        ((FibredCategoryMor.fiberFunctor F U).map φ) := by
  -- Evaluate the defining extension equation on the identity slice object and use the existing
  -- identity-slice computation for `fibredMorphismPresheafMap`.
  have hComp := congrArg
    (fun η => η.app (op (Over.mk (𝟙 U)))
      ((canonicalFiberPseudofunctor S.p).presheafHomObjHomEquiv φ))
    (stackificationLiftHomExtension_comp X G hG F x y)
  simpa only [NatTrans.comp_app, types_comp_apply, fibredMorphismPresheafMap_app_id_local]
    using hComp

/-- Helper for Chap08 Lemma 8 8 3: the fiber-level Hom-extension evaluation agrees with `F` on
literal source-image morphisms. -/
theorem stackificationLiftHomExtensionFiberMap_on_image
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y : S.p.Fiber U} (φ : x ⟶ y) :
    stackificationLiftHomExtensionFiberMap X G hG F x y
        ((FibredCategoryMor.fiberFunctor G U).map φ) =
      (FibredCategoryMor.fiberFunctor F U).map φ := by
  -- Apply the identity-slice equivalence to reduce the fiber statement to the presheaf-level
  -- source-image formula proved above.
  let e :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj y)
  change e.symm
      ((stackificationLiftHomExtension X G hG F x y).app (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
          ((FibredCategoryMor.fiberFunctor G U).map φ))) =
    (FibredCategoryMor.fiberFunctor F U).map φ
  exact e.symm_apply_eq.2 (stackificationLiftHomExtension_on_image X G hG F φ)

/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom extension sends identity morphisms on
literal `G`-image objects to identity morphisms under `F`. -/
private theorem stackificationLiftHomExtension_id
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U) :
    (stackificationLiftHomExtension X G hG F x x).app (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
          (𝟙 ((FibredCategoryMor.fiberFunctor G U).obj x))) =
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
        (𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
  -- This is the image formula specialized to the identity in the source fiber.
  simpa only [Functor.map_id] using
    stackificationLiftHomExtension_on_image X G hG F (𝟙 x)

/-- Helper for Chap08 Lemma 8 8 3: the fiber-level Hom-extension evaluation sends identities on
literal `G`-image objects to identities under `F`. -/
theorem stackificationLiftHomExtensionFiberMap_id
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U) :
    stackificationLiftHomExtensionFiberMap X G hG F x x
        (𝟙 ((FibredCategoryMor.fiberFunctor G U).obj x)) =
      𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x) := by
  -- Identity preservation is the source-image formula applied to the identity morphism.
  simpa only [Functor.map_id] using
    stackificationLiftHomExtensionFiberMap_on_image X G hG F (𝟙 x)

/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom extension commutes with postcomposition
by a literal source-image morphism. -/
private theorem stackificationLiftHomExtension_postcomp_image
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y z : S.p.Fiber U} (ψ : y ⟶ z) :
    stackificationLiftHomExtension X G hG F x y ≫
        presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor F U).map ψ) =
      presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor G U).map ψ) ≫
        stackificationLiftHomExtension X G hG F x z := by
  apply W_precomp_ext_to_sheaf (J := J.over U)
    (FibredCategoryMor.fibredMorphismPresheafMap G x y)
    (hG.morphismPresheafMap_W U x y)
  · exact
      Pseudofunctor.IsPrestack.isSheaf
        (F := canonicalFiberPseudofunctor X.p) (J := J) (S := U)
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj z)
  · calc
      FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
          (stackificationLiftHomExtension X G hG F x y ≫
            presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor F U).map ψ)) =
        (FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
            stackificationLiftHomExtension X G hG F x y) ≫
          presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor F U).map ψ) := by
          rw [Category.assoc]
      _ =
        FibredCategoryMor.fibredMorphismPresheafMap F x y ≫
          presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor F U).map ψ) := by
          rw [stackificationLiftHomExtension_comp]
      _ =
        presheafHomPostcompMap ψ ≫
          FibredCategoryMor.fibredMorphismPresheafMap F x z := by
          exact fibredMorphismPresheafMap_postcomp F ψ
      _ =
        presheafHomPostcompMap ψ ≫
          (FibredCategoryMor.fibredMorphismPresheafMap G x z ≫
            stackificationLiftHomExtension X G hG F x z) := by
          rw [stackificationLiftHomExtension_comp]
      _ =
        (presheafHomPostcompMap ψ ≫
          FibredCategoryMor.fibredMorphismPresheafMap G x z) ≫
            stackificationLiftHomExtension X G hG F x z := by
          rw [Category.assoc]
      _ =
        (FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
          presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor G U).map ψ)) ≫
            stackificationLiftHomExtension X G hG F x z := by
          rw [fibredMorphismPresheafMap_postcomp G ψ]
      _ =
        FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
          (presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor G U).map ψ) ≫
            stackificationLiftHomExtension X G hG F x z) := by
          rw [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the fiber-level Hom extension commutes with
postcomposition by a literal source-image morphism. -/
private theorem stackificationLiftHomExtensionFiberMap_postcomp_image
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y z : S.p.Fiber U}
    (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y))
    (ψ : y ⟶ z) :
    stackificationLiftHomExtensionFiberMap X G hG F x z
        (α ≫ (FibredCategoryMor.fiberFunctor G U).map ψ) =
      stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
        (FibredCategoryMor.fiberFunctor F U).map ψ := by
  let eXY :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj y)
  let eXZ :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj z)
  let sXY :=
    (canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor G U).obj x)
      (N := (FibredCategoryMor.fiberFunctor G U).obj y)
  have hEval :=
    congrArg
      (fun η => η.app (op (Over.mk (𝟙 U))) (sXY α))
      (stackificationLiftHomExtension_postcomp_image X G hG F ψ)
  have hLeft :
      (stackificationLiftHomExtension X G hG F x y ≫
          presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor F U).map ψ)).app
          (op (Over.mk (𝟙 U))) (sXY α) =
        eXZ (stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          (FibredCategoryMor.fiberFunctor F U).map ψ) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    have hα :
        (stackificationLiftHomExtension X G hG F x y).app (op (Over.mk (𝟙 U))) (sXY α) =
          eXY (stackificationLiftHomExtensionFiberMap X G hG F x y α) := by
      dsimp only [stackificationLiftHomExtensionFiberMap]
      exact (eXY.apply_symm_apply _).symm
    rw [hα]
    exact
      presheafHomPostcompMap_app_id
        (F := canonicalFiberPseudofunctor X.p)
        ((FibredCategoryMor.fiberFunctor F U).map ψ)
        (stackificationLiftHomExtensionFiberMap X G hG F x y α)
  have hRight :
      (presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor G U).map ψ) ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sXY α) =
        eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z
          (α ≫ (FibredCategoryMor.fiberFunctor G U).map ψ)) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    rw [presheafHomPostcompMap_app_id (F := canonicalFiberPseudofunctor S'.p)]
    dsimp only [stackificationLiftHomExtensionFiberMap]
    exact (eXZ.apply_symm_apply _).symm
  apply eXZ.injective
  calc
    eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z
        (α ≫ (FibredCategoryMor.fiberFunctor G U).map ψ)) =
      (presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor G U).map ψ) ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sXY α) := hRight.symm
    _ =
      (stackificationLiftHomExtension X G hG F x y ≫
          presheafHomPostcompMap ((FibredCategoryMor.fiberFunctor F U).map ψ)).app
          (op (Over.mk (𝟙 U))) (sXY α) := hEval.symm
    _ =
      eXZ (stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          (FibredCategoryMor.fiberFunctor F U).map ψ) := hLeft

/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom extension commutes with precomposition
by a literal source-image morphism. -/
private theorem stackificationLiftHomExtension_precomp_image
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y z : S.p.Fiber U} (φ : x ⟶ y) :
    stackificationLiftHomExtension X G hG F y z ≫
        presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor F U).map φ) =
      presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor G U).map φ) ≫
        stackificationLiftHomExtension X G hG F x z := by
  apply W_precomp_ext_to_sheaf (J := J.over U)
    (FibredCategoryMor.fibredMorphismPresheafMap G y z)
    (hG.morphismPresheafMap_W U y z)
  · exact
      Pseudofunctor.IsPrestack.isSheaf
        (F := canonicalFiberPseudofunctor X.p) (J := J) (S := U)
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj z)
  · calc
      FibredCategoryMor.fibredMorphismPresheafMap G y z ≫
          (stackificationLiftHomExtension X G hG F y z ≫
            presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor F U).map φ)) =
        (FibredCategoryMor.fibredMorphismPresheafMap G y z ≫
            stackificationLiftHomExtension X G hG F y z) ≫
          presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor F U).map φ) := by
          rw [Category.assoc]
      _ =
        FibredCategoryMor.fibredMorphismPresheafMap F y z ≫
          presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor F U).map φ) := by
          rw [stackificationLiftHomExtension_comp]
      _ =
        presheafHomPrecompMap φ ≫
          FibredCategoryMor.fibredMorphismPresheafMap F x z := by
          exact fibredMorphismPresheafMap_precomp F φ
      _ =
        presheafHomPrecompMap φ ≫
          (FibredCategoryMor.fibredMorphismPresheafMap G x z ≫
            stackificationLiftHomExtension X G hG F x z) := by
          rw [stackificationLiftHomExtension_comp]
      _ =
        (presheafHomPrecompMap φ ≫
          FibredCategoryMor.fibredMorphismPresheafMap G x z) ≫
            stackificationLiftHomExtension X G hG F x z := by
          rw [Category.assoc]
      _ =
        (FibredCategoryMor.fibredMorphismPresheafMap G y z ≫
          presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor G U).map φ)) ≫
            stackificationLiftHomExtension X G hG F x z := by
          rw [fibredMorphismPresheafMap_precomp G φ]
      _ =
        FibredCategoryMor.fibredMorphismPresheafMap G y z ≫
          (presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor G U).map φ) ≫
            stackificationLiftHomExtension X G hG F x z) := by
          rw [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the fiber-level Hom extension commutes with
precomposition by a literal source-image morphism. -/
private theorem stackificationLiftHomExtensionFiberMap_precomp_image
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y z : S.p.Fiber U}
    (φ : x ⟶ y)
    (β : ((FibredCategoryMor.fiberFunctor G U).obj y) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj z)) :
    stackificationLiftHomExtensionFiberMap X G hG F x z
        ((FibredCategoryMor.fiberFunctor G U).map φ ≫ β) =
      (FibredCategoryMor.fiberFunctor F U).map φ ≫
        stackificationLiftHomExtensionFiberMap X G hG F y z β := by
  let eYZ :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj y)
      (N := (FibredCategoryMor.fiberFunctor F U).obj z)
  let eXZ :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj z)
  let sYZ :=
    (canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor G U).obj y)
      (N := (FibredCategoryMor.fiberFunctor G U).obj z)
  have hEval :=
    congrArg
      (fun η => η.app (op (Over.mk (𝟙 U))) (sYZ β))
      (stackificationLiftHomExtension_precomp_image X G hG F φ)
  have hLeft :
      (stackificationLiftHomExtension X G hG F y z ≫
          presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor F U).map φ)).app
          (op (Over.mk (𝟙 U))) (sYZ β) =
        eXZ ((FibredCategoryMor.fiberFunctor F U).map φ ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    have hβ :
        (stackificationLiftHomExtension X G hG F y z).app (op (Over.mk (𝟙 U))) (sYZ β) =
          eYZ (stackificationLiftHomExtensionFiberMap X G hG F y z β) := by
      dsimp only [stackificationLiftHomExtensionFiberMap]
      exact (eYZ.apply_symm_apply _).symm
    rw [hβ]
    exact
      presheafHomPrecompMap_app_id
        (F := canonicalFiberPseudofunctor X.p)
        ((FibredCategoryMor.fiberFunctor F U).map φ)
        (stackificationLiftHomExtensionFiberMap X G hG F y z β)
  have hRight :
      (presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor G U).map φ) ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sYZ β) =
        eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z
          ((FibredCategoryMor.fiberFunctor G U).map φ ≫ β)) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    rw [presheafHomPrecompMap_app_id (F := canonicalFiberPseudofunctor S'.p)]
    dsimp only [stackificationLiftHomExtensionFiberMap]
    exact (eXZ.apply_symm_apply _).symm
  apply eXZ.injective
  calc
    eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z
        ((FibredCategoryMor.fiberFunctor G U).map φ ≫ β)) =
      (presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor G U).map φ) ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sYZ β) := hRight.symm
    _ =
      (stackificationLiftHomExtension X G hG F y z ≫
          presheafHomPrecompMap ((FibredCategoryMor.fiberFunctor F U).map φ)).app
          (op (Over.mk (𝟙 U))) (sYZ β) := hEval.symm
    _ =
      eXZ ((FibredCategoryMor.fiberFunctor F U).map φ ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β) := hLeft

/-- Helper for Chap08 Lemma 8 8 3: arbitrary precomposition compatibility of the Hom extension
implies that the fiber-level Hom-extension evaluation preserves composition. -/
theorem stackificationLiftHomExtensionFiberMap_comp_of_precomp_arbitrary
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (hprecomp :
      ∀ ⦃U : C⦄ ⦃x y z : S.p.Fiber U⦄
        (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
          ((FibredCategoryMor.fiberFunctor G U).obj y)),
        stackificationLiftHomExtension X G hG F y z ≫
            presheafHomPrecompMap
              (stackificationLiftHomExtensionFiberMap X G hG F x y α) =
          presheafHomPrecompMap α ≫
            stackificationLiftHomExtension X G hG F x z) :
    ∀ ⦃U : C⦄ ⦃x y z : S.p.Fiber U⦄
      (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
        ((FibredCategoryMor.fiberFunctor G U).obj y))
      (β : ((FibredCategoryMor.fiberFunctor G U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor G U).obj z)),
      stackificationLiftHomExtensionFiberMap X G hG F x z (α ≫ β) =
        stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β := by
  intro U x y z α β
  -- Evaluate the presheaf-level naturality law at the identity slice and translate both sides
  -- through the identity-slice Hom equivalence.
  let eYZ :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj y)
      (N := (FibredCategoryMor.fiberFunctor F U).obj z)
  let eXZ :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj z)
  let sYZ :=
    (canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor G U).obj y)
      (N := (FibredCategoryMor.fiberFunctor G U).obj z)
  have hEval :=
    congrArg
      (fun η => η.app (op (Over.mk (𝟙 U))) (sYZ β))
      (hprecomp (U := U) (x := x) (y := y) (z := z) α)
  have hLeft :
      (stackificationLiftHomExtension X G hG F y z ≫
          presheafHomPrecompMap
            (stackificationLiftHomExtensionFiberMap X G hG F x y α)).app
          (op (Over.mk (𝟙 U))) (sYZ β) =
        eXZ (stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    have hβ :
        (stackificationLiftHomExtension X G hG F y z).app (op (Over.mk (𝟙 U))) (sYZ β) =
          eYZ (stackificationLiftHomExtensionFiberMap X G hG F y z β) := by
      dsimp only [stackificationLiftHomExtensionFiberMap]
      exact (eYZ.apply_symm_apply _).symm
    rw [hβ]
    exact
      presheafHomPrecompMap_app_id
        (F := canonicalFiberPseudofunctor X.p)
        (stackificationLiftHomExtensionFiberMap X G hG F x y α)
        (stackificationLiftHomExtensionFiberMap X G hG F y z β)
  have hRight :
      (presheafHomPrecompMap α ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sYZ β) =
        eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z (α ≫ β)) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    rw [presheafHomPrecompMap_app_id (F := canonicalFiberPseudofunctor S'.p)]
    dsimp only [stackificationLiftHomExtensionFiberMap]
    exact (eXZ.apply_symm_apply _).symm
  apply eXZ.injective
  calc
    eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z (α ≫ β)) =
      (presheafHomPrecompMap α ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sYZ β) := hRight.symm
    _ =
      (stackificationLiftHomExtension X G hG F y z ≫
          presheafHomPrecompMap
            (stackificationLiftHomExtensionFiberMap X G hG F x y α)).app
          (op (Over.mk (𝟙 U))) (sYZ β) := hEval.symm
    _ =
      eXZ (stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β) := hLeft

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the identity-slice Hom restriction, normalized with
`Over.mk f` rather than `Over.mk (f ≫ 𝟙 _)`. -/
private theorem identitySlicePresheafHom_map_hom_clean
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g (by change g ≫ 𝟙 W = g; rw [Category.comp_id]) :
          Over.mk g ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫
          φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  rw [hmid]
  rw [(canonicalFiberPseudofunctor p).mapComp'_naturality_2]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: evaluating the canonical Hom extension on a slice
restriction of a target-side fiber morphism is the pullback of its identity-slice value. -/
theorem stackificationLiftHomExtensionFiberMap_pullback
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) {x y : S.p.Fiber U}
    (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y)) :
    (stackificationLiftHomExtension X G hG F x y).app (op (Over.mk f))
        (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α) =
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftHomExtensionFiberMap X G hG F x y α) := by
  let η := stackificationLiftHomExtension X G hG F x y
  let srcEq :=
    (canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor G U).obj x)
      (N := (FibredCategoryMor.fiberFunctor G U).obj y)
  let tgtEq :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj y)
  let slice : (Over U) := Over.mk f
  let sliceHom : slice ⟶ Over.mk (𝟙 U) :=
    Over.homMk f (by dsimp [slice]; rw [Category.comp_id])
  have hη_id :
      η.app (op (Over.mk (𝟙 U))) (srcEq α) =
        tgtEq (stackificationLiftHomExtensionFiberMap X G hG F x y α) := by
    dsimp only [stackificationLiftHomExtensionFiberMap]
    exact (tgtEq.apply_symm_apply _).symm
  have hnat :
      η.app (op slice)
          (((canonicalFiberPseudofunctor S'.p).presheafHom
            ((FibredCategoryMor.fiberFunctor G U).obj x)
            ((FibredCategoryMor.fiberFunctor G U).obj y)).map
              sliceHom.op (srcEq α)) =
        (((canonicalFiberPseudofunctor X.p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y)).map
              sliceHom.op
              (η.app (op (Over.mk (𝟙 U))) (srcEq α))) := by
    simpa only [NatTrans.naturality, types_comp_apply] using
      congrArg (fun m => m (srcEq α))
        (η.naturality sliceHom.op)
  have hsrc :
      (((canonicalFiberPseudofunctor S'.p).presheafHom
            ((FibredCategoryMor.fiberFunctor G U).obj x)
            ((FibredCategoryMor.fiberFunctor G U).obj y)).map
          sliceHom.op (srcEq α)) =
        ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α := by
    simpa [slice, sliceHom] using
      identitySlicePresheafHom_map_hom_clean S'.p f
      ((FibredCategoryMor.fiberFunctor G U).obj x)
      ((FibredCategoryMor.fiberFunctor G U).obj y) α
  have htgt :
      (((canonicalFiberPseudofunctor X.p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y)).map
          sliceHom.op
          (tgtEq (stackificationLiftHomExtensionFiberMap X G hG F x y α))) =
        ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftHomExtensionFiberMap X G hG F x y α) := by
    simpa [slice, sliceHom] using
      identitySlicePresheafHom_map_hom_clean X.p f
      ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y)
      (stackificationLiftHomExtensionFiberMap X G hG F x y α)
  calc
    η.app (op (Over.mk f))
        (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α)
        = η.app (op slice)
            (((canonicalFiberPseudofunctor S'.p).presheafHom
              ((FibredCategoryMor.fiberFunctor G U).obj x)
              ((FibredCategoryMor.fiberFunctor G U).obj y)).map
                sliceHom.op (srcEq α)) := by
            rw [hsrc]
    _ = (((canonicalFiberPseudofunctor X.p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y)).map
              sliceHom.op
              (η.app (op (Over.mk (𝟙 U))) (srcEq α))) := hnat
    _ = (((canonicalFiberPseudofunctor X.p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y)).map
              sliceHom.op
              (tgtEq (stackificationLiftHomExtensionFiberMap X G hG F x y α))) := by
            rw [hη_id]
    _ = ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftHomExtensionFiberMap X G hG F x y α) := htgt

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the hom component of the canonical Hom-presheaf
base-change comparison is precomposition by the inverse `mapComp'` component and
postcomposition by the hom component. -/
private theorem canonicalOverMapCompPresheafHomIso_hom_app
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U Z : C} {x y : p.Fiber U}
    (q : Z ⟶ U) (W : (Over Z)ᵒᵖ)
    (α : ((canonicalFiberPseudofunctor p).presheafHom x y).obj
      (op ((Over.map q).obj W.unop))) :
    (((canonicalFiberPseudofunctor p).overMapCompPresheafHomIso x y q).hom.app W) α =
      ((canonicalFiberPseudofunctor p).mapComp'
          q.op.toLoc W.unop.hom.op.toLoc
          (q.op.toLoc ≫ W.unop.hom.op.toLoc) rfl).inv.toNatTrans.app x ≫
        α ≫
      ((canonicalFiberPseudofunctor p).mapComp'
          q.op.toLoc W.unop.hom.op.toLoc
          (q.op.toLoc ≫ W.unop.hom.op.toLoc) rfl).hom.toNatTrans.app y := by
  let κ := (canonicalFiberPseudofunctor p).mapComp'
    q.op.toLoc W.unop.hom.op.toLoc (q.op.toLoc ≫ W.unop.hom.op.toLoc) rfl
  dsimp [Pseudofunctor.overMapCompPresheafHomIso, Iso.homFromEquiv, Iso.homToEquiv,
    Equiv.trans]
  change ((fun f ↦ f ≫ κ.hom.toNatTrans.app y)
      ((fun f ↦ κ.inv.toNatTrans.app x ≫ f) α)) =
    κ.inv.toNatTrans.app x ≫ α ≫ κ.hom.toNatTrans.app y
  beta_reduce
  rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the inverse component of the canonical Hom-presheaf
base-change comparison is precomposition by the hom `mapComp'` component and postcomposition by
the inverse component. -/
private theorem canonicalOverMapCompPresheafHomIso_inv_app
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U Z : C} {x y : p.Fiber U}
    (q : Z ⟶ U) (W : (Over Z)ᵒᵖ)
    (α : ((canonicalFiberPseudofunctor p).presheafHom
      (((canonicalFiberPseudofunctor p).map q.op.toLoc).toFunctor.obj x)
      (((canonicalFiberPseudofunctor p).map q.op.toLoc).toFunctor.obj y)).obj W) :
    (((canonicalFiberPseudofunctor p).overMapCompPresheafHomIso x y q).inv.app W) α =
      ((canonicalFiberPseudofunctor p).mapComp'
          q.op.toLoc W.unop.hom.op.toLoc
          (q.op.toLoc ≫ W.unop.hom.op.toLoc) rfl).hom.toNatTrans.app x ≫
        α ≫
      ((canonicalFiberPseudofunctor p).mapComp'
          q.op.toLoc W.unop.hom.op.toLoc
          (q.op.toLoc ≫ W.unop.hom.op.toLoc) rfl).inv.toNatTrans.app y := by
  let κ := (canonicalFiberPseudofunctor p).mapComp'
    q.op.toLoc W.unop.hom.op.toLoc (q.op.toLoc ≫ W.unop.hom.op.toLoc) rfl
  dsimp [Pseudofunctor.overMapCompPresheafHomIso, Iso.homFromEquiv, Iso.homToEquiv,
    Equiv.trans]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the Hom-presheaf map induced by a fibred morphism commutes
with restriction to a slice, after inserting the canonical pullback-comparison transports. -/
private theorem fibredMorphismPresheafMap_pullbackComparison_baseChange
    {Y Z : FibredCategoryOver.{u, v, uS, vS} C}
    (F : Y ⟶ Z)
    {U V : C} (f : V ⟶ U) {x y : Y.p.Fiber U} :
    FibredCategoryMor.fibredMorphismPresheafMap F
        (f ^*[canonicalPullbackChoice Y.p] x)
        (f ^*[canonicalPullbackChoice Y.p] y) ≫
      (fiberHomPresheafIso
        (FibredCategoryMor.pullbackComparison F f x).symm
        (FibredCategoryMor.pullbackComparison F f y).symm).hom ≫
      ((canonicalFiberPseudofunctor Z.p).overMapCompPresheafHomIso
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y) f).inv =
    ((canonicalFiberPseudofunctor Y.p).overMapCompPresheafHomIso x y f).inv ≫
      Functor.whiskerLeft (Over.map f).op
        (FibredCategoryMor.fibredMorphismPresheafMap F x y) := by
  ext W δ
  let k : W.unop.left ⟶ V := W.unop.hom
  let b : W.unop.left ⟶ U := k ≫ f
  let FYk := ((canonicalFiberPseudofunctor Z.p).map k.op.toLoc).toFunctor
  let FYb := FibredCategoryMor.fiberFunctor F W.unop.left
  let e₁ := FibredCategoryMor.pullbackComparison F f x
  let e₂ := FibredCategoryMor.pullbackComparison F f y
  let ck₁ := FibredCategoryMor.pullbackComparison F k
    (f ^*[canonicalPullbackChoice Y.p] x)
  let ck₂ := FibredCategoryMor.pullbackComparison F k
    (f ^*[canonicalPullbackChoice Y.p] y)
  let eb₁ := FibredCategoryMor.pullbackComparison F b x
  let eb₂ := FibredCategoryMor.pullbackComparison F b y
  let leftTarget :=
    ((canonicalFiberPseudofunctor Z.p).mapComp' f.op.toLoc k.op.toLoc
      (f.op.toLoc ≫ k.op.toLoc) rfl).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor F U).obj x)
  let rightTarget :=
    ((canonicalFiberPseudofunctor Z.p).mapComp' f.op.toLoc k.op.toLoc
      (f.op.toLoc ≫ k.op.toLoc) rfl).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor F U).obj y)
  let leftSource :=
    ((canonicalFiberPseudofunctor Y.p).mapComp' f.op.toLoc k.op.toLoc
      (f.op.toLoc ≫ k.op.toLoc) rfl).hom.toNatTrans.app x
  let rightSource :=
    ((canonicalFiberPseudofunctor Y.p).mapComp' f.op.toLoc k.op.toLoc
      (f.op.toLoc ≫ k.op.toLoc) rfl).inv.toNatTrans.app y
  simp only [NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app, types_comp_apply,
    fiberHomPresheafIso, NatIso.ofComponents_hom_app, Equiv.toIso_hom,
    canonicalOverMapCompPresheafHomIso_inv_app]
  have hsourceApp :
      (FibredCategoryMor.fibredMorphismPresheafMap F
          (f ^*[canonicalPullbackChoice Y.p] x)
          (f ^*[canonicalPullbackChoice Y.p] y)).app W δ =
        ck₁.hom ≫ FYb.map δ ≫ ck₂.inv := by
    rfl
  have htargetApp :
      (FibredCategoryMor.fibredMorphismPresheafMap F x y).app ((Over.map f).op.obj W)
          (leftSource ≫ δ ≫ rightSource) =
        eb₁.hom ≫ FYb.map (leftSource ≫ δ ≫ rightSource) ≫ eb₂.inv := by
    rfl
  rw [hsourceApp, htargetApp]
  change
    leftTarget ≫
        (((FYk.mapIso e₁.symm).homCongr (FYk.mapIso e₂.symm))
          (ck₁.hom ≫ FYb.map δ ≫ ck₂.inv)) ≫ rightTarget =
      eb₁.hom ≫ FYb.map (leftSource ≫ δ ≫ rightSource) ≫ eb₂.inv
  have hconj :
      (((FYk.mapIso e₁.symm).homCongr (FYk.mapIso e₂.symm))
          (ck₁.hom ≫ FYb.map δ ≫ ck₂.inv)) =
        FYk.map e₁.hom ≫ (ck₁.hom ≫ FYb.map δ ≫ ck₂.inv) ≫
          FYk.map e₂.inv := by
    rfl
  rw [hconj]
  simp only [Category.assoc]
  have hleft :
      leftTarget ≫ FYk.map e₁.hom ≫ ck₁.hom =
        eb₁.hom ≫ FYb.map leftSource := by
    simpa only [leftTarget, FYk, FYb, e₁, ck₁, eb₁, leftSource, b] using
      pullbackComparison_mapComp_hom_cocycle F f k b rfl x
  have hright :
      ck₂.inv ≫ FYk.map e₂.inv ≫ rightTarget =
        FYb.map rightSource ≫ eb₂.inv := by
    simpa only [rightTarget, FYk, FYb, e₂, ck₂, eb₂, rightSource, b] using
      pullbackComparison_mapComp_inv_cocycle F f k b rfl y
  have hmap :
      FYb.map (leftSource ≫ δ ≫ rightSource) =
        FYb.map leftSource ≫ FYb.map δ ≫ FYb.map rightSource := by
    simpa only [Category.assoc] using
      functor_map_threefold_comp FYb leftSource δ rightSource
  calc
    leftTarget ≫ FYk.map e₁.hom ≫ ck₁.hom ≫ FYb.map δ ≫ ck₂.inv ≫
        FYk.map e₂.inv ≫ rightTarget =
      (leftTarget ≫ FYk.map e₁.hom ≫ ck₁.hom) ≫ FYb.map δ ≫
        (ck₂.inv ≫ FYk.map e₂.inv ≫ rightTarget) := by
        simp only [Category.assoc]
    _ = (eb₁.hom ≫ FYb.map leftSource) ≫ FYb.map δ ≫
        (FYb.map rightSource ≫ eb₂.inv) := by
        rw [hleft, hright]
    _ = eb₁.hom ≫ (FYb.map leftSource ≫ FYb.map δ ≫ FYb.map rightSource) ≫
        eb₂.inv := by
        simp only [Category.assoc]
    _ = eb₁.hom ≫ FYb.map (leftSource ≫ δ ≫ rightSource) ≫ eb₂.inv := by
        rw [hmap]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: if a target-side fiber morphism becomes a literal
`G`-image after pullback, then its Hom-extension value pulls back to the corresponding literal
`F`-image. -/
theorem stackificationLiftHomExtensionFiberMap_pullback_of_image
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) {x y : S.p.Fiber U}
    (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y))
    (γ : (f ^*[canonicalPullbackChoice S.p] x) ⟶
      (f ^*[canonicalPullbackChoice S.p] y))
    (hγ :
      (FibredCategoryMor.fiberFunctor G V).map γ =
        (FibredCategoryMor.pullbackComparison G f x).inv ≫
          ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α ≫
          (FibredCategoryMor.pullbackComparison G f y).hom) :
    ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftHomExtensionFiberMap X G hG F x y α) =
      (FibredCategoryMor.pullbackComparison F f x).hom ≫
        (FibredCategoryMor.fiberFunctor F V).map γ ≫
        (FibredCategoryMor.pullbackComparison F f y).inv := by
  let η := stackificationLiftHomExtension X G hG F x y
  let srcEq :=
    (canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor G U).obj x)
      (N := (FibredCategoryMor.fiberFunctor G U).obj y)
  let tgtEq :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj y)
  let tgtEqV :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor F U).obj x))
      (N := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor F U).obj y))
  let slice : (Over U) := Over.mk f
  let sliceHom : slice ⟶ Over.mk (𝟙 U) :=
    Over.homMk f (by dsimp [slice]; rw [Category.comp_id])
  have hη_id :
      η.app (op (Over.mk (𝟙 U))) (srcEq α) =
        tgtEq (stackificationLiftHomExtensionFiberMap X G hG F x y α) := by
    dsimp only [stackificationLiftHomExtensionFiberMap]
    exact (tgtEq.apply_symm_apply _).symm
  have hnat :
      η.app (op slice)
          (((canonicalFiberPseudofunctor S'.p).presheafHom
            ((FibredCategoryMor.fiberFunctor G U).obj x)
            ((FibredCategoryMor.fiberFunctor G U).obj y)).map
              sliceHom.op (srcEq α)) =
        (((canonicalFiberPseudofunctor X.p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y)).map
              sliceHom.op
              (η.app (op (Over.mk (𝟙 U))) (srcEq α))) := by
    simpa only [NatTrans.naturality, types_comp_apply] using
      congrArg (fun m => m (srcEq α))
        (η.naturality sliceHom.op)
  have hsrc :
      (((canonicalFiberPseudofunctor S'.p).presheafHom
            ((FibredCategoryMor.fiberFunctor G U).obj x)
            ((FibredCategoryMor.fiberFunctor G U).obj y)).map
          sliceHom.op (srcEq α)) =
        ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α := by
    simpa [slice, sliceHom] using
      identitySlicePresheafHom_map_hom_clean S'.p f
      ((FibredCategoryMor.fiberFunctor G U).obj x)
      ((FibredCategoryMor.fiberFunctor G U).obj y) α
  have htgt :
      (((canonicalFiberPseudofunctor X.p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y)).map
          sliceHom.op
          (tgtEq (stackificationLiftHomExtensionFiberMap X G hG F x y α))) =
        ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftHomExtensionFiberMap X G hG F x y α) := by
    simpa [slice, sliceHom] using
      identitySlicePresheafHom_map_hom_clean X.p f
      ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y)
      (stackificationLiftHomExtensionFiberMap X G hG F x y α)
  have hCompApp :=
    congrArg
      (fun μ =>
        μ.app (op slice) γ)
      (stackificationLiftHomExtension_comp X G hG F x y)
  have hGapp :
      (FibredCategoryMor.fibredMorphismPresheafMap G x y).app (op slice) γ =
        ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α := by
    let c₁ := FibredCategoryMor.pullbackComparison G f x
    let c₂ := FibredCategoryMor.pullbackComparison G f y
    change c₁.hom ≫ (FibredCategoryMor.fiberFunctor G V).map γ ≫ c₂.inv =
      ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α
    rw [hγ]
    change c₁.hom ≫ (c₁.inv ≫
        ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α ≫ c₂.hom) ≫
        c₂.inv =
      ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α
    calc
      c₁.hom ≫ (c₁.inv ≫
          ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α ≫ c₂.hom) ≫
          c₂.inv =
        (c₁.hom ≫ c₁.inv) ≫
          ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α ≫
          (c₂.hom ≫ c₂.inv) := by
          simp only [Category.assoc]
      _ = ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α := by
          rw [c₁.hom_inv_id, c₂.hom_inv_id]
          rw [Category.id_comp]
          exact Category.comp_id _
  have hFapp :
      (FibredCategoryMor.fibredMorphismPresheafMap F x y).app (op slice) γ =
        (FibredCategoryMor.pullbackComparison F f x).hom ≫
          (FibredCategoryMor.fiberFunctor F V).map γ ≫
          (FibredCategoryMor.pullbackComparison F f y).inv := by
    rfl
  have hη_slice :
      η.app (op slice)
          (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α) =
        (FibredCategoryMor.pullbackComparison F f x).hom ≫
          (FibredCategoryMor.fiberFunctor F V).map γ ≫
          (FibredCategoryMor.pullbackComparison F f y).inv := by
    simpa only [NatTrans.comp_app, types_comp_apply, hGapp, hFapp] using hCompApp
  have hPresheaf :
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftHomExtensionFiberMap X G hG F x y α) =
        (FibredCategoryMor.pullbackComparison F f x).hom ≫
          (FibredCategoryMor.fiberFunctor F V).map γ ≫
          (FibredCategoryMor.pullbackComparison F f y).inv := by
    calc
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftHomExtensionFiberMap X G hG F x y α)
          = (((canonicalFiberPseudofunctor X.p).presheafHom
              ((FibredCategoryMor.fiberFunctor F U).obj x)
              ((FibredCategoryMor.fiberFunctor F U).obj y)).map
                sliceHom.op
                (tgtEq (stackificationLiftHomExtensionFiberMap X G hG F x y α))) := htgt.symm
      _ = (((canonicalFiberPseudofunctor X.p).presheafHom
              ((FibredCategoryMor.fiberFunctor F U).obj x)
              ((FibredCategoryMor.fiberFunctor F U).obj y)).map
                sliceHom.op
                (η.app (op (Over.mk (𝟙 U))) (srcEq α))) := by
            rw [hη_id]
      _ = η.app (op slice)
              (((canonicalFiberPseudofunctor S'.p).presheafHom
                ((FibredCategoryMor.fiberFunctor G U).obj x)
                ((FibredCategoryMor.fiberFunctor G U).obj y)).map
                  sliceHom.op (srcEq α)) := hnat.symm
      _ = η.app (op slice)
              (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map α) := by
            rw [hsrc]
      _ = (FibredCategoryMor.pullbackComparison F f x).hom ≫
            (FibredCategoryMor.fiberFunctor F V).map γ ≫
          (FibredCategoryMor.pullbackComparison F f y).inv := hη_slice
  exact hPresheaf

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom-extension is compatible with pulling both
source objects back, after transporting across the fibred-morphism pullback comparisons. -/
private theorem stackificationLiftHomExtension_pullback_conjugated
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) {x y : S.p.Fiber U} :
    stackificationLiftHomExtension X G hG F
        (f ^*[canonicalPullbackChoice S.p] x)
        (f ^*[canonicalPullbackChoice S.p] y) =
      (fiberHomPresheafIso
          (FibredCategoryMor.pullbackComparison G f x).symm
          (FibredCategoryMor.pullbackComparison G f y).symm).hom ≫
        ((canonicalFiberPseudofunctor S'.p).overMapCompPresheafHomIso
          ((FibredCategoryMor.fiberFunctor G U).obj x)
          ((FibredCategoryMor.fiberFunctor G U).obj y) f).inv ≫
        Functor.whiskerLeft (Over.map f).op
          (stackificationLiftHomExtension X G hG F x y) ≫
        ((canonicalFiberPseudofunctor X.p).overMapCompPresheafHomIso
          ((FibredCategoryMor.fiberFunctor F U).obj x)
          ((FibredCategoryMor.fiberFunctor F U).obj y) f).hom ≫
        (fiberHomPresheafIso
          (FibredCategoryMor.pullbackComparison F f x).symm
          (FibredCategoryMor.pullbackComparison F f y).symm).inv := by
  refine
    (stackificationLiftHomExtension_ext X G hG F
      (f ^*[canonicalPullbackChoice S.p] x)
      (f ^*[canonicalPullbackChoice S.p] y) _ ?_).symm
  let sG :=
    (fiberHomPresheafIso
      (FibredCategoryMor.pullbackComparison G f x).symm
      (FibredCategoryMor.pullbackComparison G f y).symm).hom
  let cG :=
    ((canonicalFiberPseudofunctor S'.p).overMapCompPresheafHomIso
      ((FibredCategoryMor.fiberFunctor G U).obj x)
      ((FibredCategoryMor.fiberFunctor G U).obj y) f).inv
  let wη :=
    Functor.whiskerLeft (Over.map f).op
      (stackificationLiftHomExtension X G hG F x y)
  let cF :=
    ((canonicalFiberPseudofunctor X.p).overMapCompPresheafHomIso
      ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y) f).hom
  let sF :=
    (fiberHomPresheafIso
      (FibredCategoryMor.pullbackComparison F f x).symm
      (FibredCategoryMor.pullbackComparison F f y).symm).inv
  have hGbc :=
    fibredMorphismPresheafMap_pullbackComparison_baseChange G f (x := x) (y := y)
  have hFbc :=
    fibredMorphismPresheafMap_pullbackComparison_baseChange F f (x := x) (y := y)
  have hη :=
    stackificationLiftHomExtension_comp X G hG F x y
  dsimp only
  calc
    FibredCategoryMor.fibredMorphismPresheafMap G
          (f ^*[canonicalPullbackChoice S.p] x)
          (f ^*[canonicalPullbackChoice S.p] y) ≫
        (sG ≫ cG ≫ wη ≫ cF ≫ sF) =
      (FibredCategoryMor.fibredMorphismPresheafMap G
          (f ^*[canonicalPullbackChoice S.p] x)
          (f ^*[canonicalPullbackChoice S.p] y) ≫ sG ≫ cG) ≫ wη ≫ cF ≫ sF := by
        simp only [Category.assoc]
    _ =
      (((canonicalFiberPseudofunctor S.p).overMapCompPresheafHomIso x y f).inv ≫
          Functor.whiskerLeft (Over.map f).op
            (FibredCategoryMor.fibredMorphismPresheafMap G x y)) ≫
        wη ≫ cF ≫ sF := by
        rw [hGbc]
    _ =
      ((canonicalFiberPseudofunctor S.p).overMapCompPresheafHomIso x y f).inv ≫
        Functor.whiskerLeft (Over.map f).op
          (FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
            stackificationLiftHomExtension X G hG F x y) ≫
        cF ≫ sF := by
        simp only [wη, Category.assoc]
        rfl
    _ =
      ((canonicalFiberPseudofunctor S.p).overMapCompPresheafHomIso x y f).inv ≫
        Functor.whiskerLeft (Over.map f).op
          (FibredCategoryMor.fibredMorphismPresheafMap F x y) ≫
        cF ≫ sF := by
        rw [hη]
    _ =
      (FibredCategoryMor.fibredMorphismPresheafMap F
          (f ^*[canonicalPullbackChoice S.p] x)
          (f ^*[canonicalPullbackChoice S.p] y) ≫
        (fiberHomPresheafIso
          (FibredCategoryMor.pullbackComparison F f x).symm
          (FibredCategoryMor.pullbackComparison F f y).symm).hom ≫
        ((canonicalFiberPseudofunctor X.p).overMapCompPresheafHomIso
          ((FibredCategoryMor.fiberFunctor F U).obj x)
          ((FibredCategoryMor.fiberFunctor F U).obj y) f).inv) ≫
        cF ≫ sF := by
        rw [hFbc]
        simp only [Category.assoc]
    _ =
      FibredCategoryMor.fibredMorphismPresheafMap F
          (f ^*[canonicalPullbackChoice S.p] x)
          (f ^*[canonicalPullbackChoice S.p] y) := by
        dsimp only [cF, sF]
        let oF :=
          (canonicalFiberPseudofunctor X.p).overMapCompPresheafHomIso
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y) f
        let tF :=
          fiberHomPresheafIso
            (FibredCategoryMor.pullbackComparison F f x).symm
            (FibredCategoryMor.pullbackComparison F f y).symm
        change (FibredCategoryMor.fibredMorphismPresheafMap F
            (f ^*[canonicalPullbackChoice S.p] x)
            (f ^*[canonicalPullbackChoice S.p] y) ≫ tF.hom ≫ oF.inv) ≫
            oF.hom ≫ tF.inv =
          FibredCategoryMor.fibredMorphismPresheafMap F
            (f ^*[canonicalPullbackChoice S.p] x)
            (f ^*[canonicalPullbackChoice S.p] y)
        calc
          (FibredCategoryMor.fibredMorphismPresheafMap F
              (f ^*[canonicalPullbackChoice S.p] x)
              (f ^*[canonicalPullbackChoice S.p] y) ≫ tF.hom ≫ oF.inv) ≫
              oF.hom ≫ tF.inv =
            FibredCategoryMor.fibredMorphismPresheafMap F
              (f ^*[canonicalPullbackChoice S.p] x)
              (f ^*[canonicalPullbackChoice S.p] y) ≫ tF.hom ≫
              (oF.inv ≫ oF.hom) ≫ tF.inv := by
              simp only [Category.assoc]
          _ =
            FibredCategoryMor.fibredMorphismPresheafMap F
              (f ^*[canonicalPullbackChoice S.p] x)
              (f ^*[canonicalPullbackChoice S.p] y) ≫ tF.hom ≫ tF.inv := by
              rw [oF.inv_hom_id]
              cat_disch
          _ =
            FibredCategoryMor.fibredMorphismPresheafMap F
              (f ^*[canonicalPullbackChoice S.p] x)
              (f ^*[canonicalPullbackChoice S.p] y) := by
              rw [tF.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the identity-slice component of
`fiberHomPresheafIso.hom` is the expected conjugation. -/
private theorem fiberHomPresheafIso_hom_app_identitySlice
    (Y : FibredCategoryOver.{u, v, uS, vS} C)
    {U : C} {x₁ x₂ y₁ y₂ : Y.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (φ : x₁ ⟶ y₁) :
    (fiberHomPresheafIso (Y := Y) ex ey).hom.app
        (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv φ) =
      (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv
        (ex.inv ≫ φ ≫ ey.hom) := by
  simp [fiberHomPresheafIso, Pseudofunctor.presheafHomObjHomEquiv, Iso.homCongr,
    Category.assoc]
  rw [← (canonicalFiberPseudofunctor Y.p).mapId'_eq_mapId (LocallyDiscrete.mk (op U))]
  rw [(canonicalFiberPseudofunctor Y.p).mapId'_inv_naturality
      (𝟙 (LocallyDiscrete.mk (op U))) rfl ey.hom]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the identity-slice component of
`fiberHomPresheafIso.inv` is the expected inverse conjugation. -/
private theorem fiberHomPresheafIso_inv_app_identitySlice
    (Y : FibredCategoryOver.{u, v, uS, vS} C)
    {U : C} {x₁ x₂ y₁ y₂ : Y.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (φ : x₂ ⟶ y₂) :
    (fiberHomPresheafIso (Y := Y) ex ey).inv.app
        (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv φ) =
      (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv
        (ex.hom ≫ φ ≫ ey.inv) := by
  simp [fiberHomPresheafIso, Pseudofunctor.presheafHomObjHomEquiv, Iso.homCongr,
    Category.assoc]
  rw [← (canonicalFiberPseudofunctor Y.p).mapId'_eq_mapId (LocallyDiscrete.mk (op U))]
  rw [(canonicalFiberPseudofunctor Y.p).mapId'_inv_naturality
      (𝟙 (LocallyDiscrete.mk (op U))) rfl ey.inv]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the identity-slice Hom equivalence is the action of the
canonical pseudofunctor on the identity base morphism. -/
private theorem presheafHomObjHomEquiv_eq_map_id
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U : C} {M N : p.Fiber U} (φ : M ⟶ N) :
    (canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ =
      ((canonicalFiberPseudofunctor p).map (𝟙 U).op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op U))]
  rw [← Category.assoc]
  rw [← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
      (𝟙 (LocallyDiscrete.mk (op U))) rfl φ]
  rw [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
  rfl

private theorem op_toLoc_id_comp {U V : C} (f : V ⟶ U) :
    (𝟙 V ≫ f).op.toLoc = f.op.toLoc := by
  rw [Category.id_comp]

private theorem op_toLoc_id {U : C} :
    (𝟙 U).op.toLoc = 𝟙 (LocallyDiscrete.mk (op U)) := by
  rfl

private theorem toLoc_comp_id {U V : C} (f : V ⟶ U) :
    f.op.toLoc ≫ (𝟙 V).op.toLoc = f.op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, Category.id_comp]

private noncomputable def identitySliceOverMapIso {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) ≅ Over.mk f :=
  Over.isoMk (Iso.refl V) (by dsimp [Over.mk, Over.map, Comma.mapRight])

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the inverse base-change comparison at the identity slice
is restriction along the canonical over-isomorphism. -/
private theorem overMapCompPresheafHomIso_inv_app_identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS})
    {U V : C} (f : V ⟶ U) {M N : F.obj (.mk (op U))}
    (φ : (F.map f.op.toLoc).toFunctor.obj M ⟶
      (F.map f.op.toLoc).toFunctor.obj N) :
    ((F.overMapCompPresheafHomIso M N f).inv.app (op (Over.mk (𝟙 V)))
        (F.presheafHomObjHomEquiv φ)) =
      (F.presheafHom M N).map (identitySliceOverMapIso f).hom.op φ := by
  dsimp [Pseudofunctor.overMapCompPresheafHomIso, Pseudofunctor.presheafHom,
    Pseudofunctor.presheafHomObjHomEquiv, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Iso.homCongr, Iso.homFromEquiv, Iso.homToEquiv, Equiv.trans, identitySliceOverMapIso]
  let e := F.mapId (LocallyDiscrete.mk (op V))
  have hmid :
      e.hom.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj M) ≫ φ ≫
          e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N) =
        (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map φ := by
    simpa only [Functor.id_obj, Functor.id_map, Category.assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id] using
      (e.hom.toNatTrans.naturality_assoc φ
        (e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N))).symm
  rw [hmid]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the forward base-change comparison cancels the identity-slice
restriction along the canonical over-isomorphism. -/
private theorem overMapCompPresheafHomIso_hom_app_identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS})
    {U V : C} (f : V ⟶ U) {M N : F.obj (.mk (op U))}
    (δ : (F.presheafHom M N).obj (op (Over.mk f))) :
    ((F.overMapCompPresheafHomIso M N f).hom.app (op (Over.mk (𝟙 V)))
        ((F.presheafHom M N).map (identitySliceOverMapIso f).hom.op δ)) =
      F.presheafHomObjHomEquiv δ := by
  dsimp [Pseudofunctor.overMapCompPresheafHomIso, Pseudofunctor.presheafHom,
    Pseudofunctor.presheafHomObjHomEquiv, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Iso.homCongr, Iso.homFromEquiv, Iso.homToEquiv, Equiv.trans, identitySliceOverMapIso]
  let κ := F.mapComp' f.op.toLoc (𝟙 (LocallyDiscrete.mk (op V)))
    (f.op.toLoc ≫ 𝟙 (LocallyDiscrete.mk (op V))) rfl
  let e := F.mapId (LocallyDiscrete.mk (op V))
  let m := (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map δ
  change (κ.inv.toNatTrans.app M ≫ κ.hom.toNatTrans.app M ≫ m ≫
        κ.inv.toNatTrans.app N) ≫ κ.hom.toNatTrans.app N =
      e.hom.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj M) ≫ δ ≫
        e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N)
  have hmid :
      e.hom.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj M) ≫ δ ≫
          e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N) = m := by
    dsimp only [m]
    simpa only [Functor.id_obj, Functor.id_map, Category.assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id, Over.mk_hom] using
      (e.hom.toNatTrans.naturality_assoc δ
        (e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N))).symm
  rw [hmid]
  calc
    (κ.inv.toNatTrans.app M ≫ κ.hom.toNatTrans.app M ≫ m ≫
          κ.inv.toNatTrans.app N) ≫ κ.hom.toNatTrans.app N =
        m ≫ κ.inv.toNatTrans.app N ≫ κ.hom.toNatTrans.app N := by
          simpa only [Category.assoc, Category.id_comp] using
            congrArg
              (fun t => t ≫ m ≫ κ.inv.toNatTrans.app N ≫ κ.hom.toNatTrans.app N)
              (Cat.Hom.inv_hom_id_toNatTrans_app κ M)
    _ = m ≫ 𝟙 _ := by
          exact congrArg (fun t => m ≫ t) (Cat.Hom.inv_hom_id_toNatTrans_app κ N)
    _ = m := Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: evaluating the pullback-conjugated Hom-extension at the
identity slice gives the expected pullback-comparison conjugation formula. -/
theorem stackificationLiftHomExtension_app_pullbackComparison
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) {x y : S.p.Fiber U}
    (α : ((FibredCategoryMor.fiberFunctor G V).obj
        (f ^*[canonicalPullbackChoice S.p] x)) ⟶
      ((FibredCategoryMor.fiberFunctor G V).obj
        (f ^*[canonicalPullbackChoice S.p] y))) :
    (stackificationLiftHomExtension X G hG F x y).app (op (Over.mk f))
        ((FibredCategoryMor.pullbackComparison G f x).hom ≫ α ≫
          (FibredCategoryMor.pullbackComparison G f y).inv) =
      (FibredCategoryMor.pullbackComparison F f x).hom ≫
        stackificationLiftHomExtensionFiberMap X G hG F
          (f ^*[canonicalPullbackChoice S.p] x)
          (f ^*[canonicalPullbackChoice S.p] y) α ≫
        (FibredCategoryMor.pullbackComparison F f y).inv := by
  let ηU := stackificationLiftHomExtension X G hG F x y
  let ηV := stackificationLiftHomExtension X G hG F
    (f ^*[canonicalPullbackChoice S.p] x)
    (f ^*[canonicalPullbackChoice S.p] y)
  let sV :=
    (canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor G V).obj
        (f ^*[canonicalPullbackChoice S.p] x))
      (N := (FibredCategoryMor.fiberFunctor G V).obj
        (f ^*[canonicalPullbackChoice S.p] y))
  let tV :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F V).obj
        (f ^*[canonicalPullbackChoice S.p] x))
      (N := (FibredCategoryMor.fiberFunctor F V).obj
        (f ^*[canonicalPullbackChoice S.p] y))
  let cGx := FibredCategoryMor.pullbackComparison G f x
  let cGy := FibredCategoryMor.pullbackComparison G f y
  let cFx := FibredCategoryMor.pullbackComparison F f x
  let cFy := FibredCategoryMor.pullbackComparison F f y
  let βG := cGx.hom ≫ α ≫ cGy.inv
  let βF := stackificationLiftHomExtensionFiberMap X G hG F
    (f ^*[canonicalPullbackChoice S.p] x)
    (f ^*[canonicalPullbackChoice S.p] y) α
  have hV :
      ηV.app (op (Over.mk (𝟙 V))) (sV α) = tV βF := by
    dsimp only [βF, stackificationLiftHomExtensionFiberMap, ηV, sV, tV]
    exact (tV.apply_symm_apply _).symm
  have hEval :=
    congrArg
      (fun μ => μ.app (op (Over.mk (𝟙 V))) (sV α))
      (stackificationLiftHomExtension_pullback_conjugated X G hG F f (x := x) (y := y))
  let eOver := identitySliceOverMapIso f
  have hSrc :
      (((canonicalFiberPseudofunctor S'.p).overMapCompPresheafHomIso
          ((FibredCategoryMor.fiberFunctor G U).obj x)
          ((FibredCategoryMor.fiberFunctor G U).obj y) f).inv.app
          (op (Over.mk (𝟙 V)))
        ((fiberHomPresheafIso cGx.symm cGy.symm).hom.app
          (op (Over.mk (𝟙 V))) (sV α))) =
        (((canonicalFiberPseudofunctor S'.p).presheafHom
          ((FibredCategoryMor.fiberFunctor G U).obj x)
          ((FibredCategoryMor.fiberFunctor G U).obj y)).map eOver.hom.op βG) := by
    dsimp only [sV, βG, cGx, cGy, eOver]
    rw [fiberHomPresheafIso_hom_app_identitySlice]
    exact overMapCompPresheafHomIso_inv_app_identitySlice
      (canonicalFiberPseudofunctor S'.p) f βG
  have hTgt
      (δ : (((canonicalFiberPseudofunctor X.p).presheafHom
          ((FibredCategoryMor.fiberFunctor F U).obj x)
          ((FibredCategoryMor.fiberFunctor F U).obj y)).obj (op (Over.mk f)))) :
      (fiberHomPresheafIso cFx.symm cFy.symm).inv.app (op (Over.mk (𝟙 V)))
        ((((canonicalFiberPseudofunctor X.p).overMapCompPresheafHomIso
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y) f).hom.app
              (op (Over.mk (𝟙 V)))
            (((canonicalFiberPseudofunctor X.p).presheafHom
              ((FibredCategoryMor.fiberFunctor F U).obj x)
              ((FibredCategoryMor.fiberFunctor F U).obj y)).map eOver.hom.op δ))) =
        tV (cFx.inv ≫ δ ≫ cFy.hom) := by
    dsimp only [tV, cFx, cFy, eOver]
    rw [overMapCompPresheafHomIso_hom_app_identitySlice]
    exact fiberHomPresheafIso_inv_app_identitySlice
      (Y := X.toFibredCategoryOver) cFx.symm cFy.symm δ
  have hNat' :
      ηU.app ((Over.map f).op.obj (op (Over.mk (𝟙 V))))
          ((((canonicalFiberPseudofunctor S'.p).presheafHom
            ((FibredCategoryMor.fiberFunctor G U).obj x)
            ((FibredCategoryMor.fiberFunctor G U).obj y)).map eOver.hom.op βG)) =
        (((canonicalFiberPseudofunctor X.p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj x)
            ((FibredCategoryMor.fiberFunctor F U).obj y)).map eOver.hom.op
          (ηU.app (op (Over.mk f)) βG)) := by
    simpa only [NatTrans.naturality, types_comp_apply, eOver] using
      congrArg (fun m => m βG) (ηU.naturality eOver.hom.op)
  have hConj :
      βF = cFx.inv ≫ ηU.app (op (Over.mk f)) βG ≫ cFy.hom := by
    apply tV.injective
    calc
      tV βF = ηV.app (op (Over.mk (𝟙 V))) (sV α) := hV.symm
      _ =
          ((fiberHomPresheafIso cGx.symm cGy.symm).hom ≫
            ((canonicalFiberPseudofunctor S'.p).overMapCompPresheafHomIso
              ((FibredCategoryMor.fiberFunctor G U).obj x)
              ((FibredCategoryMor.fiberFunctor G U).obj y) f).inv ≫
            Functor.whiskerLeft (Over.map f).op ηU ≫
            ((canonicalFiberPseudofunctor X.p).overMapCompPresheafHomIso
              ((FibredCategoryMor.fiberFunctor F U).obj x)
              ((FibredCategoryMor.fiberFunctor F U).obj y) f).hom ≫
            (fiberHomPresheafIso cFx.symm cFy.symm).inv).app
              (op (Over.mk (𝟙 V))) (sV α) := by
            simpa only [ηU, ηV, cGx, cGy, cFx, cFy] using hEval
      _ = tV (cFx.inv ≫ ηU.app (op (Over.mk f)) βG ≫ cFy.hom) := by
            dsimp only [NatTrans.comp_app, types_comp_apply, Functor.whiskerLeft_app]
            rw [hSrc]
            rw [hNat']
            exact hTgt (ηU.app (op (Over.mk f)) βG)
  change ηU.app (op (Over.mk f)) βG = cFx.hom ≫ βF ≫ cFy.inv
  calc
    ηU.app (op (Over.mk f)) βG =
        (cFx.hom ≫ cFx.inv) ≫ ηU.app (op (Over.mk f)) βG ≫
          (cFy.hom ≫ cFy.inv) := by
      rw [cFx.hom_inv_id, cFy.hom_inv_id]
      rw [Category.id_comp]
      exact (Category.comp_id _).symm
    _ = cFx.hom ≫
        (cFx.inv ≫ ηU.app (op (Over.mk f)) βG ≫ cFy.hom) ≫ cFy.inv := by
      simp only [Category.assoc]
    _ = cFx.hom ≫ βF ≫ cFy.inv := by
      rw [← hConj]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the canonical Hom extension commutes with postcomposition
by an arbitrary target-side morphism between literal `G`-image objects. -/
private theorem stackificationLiftHomExtension_postcomp_arbitrary
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y z : S.p.Fiber U}
    (β : ((FibredCategoryMor.fiberFunctor G U).obj y) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj z)) :
    stackificationLiftHomExtension X G hG F x y ≫
        presheafHomPostcompMap
          (stackificationLiftHomExtensionFiberMap X G hG F y z β) =
      presheafHomPostcompMap β ≫
        stackificationLiftHomExtension X G hG F x z := by
  apply W_precomp_ext_to_sheaf (J := J.over U)
    (FibredCategoryMor.fibredMorphismPresheafMap G x y)
    (hG.morphismPresheafMap_W U x y)
  · exact
      Pseudofunctor.IsPrestack.isSheaf
        (F := canonicalFiberPseudofunctor X.p) (J := J) (S := U)
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj z)
  · apply NatTrans.ext
    funext W δ
    let f : W.unop.left ⟶ U := W.unop.hom
    let Mₛ' := ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor
    let Mₓ := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
    let cGx := FibredCategoryMor.pullbackComparison G f x
    let cGy := FibredCategoryMor.pullbackComparison G f y
    let cGz := FibredCategoryMor.pullbackComparison G f z
    let cFx := FibredCategoryMor.pullbackComparison F f x
    let cFy := FibredCategoryMor.pullbackComparison F f y
    let cFz := FibredCategoryMor.pullbackComparison F f z
    let βW : ((FibredCategoryMor.fiberFunctor G W.unop.left).obj
          (f ^*[canonicalPullbackChoice S.p] y)) ⟶
        ((FibredCategoryMor.fiberFunctor G W.unop.left).obj
          (f ^*[canonicalPullbackChoice S.p] z)) :=
      cGy.inv ≫ Mₛ'.map β ≫ cGz.hom
    let ηβW :=
      stackificationLiftHomExtensionFiberMap X G hG F
        (f ^*[canonicalPullbackChoice S.p] y)
        (f ^*[canonicalPullbackChoice S.p] z) βW
    have hβpull :
        Mₓ.map (stackificationLiftHomExtensionFiberMap X G hG F y z β) =
          cFy.hom ≫ ηβW ≫ cFz.inv := by
      have hsrc :
          cGy.hom ≫ βW ≫ cGz.inv = Mₛ'.map β := by
        dsimp only [βW]
        calc
          cGy.hom ≫ (cGy.inv ≫ Mₛ'.map β ≫ cGz.hom) ≫ cGz.inv =
              Mₛ'.map β ≫ cGz.hom ≫ cGz.inv := by
                simpa only [Category.assoc] using
                  hom_inv_comp_assoc_cancel cGy (Mₛ'.map β ≫ cGz.hom ≫ cGz.inv)
          _ = Mₛ'.map β := by
                simpa only [Category.assoc] using
                  comp_hom_inv_assoc_cancel (Mₛ'.map β) cGz
      have hmap :=
        stackificationLiftHomExtensionFiberMap_pullback X G hG F f
          (x := y) (y := z) β
      have hpull :=
        stackificationLiftHomExtension_app_pullbackComparison X G hG F f
          (x := y) (y := z) βW
      rw [hsrc] at hpull
      exact hmap.symm.trans hpull
    have hrightArg :
        (cGx.hom ≫ (FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫ cGy.inv) ≫
            Mₛ'.map β =
          cGx.hom ≫
            ((FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫ βW) ≫
              cGz.inv := by
      dsimp only [βW]
      calc
        (cGx.hom ≫ (FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫ cGy.inv) ≫
            Mₛ'.map β =
          cGx.hom ≫ (FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫
            cGy.inv ≫ Mₛ'.map β := by
            simp only [Category.assoc]
        _ =
          cGx.hom ≫ (FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫
            cGy.inv ≫ Mₛ'.map β ≫ (cGz.hom ≫ cGz.inv) := by
            simpa only [Category.assoc] using
              (comp_hom_inv_assoc_cancel
                (cGx.hom ≫ (FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫
                  cGy.inv ≫ Mₛ'.map β) cGz).symm
        _ =
          cGx.hom ≫
            ((FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫
              (cGy.inv ≫ Mₛ'.map β ≫ cGz.hom)) ≫ cGz.inv := by
            simp only [Category.assoc]
    have hrightEval :
        (stackificationLiftHomExtension X G hG F x z).app W
            ((cGx.hom ≫ (FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫
                cGy.inv) ≫ Mₛ'.map β) =
          cFx.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f ^*[canonicalPullbackChoice S.p] x)
              (f ^*[canonicalPullbackChoice S.p] z)
              ((FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫ βW) ≫
            cFz.inv := by
      rw [hrightArg]
      exact
        stackificationLiftHomExtension_app_pullbackComparison X G hG F f
          (x := x) (y := z)
          ((FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫ βW)
    have hlocal :
        stackificationLiftHomExtensionFiberMap X G hG F
            (f ^*[canonicalPullbackChoice S.p] x)
            (f ^*[canonicalPullbackChoice S.p] z)
            ((FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫ βW) =
          (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ηβW := by
      exact
        stackificationLiftHomExtensionFiberMap_precomp_image X G hG F δ βW
    have hsource :
        ((FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
            stackificationLiftHomExtension X G hG F x y).app W δ) =
          (FibredCategoryMor.fibredMorphismPresheafMap F x y).app W δ := by
      exact
        congrArg (fun η => η.app W δ)
          (stackificationLiftHomExtension_comp X G hG F x y)
    calc
      (FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
              stackificationLiftHomExtension X G hG F x y ≫
                presheafHomPostcompMap
                  (stackificationLiftHomExtensionFiberMap X G hG F y z β)).app W δ =
          ((FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
              stackificationLiftHomExtension X G hG F x y).app W δ) ≫
            Mₓ.map (stackificationLiftHomExtensionFiberMap X G hG F y z β) := by
            rfl
      _ =
          (cFx.hom ≫ (FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ cFy.inv) ≫
            Mₓ.map (stackificationLiftHomExtensionFiberMap X G hG F y z β) := by
            rw [hsource]
            rfl
      _ =
          cFx.hom ≫ ((FibredCategoryMor.fiberFunctor F W.unop.left).map δ ≫ ηβW) ≫
            cFz.inv := by
            rw [hβpull]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ =
          cFx.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f ^*[canonicalPullbackChoice S.p] x)
              (f ^*[canonicalPullbackChoice S.p] z)
              ((FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫ βW) ≫
            cFz.inv := by
            rw [hlocal]
      _ =
          (stackificationLiftHomExtension X G hG F x z).app W
            ((cGx.hom ≫ (FibredCategoryMor.fiberFunctor G W.unop.left).map δ ≫
                cGy.inv) ≫ Mₛ'.map β) := hrightEval.symm
      _ =
          (FibredCategoryMor.fibredMorphismPresheafMap G x y ≫
              presheafHomPostcompMap β ≫
                stackificationLiftHomExtension X G hG F x z).app W δ := by
            rfl

/-- Helper for Chap08 Lemma 8 8 3: the Hom-extension fiber-map evaluation preserves
composition of arbitrary target-side morphisms between literal `G`-image objects. -/
theorem stackificationLiftHomExtensionFiberMap_comp
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    ∀ ⦃U : C⦄ ⦃x y z : S.p.Fiber U⦄
      (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
        ((FibredCategoryMor.fiberFunctor G U).obj y))
      (β : ((FibredCategoryMor.fiberFunctor G U).obj y) ⟶
        ((FibredCategoryMor.fiberFunctor G U).obj z)),
      stackificationLiftHomExtensionFiberMap X G hG F x z (α ≫ β) =
        stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β := by
  intro U x y z α β
  let eXY :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj y)
  let eXZ :=
    (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor F U).obj x)
      (N := (FibredCategoryMor.fiberFunctor F U).obj z)
  let sXY :=
    (canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
      (M := (FibredCategoryMor.fiberFunctor G U).obj x)
      (N := (FibredCategoryMor.fiberFunctor G U).obj y)
  have hEval :=
    congrArg
      (fun η => η.app (op (Over.mk (𝟙 U))) (sXY α))
      (stackificationLiftHomExtension_postcomp_arbitrary X G hG F β)
  have hLeft :
      (stackificationLiftHomExtension X G hG F x y ≫
          presheafHomPostcompMap
            (stackificationLiftHomExtensionFiberMap X G hG F y z β)).app
          (op (Over.mk (𝟙 U))) (sXY α) =
        eXZ (stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    have hα :
        (stackificationLiftHomExtension X G hG F x y).app (op (Over.mk (𝟙 U))) (sXY α) =
          eXY (stackificationLiftHomExtensionFiberMap X G hG F x y α) := by
      dsimp only [stackificationLiftHomExtensionFiberMap]
      exact (eXY.apply_symm_apply _).symm
    rw [hα]
    exact
      presheafHomPostcompMap_app_id
        (F := canonicalFiberPseudofunctor X.p)
        (stackificationLiftHomExtensionFiberMap X G hG F y z β)
        (stackificationLiftHomExtensionFiberMap X G hG F x y α)
  have hRight :
      (presheafHomPostcompMap β ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sXY α) =
        eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z
          (α ≫ β)) := by
    dsimp only [NatTrans.comp_app, types_comp_apply]
    rw [presheafHomPostcompMap_app_id (F := canonicalFiberPseudofunctor S'.p)]
    dsimp only [stackificationLiftHomExtensionFiberMap]
    exact (eXZ.apply_symm_apply _).symm
  apply eXZ.injective
  calc
    eXZ (stackificationLiftHomExtensionFiberMap X G hG F x z (α ≫ β)) =
      (presheafHomPostcompMap β ≫
          stackificationLiftHomExtension X G hG F x z).app
          (op (Over.mk (𝟙 U))) (sXY α) := hRight.symm
    _ =
      (stackificationLiftHomExtension X G hG F x y ≫
          presheafHomPostcompMap
            (stackificationLiftHomExtensionFiberMap X G hG F y z β)).app
          (op (Over.mk (𝟙 U))) (sXY α) := hEval.symm
    _ =
      eXZ (stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
          stackificationLiftHomExtensionFiberMap X G hG F y z β) := hLeft

/-- Helper for Chap08 Lemma 8 8 3: a commutative square after applying `G` remains
commutative after applying the Hom-extension fiber map. -/
theorem stackificationLiftHomExtensionFiberMap_square
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x₁ x₂ y₁ y₂ : S.p.Fiber U}
    (α₁ : ((FibredCategoryMor.fiberFunctor G U).obj x₁) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y₁))
    (βx : ((FibredCategoryMor.fiberFunctor G U).obj x₁) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj x₂))
    (βy : ((FibredCategoryMor.fiberFunctor G U).obj y₁) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y₂))
    (α₂ : ((FibredCategoryMor.fiberFunctor G U).obj x₂) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y₂))
    (h : α₁ ≫ βy = βx ≫ α₂) :
    stackificationLiftHomExtensionFiberMap X G hG F x₁ y₁ α₁ ≫
        stackificationLiftHomExtensionFiberMap X G hG F y₁ y₂ βy =
      stackificationLiftHomExtensionFiberMap X G hG F x₁ x₂ βx ≫
        stackificationLiftHomExtensionFiberMap X G hG F x₂ y₂ α₂ := by
  -- Turn both composites into Hom-extensions of source-side composites, then use the given
  -- commutative square in the target stackification fiber.
  rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F α₁ βy,
    ← stackificationLiftHomExtensionFiberMap_comp X G hG F βx α₂, h]

/-- Helper for Chap08 Lemma 8 8 3: changing source models by fiber isomorphisms conjugates the
Hom-extension fiber map by the corresponding `F`-images. -/
theorem stackificationLiftHomExtensionFiberMap_transport_of_sourceIso
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x x' y y' : S.p.Fiber U}
    (ex : x ≅ x') (ey : y ≅ y')
    (α : ((FibredCategoryMor.fiberFunctor G U).obj x') ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj y')) :
    stackificationLiftHomExtensionFiberMap X G hG F x y
        (((FibredCategoryMor.fiberFunctor G U).map ex.hom) ≫
          α ≫ ((FibredCategoryMor.fiberFunctor G U).map ey.inv)) =
      ((FibredCategoryMor.fiberFunctor F U).map ex.hom) ≫
        stackificationLiftHomExtensionFiberMap X G hG F x' y' α ≫
          ((FibredCategoryMor.fiberFunctor F U).map ey.inv) := by
  -- Split the conjugated source morphism into two compositions, use functoriality of the
  -- Hom-extension fiber map, and evaluate it on literal source-image isomorphisms.
  calc
    stackificationLiftHomExtensionFiberMap X G hG F x y
        (((FibredCategoryMor.fiberFunctor G U).map ex.hom) ≫
          α ≫ ((FibredCategoryMor.fiberFunctor G U).map ey.inv)) =
      stackificationLiftHomExtensionFiberMap X G hG F x y
        (((FibredCategoryMor.fiberFunctor G U).map ex.hom) ≫
          (α ≫ ((FibredCategoryMor.fiberFunctor G U).map ey.inv))) := by
        rfl
    _ =
      stackificationLiftHomExtensionFiberMap X G hG F x x'
          ((FibredCategoryMor.fiberFunctor G U).map ex.hom) ≫
        stackificationLiftHomExtensionFiberMap X G hG F x' y
          (α ≫ ((FibredCategoryMor.fiberFunctor G U).map ey.inv)) := by
        rw [stackificationLiftHomExtensionFiberMap_comp]
    _ =
      ((FibredCategoryMor.fiberFunctor F U).map ex.hom) ≫
        stackificationLiftHomExtensionFiberMap X G hG F x' y
          (α ≫ ((FibredCategoryMor.fiberFunctor G U).map ey.inv)) := by
        rw [stackificationLiftHomExtensionFiberMap_on_image]
    _ =
      ((FibredCategoryMor.fiberFunctor F U).map ex.hom) ≫
        (stackificationLiftHomExtensionFiberMap X G hG F x' y' α ≫
          stackificationLiftHomExtensionFiberMap X G hG F y' y
            ((FibredCategoryMor.fiberFunctor G U).map ey.inv)) := by
        rw [stackificationLiftHomExtensionFiberMap_comp]
    _ =
      ((FibredCategoryMor.fiberFunctor F U).map ex.hom) ≫
        (stackificationLiftHomExtensionFiberMap X G hG F x' y' α ≫
          ((FibredCategoryMor.fiberFunctor F U).map ey.inv)) := by
        rw [stackificationLiftHomExtensionFiberMap_on_image]
    _ =
      ((FibredCategoryMor.fiberFunctor F U).map ex.hom) ≫
        stackificationLiftHomExtensionFiberMap X G hG F x' y' α ≫
          ((FibredCategoryMor.fiberFunctor F U).map ey.inv) := by
        rfl

/-- Helper for Chap08 Lemma 8 8 3: on literal source-image morphisms, the canonical Hom
extension carries a composite to the corresponding composite under the fixed source morphism. -/
private theorem stackificationLiftHomExtension_on_image_comp
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y z : S.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (stackificationLiftHomExtension X G hG F x z).app (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
          (((FibredCategoryMor.fiberFunctor G U).map φ) ≫
            ((FibredCategoryMor.fiberFunctor G U).map ψ))) =
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
        (((FibredCategoryMor.fiberFunctor F U).map φ) ≫
          ((FibredCategoryMor.fiberFunctor F U).map ψ)) := by
  -- Reduce source-image composition to the already established image formula for `φ ≫ ψ`.
  simpa only [Functor.map_comp] using
    stackificationLiftHomExtension_on_image X G hG F (φ ≫ ψ)

/-- Helper for Chap08 Lemma 8 8 3: the fiber-level Hom-extension evaluation carries literal
source-image composites to the corresponding composites under `F`. -/
private theorem stackificationLiftHomExtensionFiberMap_on_image_comp
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y z : S.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    stackificationLiftHomExtensionFiberMap X G hG F x z
        (((FibredCategoryMor.fiberFunctor G U).map φ) ≫
          ((FibredCategoryMor.fiberFunctor G U).map ψ)) =
      ((FibredCategoryMor.fiberFunctor F U).map φ) ≫
        ((FibredCategoryMor.fiberFunctor F U).map ψ) := by
  -- Reduce the composite to the image of `φ ≫ ψ`, then use the fiber-level image formula.
  simpa only [Functor.map_comp] using
    stackificationLiftHomExtensionFiberMap_on_image X G hG F (φ ≫ ψ)

/-- Helper for Chap08 Lemma 8 8 3: on literal source-image isomorphisms, the Hom extension sends
the hom-then-inv composite to the identity under the fixed source morphism. -/
private theorem stackificationLiftHomExtension_on_image_hom_inv
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y : S.p.Fiber U} (e : x ≅ y) :
    (stackificationLiftHomExtension X G hG F x x).app (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
          (((FibredCategoryMor.fiberFunctor G U).map e.hom) ≫
            ((FibredCategoryMor.fiberFunctor G U).map e.inv))) =
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
        (𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
  -- The composition lemma identifies the Hom-extension value, and the target functor maps
  -- the inverse pair to an identity.
  have hcomp := stackificationLiftHomExtension_on_image_comp X G hG F e.hom e.inv
  have htarget :
      ((FibredCategoryMor.fiberFunctor F U).map e.hom) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.inv) =
        𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x) := by
    calc
      ((FibredCategoryMor.fiberFunctor F U).map e.hom) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.inv) =
          (FibredCategoryMor.fiberFunctor F U).map (e.hom ≫ e.inv) := by
            exact ((FibredCategoryMor.fiberFunctor F U).map_comp e.hom e.inv).symm
      _ = 𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x) := by
            simp only [Iso.hom_inv_id, Functor.map_id]
  exact hcomp.trans
    (congrArg
      (fun m ↦ (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv m)
      htarget)

/-- Helper for Chap08 Lemma 8 8 3: the fiber-level Hom-extension evaluation sends a literal
source-image hom-then-inv composite to the identity. -/
private theorem stackificationLiftHomExtensionFiberMap_on_image_hom_inv
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y : S.p.Fiber U} (e : x ≅ y) :
    stackificationLiftHomExtensionFiberMap X G hG F x x
        (((FibredCategoryMor.fiberFunctor G U).map e.hom) ≫
          ((FibredCategoryMor.fiberFunctor G U).map e.inv)) =
      𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x) := by
  -- Convert the inverse pair into a source-image composite and cancel it in the source fiber.
  have hcomp := stackificationLiftHomExtensionFiberMap_on_image_comp X G hG F e.hom e.inv
  have htarget :
      ((FibredCategoryMor.fiberFunctor F U).map e.hom) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.inv) =
        𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x) := by
    calc
      ((FibredCategoryMor.fiberFunctor F U).map e.hom) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.inv) =
          (FibredCategoryMor.fiberFunctor F U).map (e.hom ≫ e.inv) := by
            exact ((FibredCategoryMor.fiberFunctor F U).map_comp e.hom e.inv).symm
      _ = 𝟙 ((FibredCategoryMor.fiberFunctor F U).obj x) := by
            simp only [Iso.hom_inv_id, Functor.map_id]
  exact hcomp.trans htarget

/-- Helper for Chap08 Lemma 8 8 3: on literal source-image isomorphisms, the Hom extension sends
the inv-then-hom composite to the identity under the fixed source morphism. -/
private theorem stackificationLiftHomExtension_on_image_inv_hom
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y : S.p.Fiber U} (e : x ≅ y) :
    (stackificationLiftHomExtension X G hG F y y).app (op (Over.mk (𝟙 U)))
        ((canonicalFiberPseudofunctor S'.p).presheafHomObjHomEquiv
          (((FibredCategoryMor.fiberFunctor G U).map e.inv) ≫
            ((FibredCategoryMor.fiberFunctor G U).map e.hom))) =
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
        (𝟙 ((FibredCategoryMor.fiberFunctor F U).obj y)) := by
  -- This is the previous inverse-pair argument applied in the opposite order.
  have hcomp := stackificationLiftHomExtension_on_image_comp X G hG F e.inv e.hom
  have htarget :
      ((FibredCategoryMor.fiberFunctor F U).map e.inv) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.hom) =
        𝟙 ((FibredCategoryMor.fiberFunctor F U).obj y) := by
    calc
      ((FibredCategoryMor.fiberFunctor F U).map e.inv) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.hom) =
          (FibredCategoryMor.fiberFunctor F U).map (e.inv ≫ e.hom) := by
            exact ((FibredCategoryMor.fiberFunctor F U).map_comp e.inv e.hom).symm
      _ = 𝟙 ((FibredCategoryMor.fiberFunctor F U).obj y) := by
            simp only [Iso.inv_hom_id, Functor.map_id]
  exact hcomp.trans
    (congrArg
      (fun m ↦ (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv m)
      htarget)

/-- Helper for Chap08 Lemma 8 8 3: the fiber-level Hom-extension evaluation sends a literal
source-image inv-then-hom composite to the identity. -/
private theorem stackificationLiftHomExtensionFiberMap_on_image_inv_hom
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x y : S.p.Fiber U} (e : x ≅ y) :
    stackificationLiftHomExtensionFiberMap X G hG F y y
        (((FibredCategoryMor.fiberFunctor G U).map e.inv) ≫
          ((FibredCategoryMor.fiberFunctor G U).map e.hom)) =
      𝟙 ((FibredCategoryMor.fiberFunctor F U).obj y) := by
  -- This is the previous fiber-level inverse cancellation applied to the opposite composite.
  have hcomp := stackificationLiftHomExtensionFiberMap_on_image_comp X G hG F e.inv e.hom
  have htarget :
      ((FibredCategoryMor.fiberFunctor F U).map e.inv) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.hom) =
        𝟙 ((FibredCategoryMor.fiberFunctor F U).obj y) := by
    calc
      ((FibredCategoryMor.fiberFunctor F U).map e.inv) ≫
          ((FibredCategoryMor.fiberFunctor F U).map e.hom) =
          (FibredCategoryMor.fiberFunctor F U).map (e.inv ≫ e.hom) := by
            exact ((FibredCategoryMor.fiberFunctor F U).map_comp e.inv e.hom).symm
      _ = 𝟙 ((FibredCategoryMor.fiberFunctor F U).obj y) := by
            simp only [Iso.inv_hom_id, Functor.map_id]
  exact hcomp.trans htarget

/-- Helper for Chap08 Lemma 8 8 3: the fixed cover used to glue the value of the lifted functor
on a target fiber object. -/
noncomputable def stackificationLiftObjectCover
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y : S'.p.Fiber U) :
    J.Cover U :=
  let R : Sieve U := {
    arrows {_V} q :=
      ∃ xq : S.p.Fiber _V,
        Nonempty
          (((FibredCategoryMor.fiberFunctor G _V).obj xq) ≅
            q ^*[canonicalPullbackChoice S'.p] y)
    downward_closed := by
      intro V W q hq g
      rcases hq with ⟨xq, ⟨eq⟩⟩
      refine ⟨g ^*[canonicalPullbackChoice S.p] xq, ⟨?_⟩⟩
      exact
        ((FibredCategoryMor.pullbackComparison G g xq).symm ≪≫
          (((canonicalFiberPseudofunctor S'.p).map g.op.toLoc).toFunctor.mapIso eq)) ≪≫
          (mapCompAppIso S'.p q g (g ≫ q)
            (FibredCategoryMor.comp_toLoc_eq q g (g ≫ q) rfl) y).symm
  }
  ⟨R, by
    rcases hG.locallyEssentiallySurjectiveOnObjects U y with ⟨Scover, hScover⟩
    exact J.superset_covering (S := Scover) (R := R) (by
      intro V q hq
      rcases hScover ⟨V, q, hq⟩ with ⟨xq, hxq⟩
      exact ⟨xq, hxq⟩) Scover.condition⟩

/-- Helper for Chap08 Lemma 8 8 3: every arrow of the chosen object cover carries a source
model for the pulled-back target object. -/
private theorem stackificationLiftObjectCover_spec
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y : S'.p.Fiber U) :
    ∀ I : (stackificationLiftObjectCover (J := J) G hG y).Arrow,
      ∃ xI : S.p.Fiber I.Y,
        Nonempty
          (((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
            I.f ^*[canonicalPullbackChoice S'.p] y) := by
  intro I
  exact I.hf

/-- Helper for Chap08 Lemma 8 8 3: the chosen source model on one member of the object cover. -/
noncomputable def stackificationLiftObjectModel
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y : S'.p.Fiber U)
    (I : (stackificationLiftObjectCover (J := J) G hG y).Arrow) :
    Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y :=
  ⟨Classical.choose
      (stackificationLiftObjectCover_spec (J := J) G hG y I),
    Classical.choice
      (Classical.choose_spec
        (stackificationLiftObjectCover_spec (J := J) G hG y I))⟩

/-- Helper for Chap08 Lemma 8 8 3: the local object in the target stack attached to a chosen
source model. -/
private noncomputable def stackificationLiftLocalObject
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U)
    (I : (stackificationLiftObjectCover (J := J) G hG y).Arrow) :
    X.p.Fiber I.Y :=
  (FibredCategoryMor.fiberFunctor F I.Y).obj
    (stackificationLiftObjectModel (J := J) G hG y I).1

/-- Helper for Chap08 Lemma 8 8 3: after pulling a local source model back to a common overlap,
its image under `G` is canonically identified with the corresponding pullback of the target
object. -/
noncomputable def stackificationLiftObjectModelPullbackIso
    (G : S ⟶ S')
    {U V : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) (I : Scover.Arrow) (fI : V ⟶ I.Y)
    (hfI : fI ≫ I.f = q) :
    ((FibredCategoryMor.fiberFunctor G V).obj
        (fI ^*[canonicalPullbackChoice S.p] (model I).1)) ≅
      q ^*[canonicalPullbackChoice S'.p] y :=
  ((FibredCategoryMor.pullbackComparison G fI (model I).1).symm ≪≫
      (((canonicalFiberPseudofunctor S'.p).map fI.op.toLoc).toFunctor.mapIso
        (model I).2)) ≪≫
    (mapCompAppIso S'.p I.f fI q
      (FibredCategoryMor.comp_toLoc_eq I.f fI q hfI) y).symm

/-- Helper for Chap08 Lemma 8 8 3: the local model isomorphism for a cover branch is compatible
with an additional pullback of the overlap. -/
private theorem stackificationLiftObjectModelPullbackIso_pullback
    (G : S ⟶ S')
    {U V V' : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    (I : Scover.Arrow) (fI : V ⟶ I.Y) (hfI : fI ≫ I.f = q)
    (gfI : V' ⟶ I.Y) (hgfI : g ≫ fI = gfI) :
    ((FibredCategoryMor.fiberFunctor G V').mapIso
        (mapCompAppIso S.p fI g gfI
          (FibredCategoryMor.comp_toLoc_eq fI g gfI hgfI) (model I).1) ≪≫
      (FibredCategoryMor.pullbackComparison G g
        (fI ^*[canonicalPullbackChoice S.p] (model I).1)).symm ≪≫
      (((canonicalFiberPseudofunctor S'.p).map g.op.toLoc).toFunctor.mapIso
        (stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
          q I fI hfI)) ≪≫
      (mapCompAppIso S'.p q g q'
        (FibredCategoryMor.comp_toLoc_eq q g q' hq) y).symm) =
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model q' I gfI
      (by rw [← hq, ← hgfI, Category.assoc, hfI]) := by
  apply Iso.ext
  dsimp only [stackificationLiftObjectModelPullbackIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, mapCompAppIso,
    Category.assoc]
  -- The equality is the pullback-comparison cocycle for `G`, followed by pseudofunctor
  -- associativity for the two base-composition comparisons.
  let M := ((canonicalFiberPseudofunctor S'.p).map g.op.toLoc).toFunctor
  let mf := ((canonicalFiberPseudofunctor S'.p).map fI.op.toLoc).toFunctor
  let cgf := FibredCategoryMor.pullbackComparison G gfI (model I).1
  let cg := FibredCategoryMor.pullbackComparison G g
    (fI ^*[canonicalPullbackChoice S.p] (model I).1)
  let cf := FibredCategoryMor.pullbackComparison G fI (model I).1
  let κS := (canonicalFiberPseudofunctor S.p).mapComp' fI.op.toLoc g.op.toLoc
    gfI.op.toLoc (FibredCategoryMor.comp_toLoc_eq fI g gfI hgfI)
  let κS' := (canonicalFiberPseudofunctor S'.p).mapComp' fI.op.toLoc g.op.toLoc
    gfI.op.toLoc (FibredCategoryMor.comp_toLoc_eq fI g gfI hgfI)
  let κq := (canonicalFiberPseudofunctor S'.p).mapComp' q.op.toLoc g.op.toLoc
    q'.op.toLoc (FibredCategoryMor.comp_toLoc_eq q g q' hq)
  let κIf := (canonicalFiberPseudofunctor S'.p).mapComp' I.f.op.toLoc fI.op.toLoc
    q.op.toLoc (FibredCategoryMor.comp_toLoc_eq I.f fI q hfI)
  let κIgf := (canonicalFiberPseudofunctor S'.p).mapComp' I.f.op.toLoc gfI.op.toLoc
    q'.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq I.f gfI q'
        (by rw [← hq, ← hgfI, Category.assoc, hfI]))
  have hmap :
      M.map (cf.inv ≫ mf.map (model I).2.hom ≫ κIf.inv.toNatTrans.app y) =
        M.map cf.inv ≫ M.map (mf.map (model I).2.hom) ≫
          M.map (κIf.inv.toNatTrans.app y) := by
    rw [Functor.map_comp, Functor.map_comp]
  change
    (FibredCategoryMor.fiberFunctor G V').map (κS.hom.toNatTrans.app (model I).1) ≫
        cg.inv ≫ M.map (cf.inv ≫ mf.map (model I).2.hom ≫ κIf.inv.toNatTrans.app y) ≫
          κq.inv.toNatTrans.app y =
      cgf.inv ≫
        ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
          (model I).2.hom ≫
        κIgf.inv.toNatTrans.app y
  rw [hmap]
  have hcoc :
      cg.inv ≫ M.map cf.inv ≫
          κS'.inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) =
        (FibredCategoryMor.fiberFunctor G V').map
            (κS.inv.toNatTrans.app (model I).1) ≫ cgf.inv := by
    exact pullbackComparison_mapComp_inv_cocycle G fI g gfI hgfI (model I).1
  have hGcomp :
      (FibredCategoryMor.fiberFunctor G V').map (κS.hom.toNatTrans.app (model I).1) ≫
          cg.inv ≫ M.map cf.inv =
        cgf.inv ≫
          κS'.hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) := by
    have hκS'cancel :
        κS'.inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) ≫
            κS'.hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) =
          𝟙 _ :=
      Cat.Hom.inv_hom_id_toNatTrans_app κS'
        ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1)
    have hcancel :
        (FibredCategoryMor.fiberFunctor G V').map
              (κS.hom.toNatTrans.app (model I).1) ≫
          (FibredCategoryMor.fiberFunctor G V').map
              (κS.inv.toNatTrans.app (model I).1) =
        𝟙 _ := by
      calc
        (FibredCategoryMor.fiberFunctor G V').map
              (κS.hom.toNatTrans.app (model I).1) ≫
            (FibredCategoryMor.fiberFunctor G V').map
              (κS.inv.toNatTrans.app (model I).1) =
          (FibredCategoryMor.fiberFunctor G V').map
            (κS.hom.toNatTrans.app (model I).1 ≫
              κS.inv.toNatTrans.app (model I).1) := by
            exact ((FibredCategoryMor.fiberFunctor G V').map_comp
              (κS.hom.toNatTrans.app (model I).1)
              (κS.inv.toNatTrans.app (model I).1)).symm
        _ = (FibredCategoryMor.fiberFunctor G V').map (𝟙 _) := by
          exact congrArg (FibredCategoryMor.fiberFunctor G V').map
            (Cat.Hom.hom_inv_id_toNatTrans_app κS (model I).1)
        _ = 𝟙 _ := by
          rw [Functor.map_id]
    let L :=
        (FibredCategoryMor.fiberFunctor G V').map
            (κS.hom.toNatTrans.app (model I).1) ≫
          cg.inv ≫ M.map cf.inv
    have hleft_inv :
          L ≫ κS'.inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) =
          cgf.inv := by
      have hstep :
          (FibredCategoryMor.fiberFunctor G V').map
              (κS.hom.toNatTrans.app (model I).1) ≫
            cg.inv ≫ M.map cf.inv ≫
              κS'.inv.toNatTrans.app
                ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) =
          ((FibredCategoryMor.fiberFunctor G V').map
              (κS.hom.toNatTrans.app (model I).1) ≫
            (FibredCategoryMor.fiberFunctor G V').map
              (κS.inv.toNatTrans.app (model I).1)) ≫ cgf.inv := by
        simpa only [Category.assoc] using
          congrArg
            (fun t =>
              (FibredCategoryMor.fiberFunctor G V').map
                (κS.hom.toNatTrans.app (model I).1) ≫ t)
            hcoc
      have hcollapse :
          ((FibredCategoryMor.fiberFunctor G V').map
              (κS.hom.toNatTrans.app (model I).1) ≫
            (FibredCategoryMor.fiberFunctor G V').map
              (κS.inv.toNatTrans.app (model I).1)) ≫ cgf.inv =
          cgf.inv := by
        calc
          ((FibredCategoryMor.fiberFunctor G V').map
              (κS.hom.toNatTrans.app (model I).1) ≫
            (FibredCategoryMor.fiberFunctor G V').map
              (κS.inv.toNatTrans.app (model I).1)) ≫ cgf.inv =
            𝟙 _ ≫ cgf.inv := by
            exact congrArg (fun t => t ≫ cgf.inv) hcancel
          _ = cgf.inv := by
            simp only [Category.id_comp]
      simpa only [L, Category.assoc] using hstep.trans hcollapse
    change L =
      cgf.inv ≫
        κS'.hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1)
    rw [← hleft_inv]
    calc
      L = L ≫ 𝟙 _ := by
        exact (Category.comp_id L).symm
      _ =
        L ≫
          (κS'.inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) ≫
            κS'.hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1)) := by
        exact congrArg (fun t => L ≫ t) hκS'cancel.symm
      _ =
        (L ≫ κS'.inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1)) ≫
          κS'.hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) := by
        simp only [Category.assoc]
  have hnat :
      κS'.hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) ≫
          M.map (mf.map (model I).2.hom) =
        ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
            (model I).2.hom ≫
          κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) := by
    exact
      ((canonicalFiberPseudofunctor S'.p).mapComp'_hom_naturality
        fI.op.toLoc g.op.toLoc gfI.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq fI g gfI hgfI) (model I).2.hom).symm
  have hassoc :
      M.map (κIf.inv.toNatTrans.app y) ≫ κq.inv.toNatTrans.app y =
        κS'.inv.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
          κIgf.inv.toNatTrans.app y := by
    exact
      (canonicalFiberPseudofunctor S'.p).mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
        I.f.op.toLoc fI.op.toLoc g.op.toLoc q.op.toLoc gfI.op.toLoc q'.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq I.f fI q hfI)
        (FibredCategoryMor.comp_toLoc_eq fI g gfI hgfI)
        (FibredCategoryMor.comp_toLoc_eq q g q' hq) y
  calc
    (FibredCategoryMor.fiberFunctor G V').map (κS.hom.toNatTrans.app (model I).1) ≫
        cg.inv ≫
          (M.map cf.inv ≫ M.map (mf.map (model I).2.hom) ≫
              M.map (κIf.inv.toNatTrans.app y)) ≫
        κq.inv.toNatTrans.app y =
      ((FibredCategoryMor.fiberFunctor G V').map (κS.hom.toNatTrans.app (model I).1) ≫
        cg.inv ≫ M.map cf.inv) ≫ M.map (mf.map (model I).2.hom) ≫
          M.map (κIf.inv.toNatTrans.app y) ≫ κq.inv.toNatTrans.app y := by
        simp only [Category.assoc]
    _ =
      (cgf.inv ≫
          κS'.hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1)) ≫
        M.map (mf.map (model I).2.hom) ≫
          M.map (κIf.inv.toNatTrans.app y) ≫ κq.inv.toNatTrans.app y := by
        rw [hGcomp]
        rfl
    _ =
      (cgf.inv ≫
        (κS'.hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) ≫
          M.map (mf.map (model I).2.hom))) ≫
          M.map (κIf.inv.toNatTrans.app y) ≫ κq.inv.toNatTrans.app y := by
        simp only [Category.assoc]
    _ =
      (cgf.inv ≫
        (((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
            (model I).2.hom ≫
          κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y))) ≫
          M.map (κIf.inv.toNatTrans.app y) ≫ κq.inv.toNatTrans.app y := by
        exact congrArg
          (fun t =>
            (cgf.inv ≫ t) ≫ M.map (κIf.inv.toNatTrans.app y) ≫
              κq.inv.toNatTrans.app y)
          hnat
    _ =
      cgf.inv ≫
        ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
            (model I).2.hom ≫
          (κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
            (M.map (κIf.inv.toNatTrans.app y) ≫ κq.inv.toNatTrans.app y)) := by
        simp only [Category.assoc]
    _ =
      cgf.inv ≫
        ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
            (model I).2.hom ≫
          (κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
            (κS'.inv.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
              κIgf.inv.toNatTrans.app y)) := by
        simpa only [Category.assoc] using
          congrArg
            (fun t =>
              cgf.inv ≫
                ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
                  (model I).2.hom ≫
                κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫ t)
            hassoc
    _ =
      cgf.inv ≫
        ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
            (model I).2.hom ≫
          κIgf.inv.toNatTrans.app y := by
        have hκS'cancel' :
            κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
                κS'.inv.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) =
              𝟙 _ :=
          Cat.Hom.hom_inv_id_toNatTrans_app κS'
            (I.f ^*[canonicalPullbackChoice S'.p] y)
        calc
          cgf.inv ≫
              ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
                  (model I).2.hom ≫
                κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
                  κS'.inv.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
                    κIgf.inv.toNatTrans.app y =
            (cgf.inv ≫
              ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
                  (model I).2.hom) ≫
                (κS'.hom.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
                  κS'.inv.toNatTrans.app (I.f ^*[canonicalPullbackChoice S'.p] y)) ≫
                    κIgf.inv.toNatTrans.app y := by
            simp only [Category.assoc]
          _ =
            (cgf.inv ≫
              ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
                  (model I).2.hom) ≫
                𝟙 _ ≫
                  κIgf.inv.toNatTrans.app y := by
            exact congrArg
              (fun t =>
                (cgf.inv ≫
                  ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
                    (model I).2.hom) ≫ t ≫ κIgf.inv.toNatTrans.app y)
              hκS'cancel'
          _ =
            cgf.inv ≫
              ((canonicalFiberPseudofunctor S'.p).map gfI.op.toLoc).toFunctor.map
                  (model I).2.hom ≫
                κIgf.inv.toNatTrans.app y := by
            simp only [Category.assoc, Category.id_comp]

/-- Helper for Chap08 Lemma 8 8 3: the overlap morphism in `X` determined by two local source
models of the same target object. -/
noncomputable def stackificationLiftObjectTransition
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) {I₁ I₂ : Scover.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor F I₁.Y).obj (model I₁).1) ⟶
      ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor F I₂.Y).obj (model I₂).1) :=
  (FibredCategoryMor.pullbackComparison F f₁ (model I₁).1).hom ≫
    stackificationLiftHomExtensionFiberMap X G hG F
      (f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1)
      (f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1)
      ((stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
          q I₁ f₁ hf₁).hom ≫
        (stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
          q I₂ f₂ hf₂).inv) ≫
    (FibredCategoryMor.pullbackComparison F f₂ (model I₂).1).inv

/-- Helper for Chap08 Lemma 8 8 3: the object-gluing transition is the identity on a single
cover branch. -/
private theorem stackificationLiftObjectTransition_hom_self
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) {I : Scover.Arrow}
    (f : V ⟶ I.Y) (hf : f ≫ I.f = q) :
    stackificationLiftObjectTransition X G hG F y Scover model q f f hf hf =
      𝟙 (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor F I.Y).obj (model I).1)) := by
  dsimp only [stackificationLiftObjectTransition]
  rw [Iso.hom_inv_id]
  rw [stackificationLiftHomExtensionFiberMap_id]
  let e := FibredCategoryMor.pullbackComparison F f (model I).1
  change e.hom ≫ 𝟙 _ ≫ e.inv = 𝟙 _
  rw [Category.id_comp]
  exact e.hom_inv_id

/-- Helper for Chap08 Lemma 8 8 3: public wrapper for the object-gluing transition identity
law on a single cover branch. -/
theorem stackificationLiftObjectTransition_self
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) {I : Scover.Arrow}
    (f : V ⟶ I.Y) (hf : f ≫ I.f = q) :
    stackificationLiftObjectTransition X G hG F y Scover model q f f hf hf =
      𝟙 (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor F I.Y).obj (model I).1)) :=
  stackificationLiftObjectTransition_hom_self X G hG F y Scover model q f hf

/-- Helper for Chap08 Lemma 8 8 3: the object-gluing transition satisfies the cocycle law once
the Hom-extension fiber map is known to preserve composition. -/
private theorem stackificationLiftObjectTransition_hom_comp_of_fiberMap_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (hmap_comp :
      ∀ ⦃U : C⦄ ⦃x y z : S.p.Fiber U⦄
        (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
          ((FibredCategoryMor.fiberFunctor G U).obj y))
        (β : ((FibredCategoryMor.fiberFunctor G U).obj y) ⟶
          ((FibredCategoryMor.fiberFunctor G U).obj z)),
        stackificationLiftHomExtensionFiberMap X G hG F x z (α ≫ β) =
          stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
            stackificationLiftHomExtensionFiberMap X G hG F y z β)
    {U V : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) {I₁ I₂ I₃ : Scover.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q) :
    stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂ ≫
        stackificationLiftObjectTransition X G hG F y Scover model q f₂ f₃ hf₂ hf₃ =
      stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₃ hf₁ hf₃ := by
  let c₁ := FibredCategoryMor.pullbackComparison F f₁ (model I₁).1
  let c₂ := FibredCategoryMor.pullbackComparison F f₂ (model I₂).1
  let c₃ := FibredCategoryMor.pullbackComparison F f₃ (model I₃).1
  let e₁ :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q I₁ f₁ hf₁
  let e₂ :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q I₂ f₂ hf₂
  let e₃ :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q I₃ f₃ hf₃
  let m₁₂ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1)
      (f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1)
      (e₁.hom ≫ e₂.inv)
  let m₂₃ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1)
      (f₃ ^*[canonicalPullbackChoice S.p] (model I₃).1)
      (e₂.hom ≫ e₃.inv)
  let m₁₃ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1)
      (f₃ ^*[canonicalPullbackChoice S.p] (model I₃).1)
      (e₁.hom ≫ e₃.inv)
  have hmid :
      m₁₂ ≫ m₂₃ = m₁₃ := by
    have hcomp :=
      hmap_comp (x := f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1)
        (y := f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1)
        (z := f₃ ^*[canonicalPullbackChoice S.p] (model I₃).1)
        (e₁.hom ≫ e₂.inv) (e₂.hom ≫ e₃.inv)
    dsimp only [m₁₂, m₂₃, m₁₃]
    rw [← hcomp]
    congr 1
    calc
      (e₁.hom ≫ e₂.inv) ≫ e₂.hom ≫ e₃.inv =
        e₁.hom ≫ (e₂.inv ≫ e₂.hom) ≫ e₃.inv := by
          simp only [Category.assoc]
      _ = e₁.hom ≫ e₃.inv := by
          rw [e₂.inv_hom_id]
          simp only [Category.id_comp]
  dsimp only [stackificationLiftObjectTransition]
  change (c₁.hom ≫ m₁₂ ≫ c₂.inv) ≫ (c₂.hom ≫ m₂₃ ≫ c₃.inv) =
    c₁.hom ≫ m₁₃ ≫ c₃.inv
  calc
    (c₁.hom ≫ m₁₂ ≫ c₂.inv) ≫ (c₂.hom ≫ m₂₃ ≫ c₃.inv) =
      c₁.hom ≫ m₁₂ ≫ (c₂.inv ≫ c₂.hom) ≫ m₂₃ ≫ c₃.inv := by
        simp only [Category.assoc]
    _ = c₁.hom ≫ m₁₂ ≫ 𝟙 _ ≫ m₂₃ ≫ c₃.inv := by
        rw [c₂.inv_hom_id]
    _ = c₁.hom ≫ (m₁₂ ≫ m₂₃) ≫ c₃.inv := by
        simp only [Category.id_comp, Category.assoc]
    _ = c₁.hom ≫ m₁₃ ≫ c₃.inv := by
        rw [hmid]

/-- Helper for Chap08 Lemma 8 8 3: the object-gluing transition satisfies the cocycle law. -/
private theorem stackificationLiftObjectTransition_hom_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) {I₁ I₂ I₃ : Scover.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q) :
    stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂ ≫
        stackificationLiftObjectTransition X G hG F y Scover model q f₂ f₃ hf₂ hf₃ =
      stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₃ hf₁ hf₃ := by
  -- The cocycle is the formal composition law for the Hom extension applied to the two
  -- transition isomorphisms over the common overlap.
  exact
    stackificationLiftObjectTransition_hom_comp_of_fiberMap_comp X G hG F
      (stackificationLiftHomExtensionFiberMap_comp X G hG F)
      y Scover model q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- Helper for Chap08 Lemma 8 8 3: public wrapper for the object-gluing transition cocycle
law. -/
theorem stackificationLiftObjectTransition_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (q : V ⟶ U) {I₁ I₂ I₃ : Scover.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q) :
    stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂ ≫
        stackificationLiftObjectTransition X G hG F y Scover model q f₂ f₃ hf₂ hf₃ =
      stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₃ hf₁ hf₃ :=
  stackificationLiftObjectTransition_hom_comp X G hG F y Scover model q
    f₁ f₂ f₃ hf₁ hf₂ hf₃

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: the object-gluing transition is compatible with pullback
to a further overlap. -/
private theorem stackificationLiftObjectTransition_pullHom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V V' : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U)
    (hq : g ≫ q = q') {I₁ I₂ : Scover.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      stackificationLiftObjectTransition X G hG F y Scover model q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let x₁ : S.p.Fiber V := f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1
  let x₂ : S.p.Fiber V := f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1
  let x₁' : S.p.Fiber V' := gf₁ ^*[canonicalPullbackChoice S.p] (model I₁).1
  let x₂' : S.p.Fiber V' := gf₂ ^*[canonicalPullbackChoice S.p] (model I₂).1
  let gx₁ : S.p.Fiber V' := g ^*[canonicalPullbackChoice S.p] x₁
  let gx₂ : S.p.Fiber V' := g ^*[canonicalPullbackChoice S.p] x₂
  let MX := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let MG := ((canonicalFiberPseudofunctor S'.p).map g.op.toLoc).toFunctor
  let κX₁ :=
    mapCompAppIso X.p f₁ g gf₁
      (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)
      ((FibredCategoryMor.fiberFunctor F I₁.Y).obj (model I₁).1)
  let κX₂ :=
    mapCompAppIso X.p f₂ g gf₂
      (FibredCategoryMor.comp_toLoc_eq f₂ g gf₂ hgf₂)
      ((FibredCategoryMor.fiberFunctor F I₂.Y).obj (model I₂).1)
  let κS₁ :=
    mapCompAppIso S.p f₁ g gf₁
      (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁) (model I₁).1
  let κS₂ :=
    mapCompAppIso S.p f₂ g gf₂
      (FibredCategoryMor.comp_toLoc_eq f₂ g gf₂ hgf₂) (model I₂).1
  let κq :=
    mapCompAppIso S'.p q g q'
      (FibredCategoryMor.comp_toLoc_eq q g q' hq) y
  let cF₁ := FibredCategoryMor.pullbackComparison F f₁ (model I₁).1
  let cF₂ := FibredCategoryMor.pullbackComparison F f₂ (model I₂).1
  let cFg₁ := FibredCategoryMor.pullbackComparison F g x₁
  let cFg₂ := FibredCategoryMor.pullbackComparison F g x₂
  let cFgf₁ := FibredCategoryMor.pullbackComparison F gf₁ (model I₁).1
  let cFgf₂ := FibredCategoryMor.pullbackComparison F gf₂ (model I₂).1
  let cGg₁ := FibredCategoryMor.pullbackComparison G g x₁
  let cGg₂ := FibredCategoryMor.pullbackComparison G g x₂
  let e₁ :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q I₁ f₁ hf₁
  let e₂ :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q I₂ f₂ hf₂
  let e₁' :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q' I₁ gf₁ (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
  let e₂' :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q' I₂ gf₂ (by rw [← hq, ← hgf₂, Category.assoc, hf₂])
  let α := e₁.hom ≫ e₂.inv
  let αpull : ((FibredCategoryMor.fiberFunctor G V').obj gx₁) ⟶
      ((FibredCategoryMor.fiberFunctor G V').obj gx₂) :=
    cGg₁.inv ≫ MG.map α ≫ cGg₂.hom
  let m :=
    stackificationLiftHomExtensionFiberMap X G hG F x₁ x₂ α
  let mpull :=
    stackificationLiftHomExtensionFiberMap X G hG F gx₁ gx₂ αpull
  let m' :=
    stackificationLiftHomExtensionFiberMap X G hG F x₁' x₂'
      (e₁'.hom ≫ e₂'.inv)
  have h_m_pull :
      MX.map m = cFg₁.hom ≫ mpull ≫ cFg₂.inv := by
    have hsrc :
        cGg₁.hom ≫ αpull ≫ cGg₂.inv = MG.map α := by
      dsimp only [αpull]
      calc
        cGg₁.hom ≫ (cGg₁.inv ≫ MG.map α ≫ cGg₂.hom) ≫ cGg₂.inv =
            (cGg₁.hom ≫ cGg₁.inv) ≫ MG.map α ≫ (cGg₂.hom ≫ cGg₂.inv) := by
              simp only [Category.assoc]
        _ = MG.map α := by
              rw [cGg₁.hom_inv_id, cGg₂.hom_inv_id]
              simpa only [Category.id_comp] using Category.comp_id (MG.map α)
    have hmap :=
      stackificationLiftHomExtensionFiberMap_pullback X G hG F g
        (x := x₁) (y := x₂) α
    have happ :=
      stackificationLiftHomExtension_app_pullbackComparison X G hG F g
        (x := x₁) (y := x₂) αpull
    calc
      MX.map m =
          (stackificationLiftHomExtension X G hG F x₁ x₂).app
            (op (Over.mk g)) (MG.map α) := hmap.symm
      _ =
          (stackificationLiftHomExtension X G hG F x₁ x₂).app
            (op (Over.mk g)) (cGg₁.hom ≫ αpull ≫ cGg₂.inv) := by
            rw [hsrc]
      _ = cFg₁.hom ≫ mpull ≫ cFg₂.inv := happ
  have he₁_hom :
      (FibredCategoryMor.fiberFunctor G V').map κS₁.hom ≫
          cGg₁.inv ≫ MG.map e₁.hom ≫ κq.inv =
        e₁'.hom := by
    have h := congrArg (fun t : _ ≅ _ => t.hom)
      (stackificationLiftObjectModelPullbackIso_pullback
        (J := J) G y Scover model g q q' hq I₁ f₁ hf₁ gf₁ hgf₁)
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, mapCompAppIso,
      Category.assoc, κS₁, cGg₁, MG, e₁, e₁', κq] using h
  have he₂_inv :
      κq.hom ≫ MG.map e₂.inv ≫ cGg₂.hom ≫
          (FibredCategoryMor.fiberFunctor G V').map κS₂.inv =
        e₂'.inv := by
    have h := congrArg (fun t : _ ≅ _ => t.inv)
      (stackificationLiftObjectModelPullbackIso_pullback
        (J := J) G y Scover model g q q' hq I₂ f₂ hf₂ gf₂ hgf₂)
    simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, mapCompAppIso,
      Category.assoc, κS₂, cGg₂, MG, e₂, e₂', κq] using h
  have hαpull :
      (FibredCategoryMor.fiberFunctor G V').map κS₁.hom ≫ αpull ≫
          (FibredCategoryMor.fiberFunctor G V').map κS₂.inv =
        e₁'.hom ≫ e₂'.inv := by
    calc
      (FibredCategoryMor.fiberFunctor G V').map κS₁.hom ≫ αpull ≫
          (FibredCategoryMor.fiberFunctor G V').map κS₂.inv =
        (FibredCategoryMor.fiberFunctor G V').map κS₁.hom ≫
          cGg₁.inv ≫ MG.map e₁.hom ≫ MG.map e₂.inv ≫
          cGg₂.hom ≫ (FibredCategoryMor.fiberFunctor G V').map κS₂.inv := by
            dsimp only [αpull, α]
            rw [Functor.map_comp]
            simp only [Category.assoc]
      _ =
        ((FibredCategoryMor.fiberFunctor G V').map κS₁.hom ≫
            cGg₁.inv ≫ MG.map e₁.hom ≫ κq.inv) ≫
          (κq.hom ≫ MG.map e₂.inv ≫ cGg₂.hom ≫
            (FibredCategoryMor.fiberFunctor G V').map κS₂.inv) := by
            let A :=
              (FibredCategoryMor.fiberFunctor G V').map κS₁.hom ≫
                cGg₁.inv ≫ MG.map e₁.hom
            let B :=
              MG.map e₂.inv ≫ cGg₂.hom ≫
                (FibredCategoryMor.fiberFunctor G V').map κS₂.inv
            have hinsert := congrArg (fun t => A ≫ t ≫ B) κq.inv_hom_id.symm
            have hunit : A ≫ 𝟙 _ ≫ B = A ≫ B := by
              simpa only [Category.assoc] using
                congrArg (fun t => A ≫ t) (Category.id_comp B)
            simpa only [A, B, Category.assoc] using hunit.symm.trans hinsert
      _ = e₁'.hom ≫ e₂'.inv := by
            exact congrArg₂ (fun a b => a ≫ b) he₁_hom he₂_inv
  have hmid :
      (FibredCategoryMor.fiberFunctor F V').map κS₁.hom ≫ mpull ≫
          (FibredCategoryMor.fiberFunctor F V').map κS₂.inv =
        m' := by
    have htransport :=
      stackificationLiftHomExtensionFiberMap_transport_of_sourceIso X G hG F
        κS₁ κS₂ αpull
    dsimp only [mpull, m']
    rw [← htransport]
    exact congrArg
      (stackificationLiftHomExtensionFiberMap X G hG F x₁' x₂') hαpull
  have hleft :
      κX₁.hom ≫ MX.map cF₁.hom ≫ cFg₁.hom =
        cFgf₁.hom ≫ (FibredCategoryMor.fiberFunctor F V').map κS₁.hom := by
    simpa only [κX₁, MX, cF₁, cFg₁, cFgf₁, κS₁, mapCompAppIso] using
      pullbackComparison_mapComp_hom_cocycle F f₁ g gf₁ hgf₁ (model I₁).1
  have hright :
      cFg₂.inv ≫ MX.map cF₂.inv ≫ κX₂.inv =
        (FibredCategoryMor.fiberFunctor F V').map κS₂.inv ≫ cFgf₂.inv := by
    simpa only [κX₂, MX, cF₂, cFg₂, cFgf₂, κS₂, mapCompAppIso] using
      pullbackComparison_mapComp_inv_cocycle F f₂ g gf₂ hgf₂ (model I₂).1
  have hmap_transition :
      MX.map (cF₁.hom ≫ m ≫ cF₂.inv) =
        MX.map cF₁.hom ≫ MX.map m ≫ MX.map cF₂.inv := by
    rw [Functor.map_comp, Functor.map_comp]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    stackificationLiftObjectTransition]
  change κX₁.hom ≫ MX.map (cF₁.hom ≫ m ≫ cF₂.inv) ≫ κX₂.inv =
    cFgf₁.hom ≫ m' ≫ cFgf₂.inv
  calc
    κX₁.hom ≫ MX.map (cF₁.hom ≫ m ≫ cF₂.inv) ≫ κX₂.inv =
        κX₁.hom ≫ MX.map cF₁.hom ≫ MX.map m ≫ MX.map cF₂.inv ≫ κX₂.inv := by
          rw [hmap_transition]
          simp only [Category.assoc]
    _ =
        κX₁.hom ≫ MX.map cF₁.hom ≫
          (cFg₁.hom ≫ mpull ≫ cFg₂.inv) ≫
          MX.map cF₂.inv ≫ κX₂.inv := by
          rw [h_m_pull]
    _ =
        (κX₁.hom ≫ MX.map cF₁.hom ≫ cFg₁.hom) ≫
          mpull ≫ (cFg₂.inv ≫ MX.map cF₂.inv ≫ κX₂.inv) := by
          simp only [Category.assoc]
    _ =
        (cFgf₁.hom ≫ (FibredCategoryMor.fiberFunctor F V').map κS₁.hom) ≫
          mpull ≫
          ((FibredCategoryMor.fiberFunctor F V').map κS₂.inv ≫ cFgf₂.inv) := by
          rw [hleft, hright]
    _ =
        cFgf₁.hom ≫
          ((FibredCategoryMor.fiberFunctor F V').map κS₁.hom ≫ mpull ≫
            (FibredCategoryMor.fiberFunctor F V').map κS₂.inv) ≫
          cFgf₂.inv := by
          simp only [Category.assoc]
    _ = cFgf₁.hom ≫ m' ≫ cFgf₂.inv := by
          rw [hmid]

/-- Helper for Chap08 Lemma 8 8 3: public wrapper for compatibility of object-gluing transition
morphisms with pullback to a further overlap. -/
theorem stackificationLiftObjectTransition_pullHom_public
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V V' : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U)
    (hq : g ≫ q = q') {I₁ I₂ : Scover.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      stackificationLiftObjectTransition X G hG F y Scover model q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) :=
  stackificationLiftObjectTransition_pullHom X G hG F y Scover model
    g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- Helper for Chap08 Lemma 8 8 3: once the object-transition morphisms satisfy the two
descent-data laws, they package as fixed-cover descent data in the target stack. -/
private noncomputable def stackificationLiftObjectDescentDataOfLaws
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hpull :
      ∀ ⦃V' V : C⦄ (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U)
        (hq : g ≫ q = q') ⦃I₁ I₂ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
        (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
        (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂ =
          stackificationLiftObjectTransition X G hG F y Scover model q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂]))
    (hcomp :
      ∀ ⦃V : C⦄ (q : V ⟶ U) ⦃I₁ I₂ I₃ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
        stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂ ≫
            stackificationLiftObjectTransition X G hG F y Scover model q f₂ f₃ hf₂ hf₃ =
          stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₃ hf₁ hf₃) :
    (canonicalFiberPseudofunctor X.p).DescentData (fun I : Scover.Arrow ↦ I.f) where
  obj I := (FibredCategoryMor.fiberFunctor F I.Y).obj (model I).1
  hom := fun {_V} q {_I₁ _I₂} f₁ f₂ hf₁ hf₂ ↦
    stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂
  pullHom_hom := fun {V' V} g q q' hq {I₁ I₂} f₁ f₂ hf₁ hf₂
      gf₁ gf₂ hgf₁ hgf₂ ↦
    hpull (V' := V') (V := V) g q q' hq (I₁ := I₁) (I₂ := I₂)
      f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self := fun {_V} q {_I} f hf ↦
    stackificationLiftObjectTransition_hom_self X G hG F y Scover model q f hf
  hom_comp := fun {V} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
    hcomp (V := V) q (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
      f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- Helper for Chap08 Lemma 8 8 3: object descent data obtained from the transition laws is
effective because the target is a stack. -/
private theorem stackificationLiftObjectGlued_exists_of_laws
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hpull :
      ∀ ⦃V' V : C⦄ (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U)
        (hq : g ≫ q = q') ⦃I₁ I₂ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
        (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
        (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂ =
          stackificationLiftObjectTransition X G hG F y Scover model q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂]))
    (hcomp :
      ∀ ⦃V : C⦄ (q : V ⟶ U) ⦃I₁ I₂ I₃ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
        stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂ ≫
            stackificationLiftObjectTransition X G hG F y Scover model q f₂ f₃ hf₂ hf₃ =
          stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₃ hf₁ hf₃) :
    ∃ Hy : X.p.Fiber U,
      Nonempty
        (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : Scover.Arrow ↦ I.f)).obj Hy ≅
            stackificationLiftObjectDescentDataOfLaws X G hG F y Scover model hpull hcomp) := by
  exact
    stack_cover_obj_glue (J := J) X Scover
      (stackificationLiftObjectDescentDataOfLaws X G hG F y Scover model hpull hcomp)

/-- Helper for Chap08 Lemma 8 8 3: object descent reduces to the pullback law for transitions
and functoriality of the Hom-extension fiber map. -/
private theorem stackificationLiftObjectGlued_exists_of_pullHom_and_fiberMap_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (hmap_comp :
      ∀ ⦃U : C⦄ ⦃x y z : S.p.Fiber U⦄
        (α : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
          ((FibredCategoryMor.fiberFunctor G U).obj y))
        (β : ((FibredCategoryMor.fiberFunctor G U).obj y) ⟶
          ((FibredCategoryMor.fiberFunctor G U).obj z)),
        stackificationLiftHomExtensionFiberMap X G hG F x z (α ≫ β) =
          stackificationLiftHomExtensionFiberMap X G hG F x y α ≫
            stackificationLiftHomExtensionFiberMap X G hG F y z β)
    {U : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hpull :
      ∀ ⦃V' V : C⦄ (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U)
        (hq : g ≫ q = q') ⦃I₁ I₂ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
        (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
        (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂ =
          stackificationLiftObjectTransition X G hG F y Scover model q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) :
    ∃ Hy : X.p.Fiber U,
      Nonempty
        (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : Scover.Arrow ↦ I.f)).obj Hy ≅
            stackificationLiftObjectDescentDataOfLaws X G hG F y Scover model hpull
              (fun {V} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
                stackificationLiftObjectTransition_hom_comp_of_fiberMap_comp
                  X G hG F hmap_comp y Scover model (V := V) q
                  (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
                  f₁ f₂ f₃ hf₁ hf₂ hf₃)) := by
  exact
    stackificationLiftObjectGlued_exists_of_laws X G hG F y Scover model hpull
      (fun {V} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
        stackificationLiftObjectTransition_hom_comp_of_fiberMap_comp
          X G hG F hmap_comp y Scover model (V := V) q
          (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
          f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Helper for Chap08 Lemma 8 8 3: object descent reduces to the pullback law for transitions. -/
private theorem stackificationLiftObjectGlued_exists_of_pullHom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U)
    (Scover : J.Cover U)
    (model : ∀ I : Scover.Arrow, Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p] y)
    (hpull :
      ∀ ⦃V' V : C⦄ (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U)
        (hq : g ≫ q = q') ⦃I₁ I₂ : Scover.Arrow⦄
        (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
        (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
        (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (stackificationLiftObjectTransition X G hG F y Scover model q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂ =
          stackificationLiftObjectTransition X G hG F y Scover model q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) :
    ∃ Hy : X.p.Fiber U,
      Nonempty
        (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : Scover.Arrow ↦ I.f)).obj Hy ≅
            stackificationLiftObjectDescentDataOfLaws X G hG F y Scover model hpull
              (fun {V} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
                stackificationLiftObjectTransition_hom_comp
                  X G hG F y Scover model (V := V) q
                  (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
                  f₁ f₂ f₃ hf₁ hf₂ hf₃)) := by
  -- The Hom-extension composition law is now an internal helper, so only pullback
  -- compatibility remains as external data for object descent.
  exact
    stackificationLiftObjectGlued_exists_of_laws X G hG F y Scover model hpull
      (fun {V} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
        stackificationLiftObjectTransition_hom_comp
          X G hG F y Scover model (V := V) q
          (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
          f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Helper for Chap08 Lemma 8 8 3: the canonical object-descent data attached to a target-fiber
object and the chosen local source models supplied by the stackification. -/
noncomputable def stackificationLiftObjectDescentData
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U) :
    (canonicalFiberPseudofunctor X.p).DescentData
      (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f) :=
  stackificationLiftObjectDescentDataOfLaws X G hG F y
    (stackificationLiftObjectCover (J := J) G hG y)
    (stackificationLiftObjectModel (J := J) G hG y)
    (fun {V' V} g q q' hq {I₁ I₂} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
      stackificationLiftObjectTransition_pullHom X G hG F y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        (V' := V') (V := V) (I₁ := I₁) (I₂ := I₂)
        g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
    (fun {V} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
      stackificationLiftObjectTransition_hom_comp X G hG F y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        (V := V) q (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
        f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Helper for Chap08 Lemma 8 8 3: the chosen object-descent data is effective in the target
stack. -/
private theorem stackificationLiftObjectGlued_exists
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U) :
    ∃ Hy : X.p.Fiber U,
      Nonempty
        (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)).obj Hy ≅
            stackificationLiftObjectDescentData X G hG F y) := by
  exact
    stackificationLiftObjectGlued_exists_of_pullHom X G hG F y
      (stackificationLiftObjectCover (J := J) G hG y)
      (stackificationLiftObjectModel (J := J) G hG y)
      (fun {V' V} g q q' hq {I₁ I₂} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
        stackificationLiftObjectTransition_pullHom X G hG F y
          (stackificationLiftObjectCover (J := J) G hG y)
          (stackificationLiftObjectModel (J := J) G hG y)
          g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)

/-- Helper for Chap08 Lemma 8 8 3: the chosen descended target object attached to a target-fiber
object of `S'`. -/
noncomputable def stackificationLiftObjectGlued
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U) : X.p.Fiber U :=
  Classical.choose (stackificationLiftObjectGlued_exists X G hG F y)

/-- Helper for Chap08 Lemma 8 8 3: the chosen descended object restricts to the object-descent
data built from local source models. -/
noncomputable def stackificationLiftObjectGluedIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U) :
    ((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)).obj
        (stackificationLiftObjectGlued X G hG F y) ≅
      stackificationLiftObjectDescentData X G hG F y :=
  Classical.choice
    (Classical.choose_spec (stackificationLiftObjectGlued_exists X G hG F y))

/-- Helper for Chap08 Lemma 8 8 3: on a chosen cover branch, the descended object restricts to
the image under `F` of the chosen source model. -/
noncomputable def stackificationLiftObjectGluedLocalIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U)
    (I : (stackificationLiftObjectCover (J := J) G hG y).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
        (stackificationLiftObjectGlued X G hG F y) ≅
      (FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftObjectModel (J := J) G hG y I).1 where
  hom := (stackificationLiftObjectGluedIso X G hG F y).hom.hom I
  inv := (stackificationLiftObjectGluedIso X G hG F y).inv.hom I
  hom_inv_id := by
    let D :=
      ((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)).obj
          (stackificationLiftObjectGlued X G hG F y)
    let e := stackificationLiftObjectGluedIso X G hG F y
    have h := congrArg (fun η : D ⟶ D => Pseudofunctor.DescentData.Hom.hom η I)
      e.hom_inv_id
    simpa only [Pseudofunctor.DescentData.comp_hom,
      Pseudofunctor.DescentData.id_hom] using h
  inv_hom_id := by
    let D := stackificationLiftObjectDescentData X G hG F y
    let e := stackificationLiftObjectGluedIso X G hG F y
    have h := congrArg (fun η : D ⟶ D => Pseudofunctor.DescentData.Hom.hom η I)
      e.inv_hom_id
    simpa only [Pseudofunctor.DescentData.comp_hom,
      Pseudofunctor.DescentData.id_hom] using h

/-- Helper for Chap08 Lemma 8 8 3: the local isomorphisms from the chosen descended object to
the chosen source-model objects satisfy the descent-data commutativity law. -/
theorem stackificationLiftObjectGluedLocalIso_comm
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (q : V ⟶ U)
    {I₁ I₂ : (stackificationLiftObjectCover (J := J) G hG y).Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
        (stackificationLiftObjectGluedLocalIso X G hG F y I₁).hom ≫
      stackificationLiftObjectTransition X G hG F y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        q f₁ f₂ hf₁ hf₂ =
    ((((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)).obj
        (stackificationLiftObjectGlued X G hG F y)).hom q f₁ f₂ hf₁ hf₂) ≫
      ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
        (stackificationLiftObjectGluedLocalIso X G hG F y I₂).hom := by
  -- This is exactly the commutativity field of the descent-data morphism underlying the chosen
  -- effectiveness isomorphism, restated using the local-iso wrapper.
  let e := stackificationLiftObjectGluedIso X G hG F y
  exact e.hom.comm q f₁ f₂ hf₁ hf₂

/-- Helper for Chap08 Lemma 8 8 3: the inverse local isomorphisms from the chosen source-model
objects back to the descended object satisfy the dual descent-data commutativity law. -/
theorem stackificationLiftObjectGluedLocalIso_inv_comm
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (q : V ⟶ U)
    {I₁ I₂ : (stackificationLiftObjectCover (J := J) G hG y).Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
        (stackificationLiftObjectGluedLocalIso X G hG F y I₁).inv ≫
      ((((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)).obj
          (stackificationLiftObjectGlued X G hG F y)).hom q f₁ f₂ hf₁ hf₂) =
    stackificationLiftObjectTransition X G hG F y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
        (stackificationLiftObjectGluedLocalIso X G hG F y I₂).inv := by
  -- Read the same compatibility from the inverse descent-data morphism; this direction is the
  -- one used when local formulas are glued back to a global morphism.
  let e := stackificationLiftObjectGluedIso X G hG F y
  exact e.inv.comm q f₁ f₂ hf₁ hf₂

/-- Helper for Chap08 Lemma 8 8 3: on a local-essential-image cover of a literal `G`-image
object, the obvious pullback of `F x` is identified with the chosen local `F`-model. -/
noncomputable def stackificationLiftObjectSourceImageLocalIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U)
    (I : (stackificationLiftObjectCover (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G U).obj x)).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor F U).obj x) ≅
      (FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftObjectModel (J := J) G hG
          ((FibredCategoryMor.fiberFunctor G U).obj x) I).1 := by
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let xI := (stackificationLiftObjectModel (J := J) G hG y I).1
  let eI := (stackificationLiftObjectModel (J := J) G hG y I).2
  let px : S.p.Fiber I.Y := I.f ^*[canonicalPullbackChoice S.p] x
  let cGx := FibredCategoryMor.pullbackComparison G I.f x
  let cFx := FibredCategoryMor.pullbackComparison F I.f x
  let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj px) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) :=
    cGx.inv ≫ eI.inv
  let β : ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj px) :=
    eI.hom ≫ cGx.hom
  let m :=
    stackificationLiftHomExtensionFiberMap X G hG F px xI α
  let n :=
    stackificationLiftHomExtensionFiberMap X G hG F xI px β
  refine
    { hom := cFx.hom ≫ m
      inv := n ≫ cFx.inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- The two middle Hom-extension arrows compose to the extension of the identity, hence the
    -- outer pullback comparison cancels.
    have hαβ : α ≫ β = 𝟙 ((FibredCategoryMor.fiberFunctor G I.Y).obj px) := by
      dsimp only [α, β]
      calc
        (cGx.inv ≫ eI.inv) ≫ eI.hom ≫ cGx.hom =
            cGx.inv ≫ (eI.inv ≫ eI.hom) ≫ cGx.hom := by
              simp only [Category.assoc]
        _ = cGx.inv ≫ cGx.hom := by
              rw [eI.inv_hom_id]
              simp only [Category.id_comp]
        _ = 𝟙 _ := cGx.inv_hom_id
    have hmn : m ≫ n = 𝟙 ((FibredCategoryMor.fiberFunctor F I.Y).obj px) := by
      dsimp only [m, n]
      rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F α β]
      rw [hαβ]
      exact stackificationLiftHomExtensionFiberMap_id X G hG F px
    calc
      (cFx.hom ≫ m) ≫ n ≫ cFx.inv =
          cFx.hom ≫ (m ≫ n) ≫ cFx.inv := by
            simp only [Category.assoc]
      _ = cFx.hom ≫ 𝟙 _ ≫ cFx.inv := by
            rw [hmn]
      _ = 𝟙 _ := by
            calc
              cFx.hom ≫ 𝟙 _ ≫ cFx.inv = cFx.hom ≫ cFx.inv := by
                rw [Category.id_comp]
              _ = 𝟙 _ := cFx.hom_inv_id
  · -- The reverse composite is identical, with the source-model isomorphism cancelled in the
    -- opposite order.
    have hβα : β ≫ α = 𝟙 ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) := by
      dsimp only [α, β]
      calc
        (eI.hom ≫ cGx.hom) ≫ cGx.inv ≫ eI.inv =
            eI.hom ≫ (cGx.hom ≫ cGx.inv) ≫ eI.inv := by
              simp only [Category.assoc]
        _ = eI.hom ≫ eI.inv := by
              rw [cGx.hom_inv_id]
              simp only [Category.id_comp]
        _ = 𝟙 _ := eI.hom_inv_id
    have hnm : n ≫ m = 𝟙 ((FibredCategoryMor.fiberFunctor F I.Y).obj xI) := by
      dsimp only [m, n]
      rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F β α]
      rw [hβα]
      exact stackificationLiftHomExtensionFiberMap_id X G hG F xI
    calc
      (n ≫ cFx.inv) ≫ cFx.hom ≫ m =
          n ≫ (cFx.inv ≫ cFx.hom) ≫ m := by
            simp only [Category.assoc]
      _ = n ≫ m := by
            rw [cFx.inv_hom_id]
            rw [Category.id_comp]
      _ = 𝟙 _ := hnm

end

end CategoryTheory
