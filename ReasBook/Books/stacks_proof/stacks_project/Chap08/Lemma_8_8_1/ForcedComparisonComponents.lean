import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.FiberTransport
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.CoverwiseHomLift
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.CoverDescent
import Mathlib.Tactic.StacksAttribute

universe u v uD vD uY vY

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

/-- Helper for Lemma 8.8.1: precomposition by a `W`-morphism is injective on maps into a sheaf.
This consumes only the defining localization property of `W`, so it avoids any
`WEqualsLocallyBijective` universe hypothesis. -/
private theorem W_precomp_ext_to_sheaf
    {D : Type uD} [Category.{vD} D]
    {P Q R : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (hf : J.W f)
    (hR : Presheaf.IsSheaf J R)
    {g₁ g₂ : Q ⟶ R}
    (h : f ≫ g₁ = f ≫ g₂) :
    g₁ = g₂ := by
  exact (hf R hR).1 h

/-- Helper for Lemma 8.8.1: an arbitrary `2`-morphism between fibred-category morphisms restricts
to a morphism between the induced fiber functors over a fixed base object. -/
private noncomputable def basedFiberFunctorHom
    {X Y : FibredCategoryOver C} {F G : X ⟶ Y}
    (η : F ⟶ G) (U : C) (x : X.p.Fiber U) :
    ((FibredCategoryMor.fiberFunctor F U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G U).obj x) :=
  ⟨(η.hom.hom).toNatTrans.app x.1, (η.hom.hom).isHomLift x.2⟩

/-- Helper for Lemma 8.8.1: the fiber component of a `2`-morphism is natural on vertical
morphisms inside a fixed fiber. -/
private theorem basedFiberFunctorHom_naturality
    {X Y : FibredCategoryOver C} {F G : X ⟶ Y}
    (η : F ⟶ G) {U : C} {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (FibredCategoryMor.fiberFunctor F U).map φ ≫
        basedFiberFunctorHom η U y =
      basedFiberFunctorHom η U x ≫
        (FibredCategoryMor.fiberFunctor G U).map φ := by
  apply Functor.Fiber.hom_ext
  exact (η.hom.hom).toNatTrans.naturality φ.1

/-- Helper for Lemma 8.8.1: pulling back the fiber component of an arbitrary `2`-morphism is the
same as evaluating the component after pullback and conjugating by the two pullback-comparison
isomorphisms. -/
private theorem basedFiberFunctorHom_pullback_bridge
    {X Y : FibredCategoryOver C} {F G : X ⟶ Y}
    (η : F ⟶ G) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        (basedFiberFunctorHom η U x) =
      (FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv := by
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
      F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫
          (basedFiberFunctorHom η U x).1 =
        (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1 ≫
          G.toHom.map ((canonicalPullbackChoice X.p).map f x) := by
    change F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫
        (η.hom.hom).toNatTrans.app x.1 =
      (η.hom.hom).toNatTrans.app (f ^*[canonicalPullbackChoice X.p] x).1 ≫
        G.toHom.map ((canonicalPullbackChoice X.p).map f x)
    exact (η.hom.hom).toNatTrans.naturality ((canonicalPullbackChoice X.p).map f x)
  have hFpost :
      (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
        (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) :=
    FibredCategoryMor.pullbackComparison_hom_postcompose F f x
  have hGinvpost :
      (FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
          (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x) =
        G.toHom.map ((canonicalPullbackChoice X.p).map f x) :=
    FibredCategoryMor.pullbackComparison_inv_postcompose_owner G f x
  have hTargetCart :
      Y.p.IsStronglyCartesian f
        ((canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) := by
    exact (canonicalPullbackChoice Y.p).isStronglyCartesian f ((G.toHom.fiberFunctor U).obj x)
  have hLeftLift : Y.p.IsHomLift (𝟙 V) (M.map (basedFiberFunctorHom η U x)).1 :=
    (M.map (basedFiberFunctorHom η U x)).2
  have hRightLift : Y.p.IsHomLift (𝟙 V)
      (((FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv).1) :=
    ((FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv).2
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _ f
    ((canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) hTargetCart
    _ _ (𝟙 V) (M.map (basedFiberFunctorHom η U x)).1
    (((FibredCategoryMor.pullbackComparison F f x).hom ≫
        basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x) ≫
        (FibredCategoryMor.pullbackComparison G f x).inv).1)
    hLeftLift hRightLift ?_
  refine hPullbackMap.trans ?_
  have h1 :
      (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) ≫
          (basedFiberFunctorHom η U x).1 =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f x)) ≫
          (basedFiberFunctorHom η U x).1 :=
    congrArg (fun m => m ≫ (basedFiberFunctorHom η U x).1) hFpost.symm
  have h2 :
      ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f x)) ≫
          (basedFiberFunctorHom η U x).1 =
        (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫
            (basedFiberFunctorHom η U x).1) :=
    Category.assoc _ _ _
  have h3 :
      (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫
            (basedFiberFunctorHom η U x).1) =
        (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          ((basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1 ≫
            G.toHom.map ((canonicalPullbackChoice X.p).map f x)) :=
    congrArg (fun m => (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫ m) hNat
  have h4 :
      (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          ((basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1 ≫
            G.toHom.map ((canonicalPullbackChoice X.p).map f x)) =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1) ≫
          G.toHom.map ((canonicalPullbackChoice X.p).map f x) :=
    (Category.assoc _ _ _).symm
  have h5 :
      ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1) ≫
          G.toHom.map ((canonicalPullbackChoice X.p).map f x) =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1) ≫
          ((FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) :=
    congrArg
      (fun m => ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
        (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1) ≫ m)
      hGinvpost.symm
  have h6 :
      ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1) ≫
          ((FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)) =
        (((FibredCategoryMor.pullbackComparison F f x).hom ≫
          basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x) ≫
          (FibredCategoryMor.pullbackComparison G f x).inv).1) ≫
          (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x) := by
    change (((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          (basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1) ≫
          ((FibredCategoryMor.pullbackComparison G f x).inv.1 ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x))) =
        ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          ((basedFiberFunctorHom η V (f ^*[canonicalPullbackChoice X.p] x)).1 ≫
            (FibredCategoryMor.pullbackComparison G f x).inv.1)) ≫
            (canonicalPullbackChoice Y.p).map f ((G.toHom.fiberFunctor U).obj x)
    simp only [Category.assoc]
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- Helper for Lemma 8.8.1: postcomposition by a fixed fiber morphism is natural on the
canonical Hom presheaf. -/
private theorem presheafHomPostcompMap_naturality
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vY, uY}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (β : N ⟶ P) :
    ∀ ⦃T₁ T₂ : (Over U)ᵒᵖ⦄ (α : T₁ ⟶ T₂),
      ((F.presheafHom M N).map α) ≫
          (fun φ => φ ≫ (F.map T₂.unop.hom.op.toLoc).toFunctor.map β) =
        (fun φ => φ ≫ (F.map T₁.unop.hom.op.toLoc).toFunctor.map β) ≫
          ((F.presheafHom M P).map α) := by
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

/-- Helper for Lemma 8.8.1: the canonical Hom-presheaf map induced by postcomposition with a
fixed fiber morphism. -/
private noncomputable def presheafHomPostcompMap
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vY, uY}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (β : N ⟶ P) :
    F.presheafHom M N ⟶ F.presheafHom M P where
  app T φ := φ ≫ (F.map T.unop.hom.op.toLoc).toFunctor.map β
  naturality := presheafHomPostcompMap_naturality β

/-- Helper for Lemma 8.8.1: evaluating Hom-presheaf postcomposition at the identity slice object
gives ordinary postcomposition. -/
private theorem presheafHomPostcompMap_app_id
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vY, uY}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (β : N ⟶ P) (φ : M ⟶ N) :
    (presheafHomPostcompMap β).app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (φ ≫ β) := by
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

/-- Helper for Lemma 8.8.1: precomposition by a fixed fiber morphism is natural on the canonical
Hom presheaf. -/
private theorem presheafHomPrecompMap_naturality
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vY, uY}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (α₀ : M ⟶ N) :
    ∀ ⦃T₁ T₂ : (Over U)ᵒᵖ⦄ (α : T₁ ⟶ T₂),
      ((F.presheafHom N P).map α) ≫
          (fun φ => (F.map T₂.unop.hom.op.toLoc).toFunctor.map α₀ ≫ φ) =
        (fun φ => (F.map T₁.unop.hom.op.toLoc).toFunctor.map α₀ ≫ φ) ≫
          ((F.presheafHom M P).map α) := by
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

/-- Helper for Lemma 8.8.1: the canonical Hom-presheaf map induced by precomposition with a fixed
fiber morphism. -/
private noncomputable def presheafHomPrecompMap
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vY, uY}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (α : M ⟶ N) :
    F.presheafHom N P ⟶ F.presheafHom M P where
  app T φ := (F.map T.unop.hom.op.toLoc).toFunctor.map α ≫ φ
  naturality := presheafHomPrecompMap_naturality α

/-- Helper for Lemma 8.8.1: evaluating Hom-presheaf precomposition at the identity slice object
gives ordinary precomposition. -/
private theorem presheafHomPrecompMap_app_id
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vY, uY}}
    {U : C} {M N P : F.obj (.mk (op U))}
    (α : M ⟶ N) (φ : N ⟶ P) :
    (presheafHomPrecompMap α).app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (α ≫ φ) := by
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

/-- Helper for Lemma 8.8.1: an inverse-then-hom pair in the middle of a composite cancels after
reassociation. -/
private theorem comp_inv_hom_assoc
    {D : Type*} [Category D] {A B C' E : D}
    (a : A ⟶ B) (e : C' ≅ B) (b : B ⟶ E) :
    (a ≫ e.inv) ≫ e.hom ≫ b = a ≫ b := by
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun t => a ≫ t ≫ b) e.inv_hom_id

/-- Helper for Lemma 8.8.1: the Hom-presheaf comparison map is natural with respect to a
`2`-morphism, expressed as postcomposition on one side and precomposition on the other. -/
private theorem fibredMorphismPresheafMap_twoHom_naturality
    {X Y : FibredCategoryOver C} {F K : X ⟶ Y}
    (η : F ⟶ K) {U : C} (x x' : X.p.Fiber U) :
    FibredCategoryMor.fibredMorphismPresheafMap F x x' ≫
        presheafHomPostcompMap (basedFiberFunctorHom η U x') =
      FibredCategoryMor.fibredMorphismPresheafMap K x x' ≫
        presheafHomPrecompMap (basedFiberFunctorHom η U x) := by
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
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x') ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
    exact basedFiberFunctorHom_pullback_bridge η W.unop.hom x'
  have hpullx :
      ((canonicalFiberPseudofunctor Y.p).map W.unop.hom.op.toLoc).toFunctor.map
          (basedFiberFunctorHom η U₀ x) =
        (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x) ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x).inv := by
    exact basedFiberFunctorHom_pullback_bridge η W.unop.hom x
  have hnat :
      (FibredCategoryMor.fiberFunctor F W.unop.left).map φ ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x') =
        basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x) ≫
          (FibredCategoryMor.fiberFunctor K W.unop.left).map φ := by
    exact basedFiberFunctorHom_naturality η φ
  conv_lhs => rhs; rw [hpullx']
  conv_rhs => lhs; rw [hpullx]
  have hleft := comp_inv_hom_assoc
    ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
      (FibredCategoryMor.fiberFunctor F W.unop.left).map φ)
    (FibredCategoryMor.pullbackComparison F W.unop.hom x')
    (basedFiberFunctorHom η W.unop.left
      (W.unop.hom ^*[canonicalPullbackChoice X.p] x') ≫
      (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv)
  have hright := comp_inv_hom_assoc
    ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
      basedFiberFunctorHom η W.unop.left
        (W.unop.hom ^*[canonicalPullbackChoice X.p] x))
    (FibredCategoryMor.pullbackComparison K W.unop.hom x)
    ((FibredCategoryMor.fiberFunctor K W.unop.left).map φ ≫
      (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv)
  calc
    _ = ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
          (FibredCategoryMor.fiberFunctor F W.unop.left).map φ) ≫
        basedFiberFunctorHom η W.unop.left
          (W.unop.hom ^*[canonicalPullbackChoice X.p] x') ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
        simpa only [Category.assoc] using hleft
    _ = (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
        (((FibredCategoryMor.fiberFunctor F W.unop.left).map φ ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x')) ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv) := by
        simp only [Category.assoc]
    _ = (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
        ((basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x) ≫
          (FibredCategoryMor.fiberFunctor K W.unop.left).map φ) ≫
          (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv) := by
        exact congrArg
          (fun t =>
            (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫ t ≫
              (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv)
          hnat
    _ = ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
          basedFiberFunctorHom η W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x)) ≫
        (FibredCategoryMor.fiberFunctor K W.unop.left).map φ ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
        simp only [Category.assoc]
    _ = (FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
        basedFiberFunctorHom η W.unop.left
          (W.unop.hom ^*[canonicalPullbackChoice X.p] x) ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x).inv ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x).hom ≫
        (FibredCategoryMor.fiberFunctor K W.unop.left).map φ ≫
        (FibredCategoryMor.pullbackComparison K W.unop.hom x').inv := by
        simpa only [Category.assoc] using hright.symm
    _ = _ := by
        simp only [← Category.assoc]
        rfl

/-- Helper for Lemma 8.8.1 (object descent, forced fiber iso): for an owner iso `γ : K ≅ K'` of
fibred-category morphisms `Y₁ ⟶ Y₂` and a `G₁`-image object `(G₁.fiberFunctor W).obj z`, the
forced fiber isomorphism is the restriction of the based-functor iso `basedFunctorIsoOfOwnerIso γ`
to that fiber.  Its type is, definitionally,
`(K.fiberFunctor W).obj ((G₁.fiberFunctor W).obj z) ≅ (K'.fiberFunctor W).obj ((G₁.fiberFunctor W).obj z)`.
This is the local model of the comparison `2`-iso component `H(w) ≅ H'(w)` on a chosen
`G₁`-model of `w`.  (For `γ = basedFunctorIsoOfOwnerIso c` arising from an owner iso
`c : G₁ ≫ K ≅ G₁ ≫ K'`, this agrees with `basedFiberFunctorIso (… c) W ((G₁.fiberFunctor W).obj z)`
by the composite defeq `(fiberFunctor (G₁ ≫ K) W).obj z = (K.fiberFunctor W).obj ((G₁.fiberFunctor W).obj z)`.) -/
noncomputable def cForcedFiberIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (γ : K ≅ K')
    {W : C} (z : X.p.Fiber W) :
    ((FibredCategoryMor.fiberFunctor K W).obj ((FibredCategoryMor.fiberFunctor G₁ W).obj z)) ≅
      ((FibredCategoryMor.fiberFunctor K' W).obj ((FibredCategoryMor.fiberFunctor G₁ W).obj z)) :=
  basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) W
    ((FibredCategoryMor.fiberFunctor G₁ W).obj z)

/-- Helper for Lemma 8.8.1 (object descent): the forced fiber morphism `H(w) ⟶ H'(w)` produced by
transporting `cForcedFiberIso γ x` across a chosen `G₁`-model iso `cx : (G₁.fiberFunctor W).obj x ≅ w`.
Both ends use the SAME model `cx`, so this is a vertical morphism
`(K.fiberFunctor W).obj w ⟶ (K'.fiberFunctor W).obj w`. -/
noncomputable def forcedFiberHom
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (γ : K ≅ K')
    {W : C} (w : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ w) :
    ((FibredCategoryMor.fiberFunctor K W).obj w) ⟶
      ((FibredCategoryMor.fiberFunctor K' W).obj w) :=
  (FibredCategoryMor.fiberFunctor K W).map cx.inv ≫
    (cForcedFiberIso G₁ γ x).hom ≫
    (FibredCategoryMor.fiberFunctor K' W).map cx.hom

/-- Helper for Lemma 8.8.1 (object descent, MODEL INDEPENDENCE — the reusable crux): the forced
fiber morphism `H(w) ⟶ H'(w)` does not depend on which source model `(x, cx)` of `w` is chosen.
Two source models `(x, cx)`, `(x', cx')` of the same `w : Y₁.p.Fiber W` produce the same morphism.
The discrepancy iso `d := cx ≪≫ cx'.symm : (G₁.fiberFunctor W).obj x ≅ (G₁.fiberFunctor W).obj x'`
is a fiber iso between the two `G₁`-images, and the forced components are related across it by the
naturality of the based natural transformation underlying `γ` (`basedFiberFunctorIso_transport_of_fiberIso`),
so conjugating the second forced component by `d` recovers the first. -/
theorem forcedFiberHom_model_indep
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (γ : K ≅ K')
    {W : C} (w : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ w)
    (x' : X.p.Fiber W)
    (cx' : ((FibredCategoryMor.fiberFunctor G₁ W).obj x') ≅ w) :
    forcedFiberHom G₁ γ w x cx = forcedFiberHom G₁ γ w x' cx' := by
  -- Abbreviations for the two fiber functors and the forced components.
  set Kf := FibredCategoryMor.fiberFunctor K W with hKf
  set K'f := FibredCategoryMor.fiberFunctor K' W with hK'f
  -- The discrepancy iso between the two `G₁`-images.
  set d : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x') := cx ≪≫ cx'.symm with hd
  -- `cForcedFiberIso` at `x'` is `cForcedFiberIso` at `x` transported across `d` (naturality of γ).
  have htransport :
      (cForcedFiberIso G₁ γ x').hom =
        Kf.map d.inv ≫ (cForcedFiberIso G₁ γ x).hom ≫ K'f.map d.hom :=
    basedFiberFunctorIso_transport_of_fiberIso γ (V := W) d
  -- Abbreviate the forced component at `x`.
  set Φx := (cForcedFiberIso G₁ γ x).hom with hΦx
  -- Unfold both sides to the explicit triple composites.
  show Kf.map cx.inv ≫ Φx ≫ K'f.map cx.hom =
    Kf.map cx'.inv ≫ (cForcedFiberIso G₁ γ x').hom ≫ K'f.map cx'.hom
  rw [htransport]
  -- `d.hom = cx.hom ≫ cx'.inv`, `d.inv = cx'.hom ≫ cx.inv` (from the `≪≫`/`symm` definitions).
  have hdhom : d.hom = cx.hom ≫ cx'.inv := rfl
  have hdinv : d.inv = cx'.hom ≫ cx.inv := rfl
  rw [hdhom, hdinv, Functor.map_comp, Functor.map_comp]
  -- Reassociate fully to the right, then cancel the bracketing `cx'`-factors with `_assoc`
  -- cancellation lemmas (no literal-subterm matching needed).
  simp only [Category.assoc]
  -- Fold the leading `Kf.map cx'.inv ≫ Kf.map cx'.hom` and cancel; then fold the trailing
  -- `K'f.map cx'.inv ≫ K'f.map cx'.hom` and cancel.
  rw [← Functor.map_comp_assoc Kf cx'.inv cx'.hom, cx'.inv_hom_id, Functor.map_id,
    Category.id_comp, ← Functor.map_comp K'f cx'.inv cx'.hom, cx'.inv_hom_id, Functor.map_id,
    Category.comp_id]

/-- Helper for Lemma 8.8.1 (object descent, X-SIDE forced fiber component): for an owner iso
`c : G₁ ≫ K ≅ G₁ ≫ K'` of fibred-category morphisms `X ⟶ Y₂` (the genuinely X-side comparison
arising from two comparison data `α : G₁ ≫ H ≅ G₂`, `α' : G₁ ≫ H' ≅ G₂` via `c = α ≪≫ α'.symm`),
and a SOURCE object `x : X.p.Fiber W`, this is the restriction of the based-functor iso
`basedFunctorIsoOfOwnerIso c` to the fiber over `W` at `x`. Its type is, definitionally,
`(K.fiberFunctor W).obj ((G₁.fiberFunctor W).obj x) ≅ (K'.fiberFunctor W).obj ((G₁.fiberFunctor W).obj x)`
because `(G₁ ≫ K).fiberFunctor W` acts on objects by `(K.fiberFunctor W) ∘ (G₁.fiberFunctor W)`.
This is the local model of the comparison `2`-iso component on a chosen `G₁`-model. -/
noncomputable def cFiberComp
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (x : X.p.Fiber W) :
    ((FibredCategoryMor.fiberFunctor K W).obj ((FibredCategoryMor.fiberFunctor G₁ W).obj x)) ≅
      ((FibredCategoryMor.fiberFunctor K' W).obj ((FibredCategoryMor.fiberFunctor G₁ W).obj x)) :=
  basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso c) W x

/-- Helper for Lemma 8.8.1 (object descent, X-SIDE forced fiber morphism): the forced fiber
morphism `K(y) ⟶ K'(y)` over an ARBITRARY object `y : Y₁.p.Fiber W`, produced by transporting the
X-side forced component `cFiberComp c x` across a chosen `G₁`-model iso
`cx : (G₁.fiberFunctor W).obj x ≅ y`. Both ends use the SAME model `cx`, so this is a vertical
morphism `(K.fiberFunctor W).obj y ⟶ (K'.fiberFunctor W).obj y` in `Y₂.p.Fiber W`. -/
noncomputable def realForcedHom
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    ((FibredCategoryMor.fiberFunctor K W).obj y) ⟶
      ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
  (FibredCategoryMor.fiberFunctor K W).map cx.inv ≫
    (cFiberComp G₁ c x).hom ≫
    (FibredCategoryMor.fiberFunctor K' W).map cx.hom

/-- Helper for Lemma 8.8.1 (object descent, the cover-free core of model independence): two source
models `(x, cx)`, `(x', cx')` of `y` produce the same `realForcedHom` AS SOON AS the discrepancy
between the two `G₁`-images is itself the `G₁`-image of a SOURCE morphism `γ : x ⟶ x'` (i.e.
`G₁(γ) = cx.hom ≫ cx'.inv`). The `X`-side naturality `basedFiberFunctorIso_naturality c γ` of the
based natural transformation underlying `c` then conjugates one forced component into the other.
On a fibre over an arbitrary base, `G₁` is NOT fiberwise full, so this hypothesis does not always
hold; the genuine descent realizes it COVERWISE on the pulled-back models. -/
private theorem realForcedHom_eq_of_imageDiscrepancy
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y)
    (x' : X.p.Fiber W)
    (cx' : ((FibredCategoryMor.fiberFunctor G₁ W).obj x') ≅ y)
    (γ : x ⟶ x')
    (hγ : (FibredCategoryMor.fiberFunctor G₁ W).map γ = cx.hom ≫ cx'.inv) :
    realForcedHom G₁ c y x cx = realForcedHom G₁ c y x' cx' := by
  -- Unfold both `realForcedHom`s to explicit triple composites.
  dsimp only [realForcedHom]
  -- The `X`-side naturality of `c` on the source morphism `γ`:
  -- `(K.fiberFunctor W).map (G₁ γ) ≫ (cFiberComp c x').hom =
  --   (cFiberComp c x).hom ≫ (K'.fiberFunctor W).map (G₁ γ)`.
  have hnat :
      (FibredCategoryMor.fiberFunctor K W).map
            ((FibredCategoryMor.fiberFunctor G₁ W).map γ) ≫ (cFiberComp G₁ c x').hom =
        (cFiberComp G₁ c x).hom ≫
          (FibredCategoryMor.fiberFunctor K' W).map
            ((FibredCategoryMor.fiberFunctor G₁ W).map γ) :=
    basedFiberFunctorIso_naturality c (V := W) γ
  rw [hγ, Functor.map_comp, Functor.map_comp] at hnat
  -- `hnat : (Kf cx.hom ≫ Kf cx'.inv) ≫ (cFC x').hom = (cFC x).hom ≫ (K'f cx.hom ≫ K'f cx'.inv)`.
  -- Expand the trailing `K'f.map cx.hom` factor of the LHS into the bracketed
  -- `(K'f cx.hom ≫ K'f cx'.inv) ≫ K'f cx'.hom`.
  have hKcancel :
      (FibredCategoryMor.fiberFunctor K' W).map cx.hom =
        ((FibredCategoryMor.fiberFunctor K' W).map cx.hom ≫
            (FibredCategoryMor.fiberFunctor K' W).map cx'.inv) ≫
          (FibredCategoryMor.fiberFunctor K' W).map cx'.hom := by
    rw [Category.assoc, ← Functor.map_comp, cx'.inv_hom_id, Functor.map_id, Category.comp_id]
  rw [hKcancel]
  -- Reassociate so the RHS-of-`hnat` block `(cFC x).hom ≫ (K'f cx.hom ≫ K'f cx'.inv)` is a unit.
  rw [← Category.assoc (cFiberComp G₁ c x).hom, ← hnat]
  -- Collapse the leading `Kf`-factors `cx.inv ≫ cx.hom ≫ cx'.inv = cx'.inv`.
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, cx.inv_hom_id, Category.id_comp]

/-- Helper for Lemma 8.8.1: the X-side forced components on literal `G₁`-image objects are
natural with respect to every target-side morphism between those image objects. The proof compares
the two Hom-presheaf maps out of
`Hom_Y₁(G₁ x, G₁ x')`; they agree after precomposition with the stackification Hom map from
`Hom_X(x, x')`, and the codomain Hom presheaf is a sheaf because `Y₂` is a stack. -/
private theorem realForcedHom_image_naturality
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {U : C} (x x' : X.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor G₁ U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G₁ U).obj x')) :
    (FibredCategoryMor.fiberFunctor K U).map d ≫ (cFiberComp G₁ c x').hom =
      (cFiberComp G₁ c x).hom ≫
        (FibredCategoryMor.fiberFunctor K' U).map d := by
  have hMap :
      FibredCategoryMor.fibredMorphismPresheafMap K
          ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
          ((FibredCategoryMor.fiberFunctor G₁ U).obj x') ≫
        presheafHomPostcompMap (basedFiberFunctorHom c.hom U x') =
      FibredCategoryMor.fibredMorphismPresheafMap K'
          ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
          ((FibredCategoryMor.fiberFunctor G₁ U).obj x') ≫
        presheafHomPrecompMap (basedFiberFunctorHom c.hom U x) := by
    apply W_precomp_ext_to_sheaf (J := J.over U)
      (FibredCategoryMor.fibredMorphismPresheafMap G₁ x x')
      (hG₁.morphismPresheafMap_W U x x')
    · exact
        Pseudofunctor.IsPrestack.isSheaf
          (F := canonicalFiberPseudofunctor Y₂.p) (J := J) (S := U)
          ((FibredCategoryMor.fiberFunctor K U).obj
            ((FibredCategoryMor.fiberFunctor G₁ U).obj x))
          ((FibredCategoryMor.fiberFunctor K' U).obj
            ((FibredCategoryMor.fiberFunctor G₁ U).obj x'))
    · have hLeft :
          FibredCategoryMor.fibredMorphismPresheafMap G₁ x x' ≫
              (FibredCategoryMor.fibredMorphismPresheafMap K
                  ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
                  ((FibredCategoryMor.fiberFunctor G₁ U).obj x') ≫
                presheafHomPostcompMap (basedFiberFunctorHom c.hom U x')) =
            FibredCategoryMor.fibredMorphismPresheafMap (G₁ ≫ K) x x' ≫
              presheafHomPostcompMap (basedFiberFunctorHom c.hom U x') := by
        rw [← Category.assoc]
        rw [← fibredMorphismPresheafMap_comp G₁ K x x']
        rfl
      have hRight :
          FibredCategoryMor.fibredMorphismPresheafMap G₁ x x' ≫
              (FibredCategoryMor.fibredMorphismPresheafMap K'
                  ((FibredCategoryMor.fiberFunctor G₁ U).obj x)
                  ((FibredCategoryMor.fiberFunctor G₁ U).obj x') ≫
                presheafHomPrecompMap (basedFiberFunctorHom c.hom U x)) =
            FibredCategoryMor.fibredMorphismPresheafMap (G₁ ≫ K') x x' ≫
              presheafHomPrecompMap (basedFiberFunctorHom c.hom U x) := by
        rw [← Category.assoc]
        rw [← fibredMorphismPresheafMap_comp G₁ K' x x']
        rfl
      exact hLeft.trans
        ((fibredMorphismPresheafMap_twoHom_naturality c.hom x x').trans hRight.symm)
  have hEval :=
    congrArg
      (fun η =>
        η.app (op (Over.mk (𝟙 U)))
          ((canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv d))
      hMap
  have hPresheaf :
      (canonicalFiberPseudofunctor Y₂.p).presheafHomObjHomEquiv
          ((FibredCategoryMor.fiberFunctor K U).map d ≫
            basedFiberFunctorHom c.hom U x') =
        (canonicalFiberPseudofunctor Y₂.p).presheafHomObjHomEquiv
          (basedFiberFunctorHom c.hom U x ≫
            (FibredCategoryMor.fiberFunctor K' U).map d) := by
    simpa only [NatTrans.comp_app, fibredMorphismPresheafMap_app_id_local,
      presheafHomPostcompMap_app_id, presheafHomPrecompMap_app_id,
      types_comp_apply] using hEval
  have hFiber :
      (FibredCategoryMor.fiberFunctor K U).map d ≫
          basedFiberFunctorHom c.hom U x' =
        basedFiberFunctorHom c.hom U x ≫
          (FibredCategoryMor.fiberFunctor K' U).map d :=
    (canonicalFiberPseudofunctor Y₂.p).presheafHomObjHomEquiv.injective hPresheaf
  -- The fiber component of `c.hom` is definitionally the hom of `cFiberComp`.
  change (FibredCategoryMor.fiberFunctor K U).map d ≫
      basedFiberFunctorHom c.hom U x' =
    basedFiberFunctorHom c.hom U x ≫
      (FibredCategoryMor.fiberFunctor K' U).map d
  exact hFiber

/-- Helper for Lemma 8.8.1: the base cover of `W` obtained from a slice-site cover of the identity
slice object `Over.mk (𝟙 W)` by pushing the covering sieve forward along `Over.forget`. Its
underlying sieve is `Sieve.overEquiv (Over.mk (𝟙 W)) S.1`, which is in `J W` by definition of the
slice topology. -/
private noncomputable def baseCoverOfIdSliceCover
    {W : C} (S : (J.over W).Cover (Over.mk (𝟙 W))) :
    J.Cover W :=
  ⟨Sieve.overEquiv (Over.mk (𝟙 W)) S.1, by
    have h : S.1 ∈ (J.over W) (Over.mk (𝟙 W)) := S.2
    rw [J.mem_over_iff] at h
    exact h⟩

/-- Helper for Lemma 8.8.1: an arrow of `baseCoverOfIdSliceCover S` is an arrow `f : Z ⟶ W` whose
associated slice arrow `Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 W)` belongs to the slice cover `S`. -/
private theorem baseCoverOfIdSliceCover_arrow_mem
    {W : C} (S : (J.over W).Cover (Over.mk (𝟙 W)))
    (I : (baseCoverOfIdSliceCover (J := J) S).Arrow) :
    S.1 (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)) :=
  (Sieve.overEquiv_iff (Y := Over.mk (𝟙 W)) S.1 I.f).1 I.hf

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.8.1 (object descent, the pullback bridge for `realForcedHom`): pulling back
the forced fiber morphism along `f : V ⟶ W` (via the canonical pullback functor `Mᶠ` of `Y₂`)
equals — up to conjugation by the `K`/`K'` pullback-comparison isomorphisms at `y` — the forced
fiber morphism over `V` for the pulled-back model `(f^*x₀, cxV)` of `f^*y`, where
`cxV := (pullbackComparison G₁ f x₀).symm ≪≫ (Mᶠ_{Y₁}.mapIso cx₀)`. This is the cocycle identity
that turns the global construction into per-arrow data. -/
theorem Mf_realForcedHom_pullback
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W V : C} (f : V ⟶ W) (y : Y₁.p.Fiber W)
    (x₀ : X.p.Fiber W)
    (cx₀ : ((FibredCategoryMor.fiberFunctor G₁ W).obj x₀) ≅ y) :
    ((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
        (realForcedHom G₁ c y x₀ cx₀) =
      (FibredCategoryMor.pullbackComparison K f y).hom ≫
        realForcedHom G₁ c (f ^*[canonicalPullbackChoice Y₁.p] y)
          (f ^*[canonicalPullbackChoice X.p] x₀)
          ((FibredCategoryMor.pullbackComparison G₁ f x₀).symm ≪≫
            (((canonicalFiberPseudofunctor Y₁.p).map f.op.toLoc).toFunctor.mapIso cx₀)) ≫
        (FibredCategoryMor.pullbackComparison K' f y).inv := by
  -- Abbreviations for the canonical pullback functors over `Y₁` / `Y₂` along `f`.
  set Mf₁ := ((canonicalFiberPseudofunctor Y₁.p).map f.op.toLoc).toFunctor with hMf₁
  set Mf₂ := ((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor with hMf₂
  -- Unfold `realForcedHom` on both sides.
  simp only [realForcedHom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  -- Distribute `Mf₂.map` over the LHS composite.
  rw [Mf₂.map_comp, Mf₂.map_comp]
  -- Bridge A: the `cFiberComp` middle factor.
  have hA :
      Mf₂.map (cFiberComp G₁ c x₀).hom =
        (FibredCategoryMor.pullbackComparison (G₁ ≫ K) f x₀).hom ≫
          (cFiberComp G₁ c (f ^*[canonicalPullbackChoice X.p] x₀)).hom ≫
          (FibredCategoryMor.pullbackComparison (G₁ ≫ K') f x₀).inv :=
    basedFiberFunctorIso_pullback_bridge c f x₀
  -- Bridge B: the `K_W cx₀.inv` left factor (rearranged to solve for `Mf₂.map (Kf_W cx₀.inv)`).
  have hB :
      Mf₂.map ((FibredCategoryMor.fiberFunctor K W).map cx₀.inv) =
        (FibredCategoryMor.pullbackComparison K f y).hom ≫
          (FibredCategoryMor.fiberFunctor K V).map (Mf₁.map cx₀.inv) ≫
          (FibredCategoryMor.pullbackComparison K f
            ((FibredCategoryMor.fiberFunctor G₁ W).obj x₀)).inv := by
    have h := pullbackComparison_naturality_over_vertical K f cx₀.inv
    -- `h : Mf₂.map (Kf_W cx₀.inv) ≫ (pbc K f (G₁_W x₀)).hom
    --        = (pbc K f y).hom ≫ Kf_V.map (Mf₁ cx₀.inv)`.
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 h
  -- Bridge C: the `K'_W cx₀.hom` right factor.
  have hC :
      Mf₂.map ((FibredCategoryMor.fiberFunctor K' W).map cx₀.hom) =
        (FibredCategoryMor.pullbackComparison K' f
            ((FibredCategoryMor.fiberFunctor G₁ W).obj x₀)).hom ≫
          (FibredCategoryMor.fiberFunctor K' V).map (Mf₁.map cx₀.hom) ≫
          (FibredCategoryMor.pullbackComparison K' f y).inv := by
    have h := pullbackComparison_naturality_over_vertical K' f cx₀.hom
    -- `h : Mf₂.map (K'f_W cx₀.hom) ≫ (pbc K' f y).hom
    --        = (pbc K' f (G₁_W x₀)).hom ≫ K'f_V.map (Mf₁ cx₀.hom)`.
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 h
  rw [hA, hB, hC]
  -- The composition decomposition of the `G₁ ≫ K` / `G₁ ≫ K'` pullback comparisons.
  have hKcomp :
      (FibredCategoryMor.pullbackComparison (G₁ ≫ K) f x₀).hom =
        (FibredCategoryMor.pullbackComparison K f
            ((FibredCategoryMor.fiberFunctor G₁ W).obj x₀)).hom ≫
          (FibredCategoryMor.fiberFunctor K V).map
            (FibredCategoryMor.pullbackComparison G₁ f x₀).hom :=
    pullbackComparison_comp_hom G₁ K f x₀
  have hK'comp :
      (FibredCategoryMor.pullbackComparison (G₁ ≫ K') f x₀).inv =
        (FibredCategoryMor.fiberFunctor K' V).map
            (FibredCategoryMor.pullbackComparison G₁ f x₀).inv ≫
          (FibredCategoryMor.pullbackComparison K' f
            ((FibredCategoryMor.fiberFunctor G₁ W).obj x₀)).inv := by
    -- The two pullback-comparison isos agree on `hom` by `pullbackComparison_comp_hom`, hence on
    -- `inv`; read off the `inv` of the composite iso.
    have hiso :
        FibredCategoryMor.pullbackComparison (G₁ ≫ K') f x₀ =
          (FibredCategoryMor.pullbackComparison K' f
              ((FibredCategoryMor.fiberFunctor G₁ W).obj x₀) ≪≫
            (FibredCategoryMor.fiberFunctor K' V).mapIso
              (FibredCategoryMor.pullbackComparison G₁ f x₀)) := by
      apply Iso.ext
      simp only [Iso.trans_hom, Functor.mapIso_hom]
      exact pullbackComparison_comp_hom G₁ K' f x₀
    rw [hiso]
    simp only [Iso.trans_inv, Functor.mapIso_inv]
  rw [hKcomp, hK'comp]
  -- Reassociate, cancel the adjacent `pbc⁻¹ ≫ pbc` blocks, and identify `Mf₁`.
  simp only [Category.assoc, Functor.map_comp, Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scratch_coherence
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g : Over.mk (g ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map (g ≫ 𝟙 W).op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  -- The middle factor collapses: conjugating `φ` by `mapId` is `(F.map (𝟙 _)).map φ`, which is
  -- definitionally `(F.map (Over.mk (𝟙 W)).hom.op.toLoc).map φ` — exactly the first leg of the
  -- enclosing `mapComp'`, so the whole thing is the naturality square `mapComp'_naturality_2`.
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫ φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  rw [hmid]
  -- The remaining goal is exactly the `mapComp'` naturality square `mapComp'_naturality_2`; the
  -- residual `(Over.mk (g ≫ 𝟙 W)).hom` vs `g ≫ 𝟙 W` matches definitionally.
  rw [(canonicalFiberPseudofunctor p).mapComp'_naturality_2]
  rfl

/-- Helper for Lemma 8.8.1: transporting the `pullbackComparison`-conjugate of a canonical-fiber
pullback map along an equal base arrow `b = b'` is `eqToHom`-conjugation. This packages the cast
between the `(I.f ≫ 𝟙 W)`-indexed slice arrow and the `I.f`-indexed pullback used in the object
descent. -/
private theorem pbc_Mf_conjugate_cast
    {X : FibredCategoryOver C} {Y₁ : StackOver J}
    (G₁ : X ⟶ Y₁)
    {W V : C} {b b' : V ⟶ W} (hbb : b = b')
    (x x' : X.p.Fiber W)
    (φ : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ⟶
        ((FibredCategoryMor.fiberFunctor G₁ W).obj x'))
    (h₁ : ((FibredCategoryMor.fiberFunctor G₁ V).obj (b' ^*[canonicalPullbackChoice X.p] x)) =
        ((FibredCategoryMor.fiberFunctor G₁ V).obj (b ^*[canonicalPullbackChoice X.p] x)))
    (h₂ : ((FibredCategoryMor.fiberFunctor G₁ V).obj (b ^*[canonicalPullbackChoice X.p] x')) =
        ((FibredCategoryMor.fiberFunctor G₁ V).obj (b' ^*[canonicalPullbackChoice X.p] x'))) :
    eqToHom h₁ ≫
        (FibredCategoryMor.pullbackComparison G₁ b x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map b.op.toLoc).toFunctor.map φ ≫
          (FibredCategoryMor.pullbackComparison G₁ b x').hom ≫
        eqToHom h₂ =
      (FibredCategoryMor.pullbackComparison G₁ b' x).inv ≫
        ((canonicalFiberPseudofunctor Y₁.p).map b'.op.toLoc).toFunctor.map φ ≫
        (FibredCategoryMor.pullbackComparison G₁ b' x').hom := by
  subst hbb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 1: the Hom-presheaf section associated to the discrepancy
between two `G₁`-image models. -/
private noncomputable def realForcedHomDiscrepancySection
    {X : FibredCategoryOver C} {Y₁ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    {W : C} (x x' : X.p.Fiber W)
    (d : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x')) :
    ((canonicalFiberPseudofunctor Y₁.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x)
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x')).obj (op (Over.mk (𝟙 W))) :=
  (canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv d.hom

/-- Helper for Chap08 Lemma 8 8 1: the identity-slice image cover of a discrepancy between two
`G₁`-image models. -/
private noncomputable abbrev realForcedHomDiscrepancySliceCover
    {X : FibredCategoryOver C} {Y₁ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {W : C} (x x' : X.p.Fiber W)
    [(J.over W).WEqualsLocallyBijective (Type vY)]
    (d : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x')) :
    (J.over W).Cover (Over.mk (𝟙 W)) :=
  stackification_hom_image_cover (J := J) G₁ hG₁ (x := x) (y := x')
    (realForcedHomDiscrepancySection (J := J) G₁ x x' d)

/-- Helper for Chap08 Lemma 8 8 1: the base cover on which a discrepancy between two
`G₁`-image models is represented by a source-side morphism. -/
private noncomputable abbrev realForcedHomDiscrepancyCover
    {X : FibredCategoryOver C} {Y₁ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {W : C} (x x' : X.p.Fiber W)
    [(J.over W).WEqualsLocallyBijective (Type vY)]
    (d : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x')) :
    J.Cover W :=
  baseCoverOfIdSliceCover (J := J)
    (realForcedHomDiscrepancySliceCover (J := J) G₁ hG₁ x x' d)

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1: on the discrepancy image cover, the discrepancy between two
`G₁`-image models has a source-side lift with the pullback-comparison normal form needed by
`realForcedHom_eq_of_imageDiscrepancy`. -/
private theorem realForcedHomDiscrepancyCover_hom_lift
    {X : FibredCategoryOver C} {Y₁ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {W : C} (x x' : X.p.Fiber W)
    [(J.over W).WEqualsLocallyBijective (Type vY)]
    (d : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x'))
    (I : (realForcedHomDiscrepancyCover (J := J) G₁ hG₁ x x' d).Arrow) :
    ∃ γ : (I.f ^*[canonicalPullbackChoice X.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice X.p] x'),
      (FibredCategoryMor.fiberFunctor G₁ I.Y).map γ =
        (FibredCategoryMor.pullbackComparison G₁ I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison G₁ I.f x').hom := by
  -- Lift the discrepancy as a section of the Hom presheaf on the identity-slice image cover.
  let β : ((canonicalFiberPseudofunctor Y₁.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x)
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x')).obj (op (Over.mk (𝟙 W))) :=
    realForcedHomDiscrepancySection (J := J) G₁ x x' d
  let Sslice : (J.over W).Cover (Over.mk (𝟙 W)) :=
    stackification_hom_image_cover (J := J) G₁ hG₁ (x := x) (y := x') β
  let Islice : Sslice.Arrow :=
    ⟨Over.mk (I.f ≫ 𝟙 W), Over.homMk I.f,
      baseCoverOfIdSliceCover_arrow_mem (J := J) Sslice I⟩
  obtain ⟨γRaw, hγRaw⟩ :=
    stackification_coverwise_hom_lift (J := J) G₁ hG₁ (x := x) (y := x') β Islice
  have hfeq : I.f ≫ 𝟙 W = I.f := Category.comp_id _
  -- Cast the raw slice lift back to the base-cover pullback objects.
  refine ⟨(eqToHom ?_) ≫ γRaw ≫ (eqToHom ?_), ?_⟩
  · simp only [Islice, Over.mk_hom, hfeq]
    rfl
  · simp only [Islice, Over.mk_hom, hfeq]
    rfl
  · have hγRawApp :
        (FibredCategoryMor.pullbackComparison G₁ (Islice.Y.hom) x).hom ≫
            (FibredCategoryMor.fiberFunctor G₁ Islice.Y.left).map γRaw ≫
            (FibredCategoryMor.pullbackComparison G₁ (Islice.Y.hom) x').inv =
          (((canonicalFiberPseudofunctor Y₁.p).presheafHom
              ((FibredCategoryMor.fiberFunctor G₁ W).obj x)
              ((FibredCategoryMor.fiberFunctor G₁ W).obj x')).map Islice.f.op) β := by
      rw [← hγRaw]
      rfl
    dsimp only [β, realForcedHomDiscrepancySection] at hγRawApp
    rw [scratch_coherence] at hγRawApp
    have hγRawMap :
        (FibredCategoryMor.fiberFunctor G₁ I.Y).map γRaw =
          (FibredCategoryMor.pullbackComparison G₁ (Islice.Y.hom) x).inv ≫
            ((canonicalFiberPseudofunctor Y₁.p).map (I.f ≫ 𝟙 W).op.toLoc).toFunctor.map d.hom ≫
            (FibredCategoryMor.pullbackComparison G₁ (Islice.Y.hom) x').hom := by
      have h1 :=
        (Iso.eq_inv_comp (FibredCategoryMor.pullbackComparison G₁ (Islice.Y.hom) x)).2
          hγRawApp
      have h2 :=
        (Iso.comp_inv_eq (FibredCategoryMor.pullbackComparison G₁ (Islice.Y.hom) x')).1 h1
      rw [Category.assoc] at h2
      exact h2
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, hγRawMap]
    simpa only [Functor.map_comp, Category.assoc] using
      pbc_Mf_conjugate_cast G₁ hfeq x x' d.hom
        (by simp only [hfeq])
        (by simp only [hfeq])

/-- Helper for Chap08 Lemma 8 8 1: under the precise slice-site local-bijectivity hypothesis
needed by the Hom-presheaf image cover, the forced morphism is independent of the chosen source
model. -/
private theorem realForcedHom_model_indep_of_locallyBijective
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y)
    (x' : X.p.Fiber W)
    (cx' : ((FibredCategoryMor.fiberFunctor G₁ W).obj x') ≅ y)
    [(J.over W).WEqualsLocallyBijective (Type vY)] :
    realForcedHom G₁ c y x cx = realForcedHom G₁ c y x' cx' := by
  -- Cover `W` by arrows on which the discrepancy between the two `G₁`-models has a
  -- source-side lift.
  let d : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x') :=
    cx ≪≫ cx'.symm
  apply stack_cover_hom_ext (J := J) Y₂
    (realForcedHomDiscrepancyCover (J := J) G₁ hG₁ x x' d)
  intro I
  obtain ⟨γ, hγ⟩ := realForcedHomDiscrepancyCover_hom_lift (J := J) G₁ hG₁ x x' d I
  -- Normalize both pullbacks to forced morphisms over the cover member.
  rw [Mf_realForcedHom_pullback G₁ c I.f y x cx,
    Mf_realForcedHom_pullback G₁ c I.f y x' cx']
  -- The lifted source morphism realizes exactly the discrepancy between the two pulled-back
  -- source models.
  have hγ' :
      (FibredCategoryMor.fiberFunctor G₁ I.Y).map γ =
        (((FibredCategoryMor.pullbackComparison G₁ I.f x).symm ≪≫
            (((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.mapIso cx)).hom) ≫
          (((FibredCategoryMor.pullbackComparison G₁ I.f x').symm ≪≫
            (((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.mapIso cx')).inv) := by
    rw [hγ]
    simp only [d, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    let Mf := ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor
    let a := (FibredCategoryMor.pullbackComparison G₁ I.f x).inv
    let b := Mf.map cx.hom
    let cMap := Mf.map cx'.inv
    let dMap := (FibredCategoryMor.pullbackComparison G₁ I.f x').hom
    change a ≫ (Mf.map (cx.hom ≫ cx'.inv) ≫ dMap) =
      a ≫ (b ≫ (cMap ≫ dMap))
    have hmap :
        Mf.map (cx.hom ≫ cx'.inv) = b ≫ cMap := by
      exact Mf.map_comp cx.hom cx'.inv
    rw [hmap]
    exact congrArg (fun φ => a ≫ φ) (Category.assoc b cMap dMap)
  -- Apply the cover-free model-independence lemma on this cover member and reinsert the common
  -- pullback-comparison conjugation.
  rw [realForcedHom_eq_of_imageDiscrepancy G₁ c
    (I.f ^*[canonicalPullbackChoice Y₁.p] y)
    (I.f ^*[canonicalPullbackChoice X.p] x)
    ((FibredCategoryMor.pullbackComparison G₁ I.f x).symm ≪≫
      (((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.mapIso cx))
    (I.f ^*[canonicalPullbackChoice X.p] x')
    ((FibredCategoryMor.pullbackComparison G₁ I.f x').symm ≪≫
      (((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.mapIso cx'))
    γ hγ']

/-- Helper for Chap08 Lemma 8 8 1: on every slice site, the canonical type-valued
local-bijectivity instance lives at the saturated site universe. -/
private theorem overTypeWEqualsLocallyBijective
    {W : C} :
    (J.over W).WEqualsLocallyBijective (Type (max u v)) := by
  -- This records the default mathlib instance used by the saturated comparison surface.
  infer_instance

/-- Helper for Chap08 Lemma 8 8 1: at the default saturated stack universe, model independence
follows from the side-conditioned coverwise core. -/
theorem realForcedHom_model_indep_saturated
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, max u v, max u v} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y)
    (x' : X.p.Fiber W)
    (cx' : ((FibredCategoryMor.fiberFunctor G₁ W).obj x') ≅ y) :
    realForcedHom G₁ c y x cx = realForcedHom G₁ c y x' cx' := by
  -- The default stack surface aligns the Hom universe with `Type (max u v)`, where the slice-site
  -- local-bijectivity instance is available, so the proved coverwise core applies directly.
  letI : (J.over W).WEqualsLocallyBijective (Type (max u v)) :=
    overTypeWEqualsLocallyBijective (J := J)
  exact realForcedHom_model_indep_of_locallyBijective (J := J) G₁ hG₁ c y x cx x' cx'

set_option backward.isDefEq.respectTransparency false in
theorem realForcedHom_model_indep
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y)
    (x' : X.p.Fiber W)
    (cx' : ((FibredCategoryMor.fiberFunctor G₁ W).obj x') ≅ y) :
    realForcedHom G₁ c y x cx = realForcedHom G₁ c y x' cx' := by
  -- Compare the two source models through their target-side discrepancy and use naturality of the
  -- forced component on literal `G₁`-image objects. This avoids choosing local preimages of the
  -- discrepancy, so no `WEqualsLocallyBijective (Type vY)` bridge is needed.
  let Kf := FibredCategoryMor.fiberFunctor K W
  let K'f := FibredCategoryMor.fiberFunctor K' W
  let d : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x') :=
    cx.hom ≫ cx'.inv
  have hnat :
      Kf.map d ≫ (cFiberComp G₁ c x').hom =
        (cFiberComp G₁ c x).hom ≫ K'f.map d :=
    realForcedHom_image_naturality (J := J) G₁ hG₁ c x x' d
  dsimp only [realForcedHom]
  have hKsplit :
      K'f.map cx.hom =
        K'f.map d ≫ K'f.map cx'.hom := by
    dsimp [d]
    rw [Functor.map_comp, Category.assoc, ← Functor.map_comp, cx'.inv_hom_id,
      Functor.map_id, Category.comp_id]
  have hHcollapse :
      Kf.map cx.inv ≫ Kf.map d = Kf.map cx'.inv := by
    have hsrc : cx.inv ≫ d = cx'.inv := by
      dsimp [d]
      rw [← Category.assoc, cx.inv_hom_id, Category.id_comp]
    rw [← Functor.map_comp]
    exact congrArg Kf.map hsrc
  rw [hKsplit]
  calc
    Kf.map cx.inv ≫ (cFiberComp G₁ c x).hom ≫ K'f.map d ≫ K'f.map cx'.hom =
        Kf.map cx.inv ≫ ((cFiberComp G₁ c x).hom ≫ K'f.map d) ≫
          K'f.map cx'.hom := by
          simp only [Category.assoc]
    _ = Kf.map cx.inv ≫ (Kf.map d ≫ (cFiberComp G₁ c x').hom) ≫
          K'f.map cx'.hom := by
          exact
            congrArg (fun m ↦ Kf.map cx.inv ≫ m ≫ K'f.map cx'.hom) hnat.symm
    _ = (Kf.map cx.inv ≫ Kf.map d) ≫ (cFiberComp G₁ c x').hom ≫
          K'f.map cx'.hom := by
          simp only [Category.assoc]
    _ = Kf.map cx'.inv ≫ (cFiberComp G₁ c x').hom ≫ K'f.map cx'.hom := by
          rw [hHcollapse]

/-- Helper for Lemma 8.8.1: the forced morphism is natural in the target fiber object after
choosing source models for the source and target objects. -/
theorem realForcedHom_model_naturality
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} {y y' : Y₁.p.Fiber W}
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y)
    (x' : X.p.Fiber W)
    (cx' : ((FibredCategoryMor.fiberFunctor G₁ W).obj x') ≅ y')
    (d : y ⟶ y') :
    (FibredCategoryMor.fiberFunctor K W).map d ≫ realForcedHom G₁ c y' x' cx' =
      realForcedHom G₁ c y x cx ≫
        (FibredCategoryMor.fiberFunctor K' W).map d := by
  let Kf := FibredCategoryMor.fiberFunctor K W
  let K'f := FibredCategoryMor.fiberFunctor K' W
  let dImg : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G₁ W).obj x') :=
    cx.hom ≫ d ≫ cx'.inv
  have hnat :
      Kf.map dImg ≫ (cFiberComp G₁ c x').hom =
        (cFiberComp G₁ c x).hom ≫ K'f.map dImg :=
    realForcedHom_image_naturality (J := J) G₁ hG₁ c x x' dImg
  have htransport :=
    congrArg (fun m => Kf.map cx.inv ≫ m ≫ K'f.map cx'.hom) hnat
  dsimp only [realForcedHom]
  simpa [Kf, K'f, dImg, Functor.map_comp, Category.assoc] using htransport

/-- Helper for Lemma 8.8.1 (object descent, GLOBAL fiber component of the comparison `2`-iso): for
an owner iso `γ : K ≅ K'` of fibred-category morphisms `Y₁ ⟶ Y₂` into a stack `Y₂`, and an
ARBITRARY object `w : Y₁.p.Fiber W`, the global fiber component
`(K.fiberFunctor W).obj w ≅ (K'.fiberFunctor W).obj w` is the restriction of the based-functor iso
`basedFunctorIsoOfOwnerIso γ` to the fiber over `W` at `w`. This is the model-free definition; its
characterization `comparisonTwoIsoComponent_eq_forced` shows that on any `G₁`-model `(x, cx)` of
`w` it equals the forced fiber morphism, so it is the unique global morphism whose local components
are forced by `γ`. -/
noncomputable def comparisonTwoIsoComponent
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (γ : K ≅ K')
    {W : C} (w : Y₁.p.Fiber W) :
    ((FibredCategoryMor.fiberFunctor K W).obj w) ≅
      ((FibredCategoryMor.fiberFunctor K' W).obj w) :=
  basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) W w

/-- Helper for Lemma 8.8.1 (object descent, CHARACTERIZATION): on any source model `(x, cx)` of an
arbitrary object `w : Y₁.p.Fiber W` (with `cx : (G₁.fiberFunctor W).obj x ≅ w`), the hom of the
global comparison `2`-iso component equals the forced fiber morphism `forcedFiberHom G₁ γ w x cx`.
This is the cover-free model-independence of the based natural transformation underlying `γ`
restricted to the fiber over `W`, packaged exactly as `basedFiberFunctorIso_transport_of_fiberIso`.
It identifies the global component with the descent-data-glued local data of the consumers. -/
theorem comparisonTwoIsoComponent_eq_forced
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (γ : K ≅ K')
    {W : C} (w : Y₁.p.Fiber W)
    (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ w) :
    (comparisonTwoIsoComponent G₁ hG₁ γ w).hom = forcedFiberHom G₁ γ w x cx := by
  -- The global component at `w` is the based-fiber iso at `w`, which the transport lemma rewrites
  -- as the conjugation of the based-fiber iso at the `G₁`-image `(G₁.fiberFunctor W).obj x` by the
  -- model iso `cx`. That conjugation is, by definition, `forcedFiberHom`.
  show (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) W w).hom =
    (FibredCategoryMor.fiberFunctor K W).map cx.inv ≫
      (cForcedFiberIso G₁ γ x).hom ≫
      (FibredCategoryMor.fiberFunctor K' W).map cx.hom
  exact basedFiberFunctorIso_transport_of_fiberIso γ (V := W) cx

/-- Helper for Lemma 8.8.1 (object descent, PULLBACK COMPATIBILITY — the descent-data cocycle
brick): the global comparison `2`-iso component is compatible with pullback. For `f : V ⟶ W`, the
canonical pullback along `f` (the functor `M := (canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc`)
of the component at `w` equals the `pullbackComparison`-conjugate of the component at the
pulled-back object `f ^* w`. This is the bridge that turns the per-arrow local components
(`forcedFiberHom` on the pulled-back objects, transported to `f ^* ((K.fiberFunctor W).obj w)` by
the two `pullbackComparison` isos) into a morphism of fixed-cover descent data: assembling the
`comm` cocycle for `stack_cover_hom_glue` reduces, on each overlap, to exactly this identity
(combined with the cover-free `comparisonTwoIsoComponent_eq_forced`/`forcedFiberHom_model_indep`).
It is `basedFiberFunctorIso_pullback_bridge` for `γ` read off at `w`. -/
theorem forcedFiberHom_pullback_compat
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver}
    (γ : K ≅ K')
    {W V : C} (f : V ⟶ W) (w : Y₁.p.Fiber W) :
    ((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
        (comparisonTwoIsoComponent G₁ hG₁ γ w).hom =
      (FibredCategoryMor.pullbackComparison K f w).hom ≫
        (comparisonTwoIsoComponent G₁ hG₁ γ
            (f ^*[canonicalPullbackChoice Y₁.p] w)).hom ≫
        (FibredCategoryMor.pullbackComparison K' f w).inv := by
  -- Unfold both global components to the based-fiber isos and apply the pullback bridge for `γ`.
  show ((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) W w).hom =
    (FibredCategoryMor.pullbackComparison K f w).hom ≫
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V
          (f ^*[canonicalPullbackChoice Y₁.p] w)).hom ≫
      (FibredCategoryMor.pullbackComparison K' f w).inv
  exact basedFiberFunctorIso_pullback_bridge γ f w

end

end CategoryTheory
