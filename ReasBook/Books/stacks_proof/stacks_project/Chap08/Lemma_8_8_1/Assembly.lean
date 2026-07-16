import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.ComparisonEquivalence
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.ForcedComparisonComponents
import Mathlib.Tactic.StacksAttribute

universe u v uY vY

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

/-- Helper for Lemma 8.8.1: a stack `2`-isomorphism is determined by the components of its
underlying based natural transformation on every total-source object. -/
private theorem stack_twoIso_ext
    {Y₁ Y₂ : StackOver J} {H H' : Y₁ ⟶ Y₂} (β β' : H ≅ H')
    (h : ∀ T : Y₁.S,
      (β.hom.hom.hom.hom.hom).toNatTrans.app T = (β'.hom.hom.hom.hom.hom).toNatTrans.app T) :
    β = β' := by
  apply Iso.ext
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext T
  exact h T

/-- Helper for Lemma 8.8.1: the component of the precomposed `2`-isomorphism `P.mapIso β` at a
source object `x` equals the component of `β` at the image `G₁(x)`. -/
private theorem precompose_mapIso_app
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁) {H H' : Y₁ ⟶ Y₂} (β : H ≅ H') (x : X.S) :
    ((stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β).hom.hom.hom.toNatTrans.app x
      = (β.hom.hom.hom.hom.hom).toNatTrans.app (G₁.toHom.obj x) :=
  rfl

/-- Helper for Lemma 8.8.1: the based-nat-trans component of an owner iso `γ` at a total object `T`
equals the underlying `.hom.1` of the fiber component at the canonical fiber object of `T`. -/
private theorem basedFiberFunctorIso_hom_one
    {X Y : FibredCategoryOver C} {F F' : X ⟶ Y} (γ : F ≅ F')
    (T : X.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ).hom.toNatTrans.app T =
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) (X.p.obj T)
        ⟨T, rfl⟩).hom.1 :=
  rfl

/-- Helper for Lemma 8.8.1 (faithfulness, descent core): two owner isomorphisms of stack
morphisms whose fiber components agree on every `G₁`-image object agree on every fiber object. The
proof descends the agreement coverwise: each fiber object has local `G₁`-models, the pullback of
the component is the comparison-conjugate of the component at the pulled-back object (which is a
local model up to a fiber iso), and the agreement transports there. -/
private theorem comparison_owner_iso_fiberwise_ext_of_source_image
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {F F' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (γ γ' : F ≅ F')
    (hsrc :
      ∀ {V : C} (z : X.p.Fiber V),
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V
            ((FibredCategoryMor.fiberFunctor G₁ V).obj z)).hom =
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ') V
            ((FibredCategoryMor.fiberFunctor G₁ V).obj z)).hom)
    {U : C} (x : Y₁.p.Fiber U) :
    (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) U x).hom =
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ') U x).hom := by
  -- Choose a cover with local source models for `x`.
  obtain ⟨S, hS⟩ := hG₁.locallyEssentiallySurjectiveOnObjects U x
  -- It suffices to check the agreement after pulling back to each cover arrow.
  apply stack_cover_hom_ext (J := J) Y₂ S
  intro I
  obtain ⟨xI, ⟨cI⟩⟩ := hS I
  -- `cI : (fiberFunctor G₁ I.Y).obj xI ≅ I.f ^*[Y₁.p] x`.
  -- The pullback of the component at `x` along `I.f` is the comparison-conjugate of the component
  -- at `I.f ^* x`, by the bridge — the same for `γ` and `γ'` (same `F`, `F'`).
  rw [basedFiberFunctorIso_pullback_bridge γ I.f x,
    basedFiberFunctorIso_pullback_bridge γ' I.f x]
  -- The comparisons agree, so reduce to the component at `I.f ^* x`.
  congr 2
  -- Component at `I.f ^* x` agrees: transport from the local `G₁`-model `xI` across `cI`.
  rw [basedFiberFunctorIso_transport_of_fiberIso γ cI,
    basedFiberFunctorIso_transport_of_fiberIso γ' cI]
  -- The middle component (at `G₁(xI)`) agrees by hypothesis; the outer fiber-functor maps of `cI`
  -- are identical since `F`, `F'` are fixed.
  rw [hsrc xI]

/-- Helper for Lemma 8.8.1 (faithfulness): two stack `2`-isomorphisms whose precompositions by
`G₁` agree are equal. The fiberwise agreement on `G₁`-images descends to all fibers via
`comparison_owner_iso_fiberwise_ext_of_source_image`. -/
private theorem precompose_mapIso_injective
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    {H H' : Y₁ ⟶ Y₂} (β β' : H ≅ H')
    (h :
      (stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β =
        (stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β') :
    β = β' := by
  -- The owner isos of `H, H'` (forget β, β' to the FibredCategoryMor level).
  set γ : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver :=
    stack_morphism_toFibredCategoryMor H with hγdef
  set γ' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver :=
    stack_morphism_toFibredCategoryMor H' with hγ'def
  let γβ : γ ≅ γ' :=
    Functor.mapIso ((stackOverSubTwoCategory J).hom Y₁ Y₂).inclusion β
  let γβ' : γ ≅ γ' :=
    Functor.mapIso ((stackOverSubTwoCategory J).hom Y₁ Y₂).inclusion β'
  -- The components of `P.mapIso β` at source objects agree with those of `P.mapIso β'`, hence the
  -- based components of `β`, `β'` agree on every `G₁`-image.
  have hsrc :
      ∀ {V : C} (z : X.p.Fiber V),
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γβ) V
            ((FibredCategoryMor.fiberFunctor G₁ V).obj z)).hom =
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γβ') V
            ((FibredCategoryMor.fiberFunctor G₁ V).obj z)).hom := by
    intro V z
    apply Functor.Fiber.hom_ext
    -- Reduce to the based components at `G₁(z).1`.
    show (FibredCategoryMor.basedFunctorIsoOfOwnerIso γβ).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor G₁ V).obj z).1 =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso γβ').hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor G₁ V).obj z).1
    -- These are exactly the based components of `β`, `β'` at the image objects.
    have key :
        (β.hom.hom.hom.hom.hom).toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G₁ V).obj z).1 =
          (β'.hom.hom.hom.hom.hom).toNatTrans.app
            ((FibredCategoryMor.fiberFunctor G₁ V).obj z).1 := by
      -- From `h`, the precompose components agree at the source object `z.1`.
      have hcomp := congrArg
        (fun (e : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅
            (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H') ↦
          (e.hom.hom.hom.toNatTrans.app z.1)) h
      simp only at hcomp
      -- Translate both sides via `precompose_mapIso_app`.
      rw [precompose_mapIso_app G₁ β z.1, precompose_mapIso_app G₁ β' z.1] at hcomp
      exact hcomp
    exact key
  -- Now lift fiberwise agreement to global owner-iso agreement, then to `β = β'`.
  apply stack_twoIso_ext
  intro T
  -- Reduce the based components of `β`, `β'` at `T` to the fiber components of `γβ`, `γβ'`.
  show (FibredCategoryMor.basedFunctorIsoOfOwnerIso γβ).hom.toNatTrans.app T =
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso γβ').hom.toNatTrans.app T
  rw [basedFiberFunctorIso_hom_one γβ T, basedFiberFunctorIso_hom_one γβ' T]
  -- The fiber components agree on all fibers, by descent from the `G₁`-image agreement.
  rw [comparison_owner_iso_fiberwise_ext_of_source_image (J := J) G₁ hG₁ γβ γβ' hsrc ⟨T, rfl⟩]

/-- Helper for Lemma 8.8.1 (object descent, the comparison `2`-iso component as an iso): the iso
form of `realForcedHom`, transporting the X-side forced fiber component `cFiberComp G₁ c x` across
a chosen `G₁`-model iso `cx`. Its `hom` is `realForcedHom G₁ c y x cx` by `rfl`. -/
noncomputable def realForcedHomIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J} (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    ((FibredCategoryMor.fiberFunctor K W).obj y) ≅ ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
  (FibredCategoryMor.fiberFunctor K W).mapIso cx.symm ≪≫ (cFiberComp G₁ c x) ≪≫
    (FibredCategoryMor.fiberFunctor K' W).mapIso cx

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1: the pullback-comparison cocycle for a composite base arrow
holds after applying a fibred morphism. -/
private theorem pbc_base_cocycle
    {X Y : FibredCategoryOver C} (K : X ⟶ Y)
    {W Z Wmid : C} (i_f : Wmid ⟶ W) (fi : Z ⟶ Wmid) (q : Z ⟶ W)
    (hq : fi ≫ i_f = q)
    (y : X.p.Fiber W) :
    ((canonicalFiberPseudofunctor Y.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
        (by rw [← FibredCategoryMor.comp_toLoc_eq i_f fi q hq])).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
      ((canonicalFiberPseudofunctor Y.p).map fi.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison K i_f y).hom ≫
        (FibredCategoryMor.pullbackComparison K fi
          (i_f ^*[canonicalPullbackChoice X.p] y)).hom =
      (FibredCategoryMor.pullbackComparison K q y).hom ≫
        (FibredCategoryMor.fiberFunctor K Z).map
          ((((canonicalFiberPseudofunctor X.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
              (by rw [← FibredCategoryMor.comp_toLoc_eq i_f fi q hq])).hom.toNatTrans.app y)) := by
  -- Compare the two vertical arrows by postcomposing with the chosen cartesian arrow over `q`.
  apply Functor.Fiber.hom_ext
  set Kf := FibredCategoryMor.fiberFunctor K W with hKf
  set θ : ((FibredCategoryMor.fiberFunctor K Z).obj
        (fi ^*[canonicalPullbackChoice X.p] (i_f ^*[canonicalPullbackChoice X.p] y))).1 ⟶
      (Kf.obj y).1 :=
    K.toHom.map ((canonicalPullbackChoice X.p).map fi (i_f ^*[canonicalPullbackChoice X.p] y)) ≫
      K.toHom.map ((canonicalPullbackChoice X.p).map i_f y) with hθ
  have hθcart : Y.p.IsStronglyCartesian q θ := by
    letI hcart_fi : Y.p.IsStronglyCartesian fi
        (K.toHom.map ((canonicalPullbackChoice X.p).map fi
          (i_f ^*[canonicalPullbackChoice X.p] y))) :=
      FibredCategoryMor.map_stronglyCartesian_of_lift K fi
        ((canonicalPullbackChoice X.p).map fi (i_f ^*[canonicalPullbackChoice X.p] y))
        ((canonicalPullbackChoice X.p).isStronglyCartesian fi
          (i_f ^*[canonicalPullbackChoice X.p] y))
    letI hcart_if : Y.p.IsStronglyCartesian i_f
        (K.toHom.map ((canonicalPullbackChoice X.p).map i_f y)) :=
      FibredCategoryMor.map_stronglyCartesian_of_lift K i_f
        ((canonicalPullbackChoice X.p).map i_f y)
        ((canonicalPullbackChoice X.p).isStronglyCartesian i_f y)
    have hcomp : Y.p.IsStronglyCartesian (fi ≫ i_f) θ := by
      rw [hθ]
      infer_instance
    rwa [hq] at hcomp
  letI : Y.p.IsStronglyCartesian q θ := hθcart
  set Ahom := ((canonicalFiberPseudofunctor Y.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
      (by rw [← FibredCategoryMor.comp_toLoc_eq i_f fi q hq])).hom.toNatTrans.app (Kf.obj y)
    with hAhom
  set cI_X := (((canonicalFiberPseudofunctor X.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
      (by rw [← FibredCategoryMor.comp_toLoc_eq i_f fi q hq])).hom.toNatTrans.app y)
    with hcI_X
  refine Functor.IsStronglyCartesian.ext Y.p q θ (𝟙 Z) ?_
  show (Ahom.1 ≫
        (((canonicalFiberPseudofunctor Y.p).map fi.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison K i_f y).hom).1 ≫
          (FibredCategoryMor.pullbackComparison K fi
            (i_f ^*[canonicalPullbackChoice X.p] y)).hom.1) ≫ θ =
      ((FibredCategoryMor.pullbackComparison K q y).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor K Z).map cI_X).1) ≫ θ
  -- Both composites postcomposed with `θ` are the chosen pullback arrow over `q`.
  have hXfac : cI_X.1 ≫
        (canonicalPullbackChoice X.p).map fi (i_f ^*[canonicalPullbackChoice X.p] y) ≫
        (canonicalPullbackChoice X.p).map i_f y =
      (canonicalPullbackChoice X.p).map q y := by
    have := FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      X.p i_f fi q hq y
    simpa only [hcI_X] using this
  have hYfac : Ahom.1 ≫
        (canonicalPullbackChoice Y.p).map fi
          (((canonicalFiberPseudofunctor Y.p).map i_f.op.toLoc).toFunctor.obj (Kf.obj y)) ≫
        (canonicalPullbackChoice Y.p).map i_f (Kf.obj y) =
      (canonicalPullbackChoice Y.p).map q (Kf.obj y) := by
    have := FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      Y.p i_f fi q hq (Kf.obj y)
    simpa only [hAhom] using this
  have hθ1 : θ =
      K.toHom.map ((canonicalPullbackChoice X.p).map fi (i_f ^*[canonicalPullbackChoice X.p] y)) ≫
        K.toHom.map ((canonicalPullbackChoice X.p).map i_f y) := hθ
  have hKZ : ((FibredCategoryMor.fiberFunctor K Z).map cI_X).1 = K.toHom.map cI_X.1 := rfl
  have hMfi := FibredCategoryMor.canonical_pullbackFunctor_map_fac Y.p fi
      (FibredCategoryMor.pullbackComparison K i_f y).hom
  have hRHS : ((FibredCategoryMor.pullbackComparison K q y).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor K Z).map cI_X).1) ≫ θ =
      (canonicalPullbackChoice Y.p).map q (Kf.obj y) := by
    rw [hKZ, hθ1]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [hXfac]
    exact FibredCategoryMor.pullbackComparison_hom_postcompose K q y
  have hpost_fi := FibredCategoryMor.pullbackComparison_hom_postcompose K fi
    (i_f ^*[canonicalPullbackChoice X.p] y)
  have hpost_if := FibredCategoryMor.pullbackComparison_hom_postcompose K i_f y
  have hLHS : (Ahom.1 ≫
        (((canonicalFiberPseudofunctor Y.p).map fi.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison K i_f y).hom).1 ≫
          (FibredCategoryMor.pullbackComparison K fi
            (i_f ^*[canonicalPullbackChoice X.p] y)).hom.1) ≫ θ =
      (canonicalPullbackChoice Y.p).map q (Kf.obj y) := by
    rw [hθ1]
    rw [Category.assoc, Category.assoc]
    rw [reassoc_of% hpost_fi]
    rw [reassoc_of% hMfi]
    rw [hpost_if]
    exact hYfac
  rw [hLHS, hRHS]

/-- Helper for Chap08 Lemma 8 8 1: the component of a pseudofunctorial composition comparison,
viewed as an isomorphism between the two chosen pullbacks. -/
private noncomputable def mapCompAppIso
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered]
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
/-- Helper for Chap08 Lemma 8 8 1: the pullback-comparison cocycle can be used directly as an
identity of isomorphisms. -/
private theorem pbc_base_cocycle_iso
    {X Y : FibredCategoryOver C} (K : X ⟶ Y)
    {W Z Wmid : C} (i_f : Wmid ⟶ W) (fi : Z ⟶ Wmid) (q : Z ⟶ W)
    (hq : fi ≫ i_f = q)
    (y : X.p.Fiber W) :
    (mapCompAppIso Y.p i_f fi q (FibredCategoryMor.comp_toLoc_eq i_f fi q hq)
        ((FibredCategoryMor.fiberFunctor K W).obj y) ≪≫
      ((canonicalFiberPseudofunctor Y.p).map fi.op.toLoc).toFunctor.mapIso
          (FibredCategoryMor.pullbackComparison K i_f y) ≪≫
        (FibredCategoryMor.pullbackComparison K fi
          (i_f ^*[canonicalPullbackChoice X.p] y))) =
      (FibredCategoryMor.pullbackComparison K q y) ≪≫
        (FibredCategoryMor.fiberFunctor K Z).mapIso
          (mapCompAppIso X.p i_f fi q (FibredCategoryMor.comp_toLoc_eq i_f fi q hq) y) := by
  -- The hom component is the previous cocycle; the inverse component follows from isomorphism
  -- extensionality.
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, mapCompAppIso]
  exact pbc_base_cocycle K i_f fi q hq y

/-- Helper for Chap08 Lemma 8 8 1: changing the base object of a forced morphism by a fiber
isomorphism only conjugates the two outer transport maps. -/
private theorem realForcedHom_base_transport
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J} (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} {y y' : Y₁.p.Fiber W} (cI : y ≅ y')
    (x' : X.p.Fiber W)
    (cx' : ((FibredCategoryMor.fiberFunctor G₁ W).obj x') ≅ y') :
    (FibredCategoryMor.fiberFunctor K W).map cI.hom ≫
        realForcedHom G₁ c y' x' cx' ≫
        (FibredCategoryMor.fiberFunctor K' W).map cI.inv =
      realForcedHom G₁ c y x' (cx' ≪≫ cI.symm) := by
  -- Unfold the two forced morphisms; the composed model has exactly the conjugated hom and inv.
  dsimp only [realForcedHom]
  have hinv : (cx' ≪≫ cI.symm).inv = cI.hom ≫ cx'.inv := rfl
  have hhom : (cx' ≪≫ cI.symm).hom = cx'.hom ≫ cI.inv := rfl
  rw [hinv, hhom, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Lemma 8.8.1: cancel one `inv ≫ hom` block in the middle of an associated
categorical composite. -/
private theorem comp_inv_hom_assoc_cancel
    {Cat : Type*} [Category Cat] {A B C D : Cat}
    (a : A ⟶ B) (e : C ≅ B) (b : B ⟶ D) :
    (a ≫ e.inv) ≫ (e.hom ≫ b) = a ≫ b := by
  calc
    (a ≫ e.inv) ≫ (e.hom ≫ b) = a ≫ (e.inv ≫ e.hom) ≫ b := by
      simp only [Category.assoc]
    _ = a ≫ 𝟙 _ ≫ b := by
      rw [e.inv_hom_id]
    _ = a ≫ b := by
      simp only [Category.id_comp]

/-- Helper for Lemma 8.8.1: combine two outer cocycle normalizations with one middle transport
normalization in a long categorical sandwich. -/
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
  calc
    a ≫ (b ≫ (c ≫ f ≫ g) ≫ h) ≫ i =
        (a ≫ b ≫ c) ≫ f ≫ (g ≫ h ≫ i) := by
          simp only [Category.assoc]
    _ = (d ≫ e) ≫ f ≫ (j ≫ k) := by
      rw [hL, hR]
    _ = d ≫ (e ≫ f ≫ j) ≫ k := by
      simp only [Category.assoc]
    _ = d ≫ n ≫ k := by
      rw [hM]

/-- Helper for Lemma 8.8.1: cancel a common conjugation shell from both sides of a categorical
equality. -/
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

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.8.1 (object descent, the descent-data cocycle for the comparison `2`-iso):
the per-arrow comparison components `e I` (pullback-comparison conjugates of the X-side
`realForcedHomIso` over the chosen local model of `I.f ^* y`) assemble into a morphism of
fixed-cover descent data. The cocycle identity is, on each overlap `(q, f₁, f₂)`, the equality of
the two `mapComp'` legs after applying `Mᶠ`; both sides reduce — by the pullback bridge
`Mf_realForcedHom_pullback` followed by the model independence `realForcedHom_model_indep` — to the
same forced fiber morphism over the overlap base object `Z` (of `q ^* y`). -/
private theorem realComparisonComponent_comm
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (S : J.Cover W)
    (model : ∀ I : S.Arrow, Σ' (xI : X.p.Fiber I.Y),
      ((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅ (I.f ^*[canonicalPullbackChoice Y₁.p] y))
    (e : ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor K W).obj y)).obj I ≅
        (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor K' W).obj y)).obj I)
    (he : ∀ I : S.Arrow, e I =
        (FibredCategoryMor.pullbackComparison K I.f y) ≪≫
        realForcedHomIso G₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y) (model I).1 (model I).2 ≪≫
        (FibredCategoryMor.pullbackComparison K' I.f y).symm) :
    ∀ ⦃Z : C⦄ (q : Z ⟶ W) ⦃i₁ i₂ : S.Arrow⦄ (f₁ : Z ⟶ i₁.Y) (f₂ : Z ⟶ i₂.Y)
      (hf₁ : f₁ ≫ i₁.f = q) (hf₂ : f₂ ≫ i₂.f = q),
      ((canonicalFiberPseudofunctor Y₂.p).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor K' W).obj y)).hom q f₁ f₂ hf₁ hf₂ =
        (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor K W).obj y)).hom q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor Y₂.p).map f₂.op.toLoc).toFunctor.map (e i₂).hom := by
  intro Z q i₁ i₂ f₁ f₂ hf₁ hf₂
  have key : ∀ (i : S.Arrow) (fi : Z ⟶ i.Y) (hfi : fi ≫ i.f = q),
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i.f.op.toLoc fi.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i.f fi q hfi])).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map fi.op.toLoc).toFunctor.map (e i).hom ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' i.f.op.toLoc fi.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i.f fi q hfi])).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' W).obj y) =
        (FibredCategoryMor.pullbackComparison K q y).hom ≫
          realForcedHom G₁ c (q ^*[canonicalPullbackChoice Y₁.p] y)
            (fi ^*[canonicalPullbackChoice X.p] (model i).1)
            (((FibredCategoryMor.pullbackComparison G₁ fi (model i).1).symm ≪≫
                (((canonicalFiberPseudofunctor Y₁.p).map fi.op.toLoc).toFunctor.mapIso
                  (model i).2)) ≪≫
              (mapCompAppIso Y₁.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)
                y).symm) ≫
          (FibredCategoryMor.pullbackComparison K' q y).inv := by
    intro i fi hfi
    have hei : (e i).hom =
        (FibredCategoryMor.pullbackComparison K i.f y).hom ≫
          realForcedHom G₁ c (i.f ^*[canonicalPullbackChoice Y₁.p] y) (model i).1
            (model i).2 ≫
          (FibredCategoryMor.pullbackComparison K' i.f y).inv := by
      rw [he i]
      rfl
    rw [hei, Functor.map_comp, Functor.map_comp]
    rw [Mf_realForcedHom_pullback G₁ c fi
      (i.f ^*[canonicalPullbackChoice Y₁.p] y) (model i).1 (model i).2]
    have hBK := congrArg (fun (t : _ ≅ _) => t.hom)
      (pbc_base_cocycle_iso K i.f fi q hfi y)
    have hBK' := congrArg (fun (t : _ ≅ _) => t.inv)
      (pbc_base_cocycle_iso K' i.f fi q hfi y)
    simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc] at hBK hBK'
    have hAhomK :
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i.f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y) =
        (mapCompAppIso Y₂.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)
          ((FibredCategoryMor.fiberFunctor K W).obj y)).hom := rfl
    have hAinvK' :
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i.f.op.toLoc fi.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' W).obj y) =
        (mapCompAppIso Y₂.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)
          ((FibredCategoryMor.fiberFunctor K' W).obj y)).inv := rfl
    rw [hAhomK, hAinvK']
    simp only [Category.assoc]
    rw [reassoc_of% hBK]
    rw [hBK']
    have mid_eq := realForcedHom_base_transport (W := Z) G₁ c
      (mapCompAppIso Y₁.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi) y)
      (fi ^*[canonicalPullbackChoice X.p] (model i).1)
      ((FibredCategoryMor.pullbackComparison G₁ fi (model i).1).symm ≪≫
        (((canonicalFiberPseudofunctor Y₁.p).map fi.op.toLoc).toFunctor.mapIso (model i).2))
    rw [reassoc_of% mid_eq]
  have hTeq :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' W).obj y) =
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map f₂.op.toLoc).toFunctor.map (e i₂).hom ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' W).obj y) := by
    rw [key i₁ f₁ hf₁, key i₂ f₂ hf₂]
    rw [realForcedHom_model_indep G₁ hG₁ c (q ^*[canonicalPullbackChoice Y₁.p] y)
      (f₁ ^*[canonicalPullbackChoice X.p] (model i₁).1) _
      (f₂ ^*[canonicalPullbackChoice X.p] (model i₂).1) _]
  dsimp only [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  have hcancel_K₁ :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y) = 𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hcancel_K'₂ :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' W).obj y) ≫
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' W).obj y) = 𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hA1 :
      ((canonicalFiberPseudofunctor Y₂.p).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' W).obj y) =
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
          (((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
            ((canonicalFiberPseudofunctor Y₂.p).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
            ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K' W).obj y)) := by
    rw [← Category.assoc, hcancel_K₁, Category.id_comp]
  have hA2 :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map f₂.op.toLoc).toFunctor.map (e i₂).hom =
        (((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
            ((canonicalFiberPseudofunctor Y₂.p).map f₂.op.toLoc).toFunctor.map (e i₂).hom ≫
            ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K' W).obj y)) ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' W).obj y) := by
    rw [Category.assoc, Category.assoc, hcancel_K'₂]
    simp
  rw [reassoc_of% hA1]
  conv_rhs => rw [Category.assoc, hA2]
  rw [reassoc_of% hTeq]
  simp only [Category.assoc]

/-- Helper for Lemma 8.8.1 (object descent, GLOBAL comparison `2`-iso component): the global fiber
component `K(y) ≅ K'(y)` over an arbitrary object `y : Y₁.p.Fiber W` produced by gluing the
per-arrow forced components `e I` across a stackification cover into a single global vertical
isomorphism (the source `c` being the X-side owner iso `G₁ ≫ K ≅ G₁ ≫ K'`). It is the
descent-data essential preimage of the glued data, hence the unique global iso whose pullbacks to
the cover are the forced components. -/
noncomputable def realComparisonComponent
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) :
    ((FibredCategoryMor.fiberFunctor K W).obj y) ≅ ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
  let hsurj := hG₁.locallyEssentiallySurjectiveOnObjects W y
  let S : J.Cover W := hsurj.choose
  let model : ∀ I : S.Arrow, Σ' (xI : X.p.Fiber I.Y),
      ((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅ (I.f ^*[canonicalPullbackChoice Y₁.p] y) :=
    fun I => ⟨(hsurj.choose_spec I).choose, (hsurj.choose_spec I).choose_spec.some⟩
  let Φ := (canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)
  let e : ∀ I : S.Arrow, (Φ.obj ((FibredCategoryMor.fiberFunctor K W).obj y)).obj I ≅
        (Φ.obj ((FibredCategoryMor.fiberFunctor K' W).obj y)).obj I :=
    fun I => (FibredCategoryMor.pullbackComparison K I.f y) ≪≫
        realForcedHomIso G₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y) (model I).1 (model I).2 ≪≫
        (FibredCategoryMor.pullbackComparison K' I.f y).symm
  let ddIso : Φ.obj ((FibredCategoryMor.fiberFunctor K W).obj y) ≅
      Φ.obj ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
    Pseudofunctor.DescentData.isoMk e
      (realComparisonComponent_comm G₁ hG₁ c y S model e (fun I => rfl))
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := Y₂.p)).1 inferInstance W S
  (Functor.FullyFaithful.ofFullyFaithful Φ).preimageIso ddIso

/-- Helper for Lemma 8.8.1: the fixed local-essential-image cover used by
`realComparisonComponent`. -/
private noncomputable def realComparisonComponentCover
    {X : FibredCategoryOver C} {Y₁ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {W : C} (y : Y₁.p.Fiber W) :
    J.Cover W :=
  (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose

/-- Helper for Lemma 8.8.1: the chosen cover used by `realComparisonComponent` locally represents
the target fiber object. -/
private theorem realComparisonComponentCover_spec
    {X : FibredCategoryOver C} {Y₁ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {W : C} (y : Y₁.p.Fiber W) :
    ∀ I : (realComparisonComponentCover (J := J) G₁ hG₁ y).Arrow,
      ∃ xI : X.p.Fiber I.Y,
        Nonempty
          (((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅
            I.f ^*[canonicalPullbackChoice Y₁.p] y) := by
  exact (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose_spec

/-- Helper for Lemma 8.8.1: the chosen local source model used by the comparison component on an
arrow of its local-essential-image cover. -/
private noncomputable def realComparisonComponentModel
    {X : FibredCategoryOver C} {Y₁ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {W : C} (y : Y₁.p.Fiber W)
    (I : (realComparisonComponentCover (J := J) G₁ hG₁ y).Arrow) :
    Σ' xI : X.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice Y₁.p] y :=
  ⟨Classical.choose (realComparisonComponentCover_spec (J := J) G₁ hG₁ y I),
    Classical.choice
      (Classical.choose_spec
        (realComparisonComponentCover_spec (J := J) G₁ hG₁ y I))⟩

/-- Helper for Lemma 8.8.1 (object descent): the pullback of the global comparison `2`-iso
component `realComparisonComponent` along a cover arrow `I.f` is, for some chosen local source
model `(x, cx)` of `I.f ^* y`, the pullback-comparison conjugate of the X-side forced fiber
morphism over `I.f ^* y`. This reads off the descent-data essential-preimage relation. -/
private theorem realComparisonComponent_pullback_eq
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (I : (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose.Arrow) :
    ∃ (x : X.p.Fiber I.Y)
      (cx : ((FibredCategoryMor.fiberFunctor G₁ I.Y).obj x) ≅
        (I.f ^*[canonicalPullbackChoice Y₁.p] y)),
    ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
        (realComparisonComponent G₁ hG₁ c y).hom =
      (FibredCategoryMor.pullbackComparison K I.f y).hom ≫
        realForcedHom G₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y) x cx ≫
        (FibredCategoryMor.pullbackComparison K' I.f y).inv := by
  refine ⟨((hG₁.locallyEssentiallySurjectiveOnObjects W y).choose_spec I).choose,
    ((hG₁.locallyEssentiallySurjectiveOnObjects W y).choose_spec I).choose_spec.some, ?_⟩
  dsimp only [realComparisonComponent]
  rw [Functor.FullyFaithful.preimageIso_hom]
  set Φ := (canonicalFiberPseudofunctor Y₂.p).toDescentData
    (fun I : (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose.Arrow ↦ I.f) with hΦ
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence (J := J) (p := Y₂.p)).1
      inferInstance W (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose
  change (Φ.map ((Functor.FullyFaithful.ofFullyFaithful Φ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- Helper for Lemma 8.8.1: the chosen local model for a cover arrow gives the stored pullback
formula for `realComparisonComponent`. -/
private theorem realComparisonComponent_cover_pullback
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (I : (realComparisonComponentCover (J := J) G₁ hG₁ y).Arrow) :
    ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
        (realComparisonComponent G₁ hG₁ c y).hom =
      (FibredCategoryMor.pullbackComparison K I.f y).hom ≫
        realForcedHom G₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y)
          (realComparisonComponentModel (J := J) G₁ hG₁ y I).1
          (realComparisonComponentModel (J := J) G₁ hG₁ y I).2 ≫
        (FibredCategoryMor.pullbackComparison K' I.f y).inv := by
  dsimp only [realComparisonComponent]
  rw [Functor.FullyFaithful.preimageIso_hom]
  set Φ := (canonicalFiberPseudofunctor Y₂.p).toDescentData
    (fun I : (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose.Arrow ↦ I.f) with hΦ
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence (J := J) (p := Y₂.p)).1
      inferInstance W (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose
  change (Φ.map ((Functor.FullyFaithful.ofFullyFaithful Φ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- Helper for Lemma 8.8.1 (object descent, CHARACTERIZATION): on any source model `(x, cx)` of an
arbitrary object `y`, the hom of the global comparison `2`-iso component `realComparisonComponent`
equals the X-side forced fiber morphism `realForcedHom G₁ c y x cx`. It is verified coverwise: the
pullback along each cover arrow is the forced morphism over the pulled-back object for a local
model, which agrees with the pulled-back `(x, cx)`-model by `realForcedHom_model_indep`. -/
private theorem realComparisonComponent_eq_forced
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    (realComparisonComponent G₁ hG₁ c y).hom = realForcedHom G₁ c y x cx := by
  apply stack_cover_hom_ext (J := J) Y₂ (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose
  intro I
  obtain ⟨xI, cxI, hI⟩ := realComparisonComponent_pullback_eq G₁ hG₁ c y I
  rw [hI, Mf_realForcedHom_pullback G₁ c I.f y x cx]
  rw [realForcedHom_model_indep G₁ hG₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y)
    xI cxI
    (I.f ^*[canonicalPullbackChoice X.p] x)
    ((FibredCategoryMor.pullbackComparison G₁ I.f x).symm ≪≫
      (((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.mapIso cx))]

/-- Helper for Lemma 8.8.1 (object descent, X-side image normal form): on a `G₁`-image object
`(G₁.fiberFunctor W).obj x`, the global comparison `2`-iso component is the X-side forced fiber
component `cFiberComp G₁ c x` (i.e. the restriction of the based-functor iso of `c` to that fiber).
This is the characterization on the trivial model `(x, Iso.refl _)`. -/
private theorem realComparisonComponent_on_image
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (x : X.p.Fiber W) :
    (realComparisonComponent G₁ hG₁ c ((FibredCategoryMor.fiberFunctor G₁ W).obj x)).hom =
      (cFiberComp G₁ c x).hom := by
  rw [realComparisonComponent_eq_forced G₁ hG₁ c
    ((FibredCategoryMor.fiberFunctor G₁ W).obj x) x (Iso.refl _)]
  show (FibredCategoryMor.fiberFunctor K W).map (Iso.refl _).inv ≫
      (cFiberComp G₁ c x).hom ≫ (FibredCategoryMor.fiberFunctor K' W).map (Iso.refl _).hom =
    (cFiberComp G₁ c x).hom
  simp only [Iso.refl_inv, Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 1: saturated downstream surface for the characterization of the
glued comparison component by a chosen source model. -/
private theorem realComparisonComponent_eq_forced_saturated
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, max u v, max u v} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    (realComparisonComponent G₁ hG₁ c y).hom = realForcedHom G₁ c y x cx := by
  -- This records the saturated API shape without replaying the descent proof.
  exact realComparisonComponent_eq_forced (J := J) G₁ hG₁ c y x cx

/-- Helper for Chap08 Lemma 8 8 1: saturated downstream surface for the comparison component on a
`G₁`-image object. -/
private theorem realComparisonComponent_on_image_saturated
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, max u v, max u v} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (x : X.p.Fiber W) :
    (realComparisonComponent G₁ hG₁ c ((FibredCategoryMor.fiberFunctor G₁ W).obj x)).hom =
      (cFiberComp G₁ c x).hom := by
  -- Reuse the established image normal form at the saturated stack surface.
  exact realComparisonComponent_on_image (J := J) G₁ hG₁ c x

/-- Helper for Lemma 8.8.1: the pseudofunctorial composition shell around a pulled-back
comparison component collapses to the single composite-base pullback. -/
private theorem realComparisonComponent_mapComp_naturality
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (q : W ⟶ U)
    (hgq : g ≫ f = q) (y : Y₁.p.Fiber U) :
    ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g q hgq)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K U).obj y) ≫
        ((canonicalFiberPseudofunctor Y₂.p).map g.op.toLoc).toFunctor.map
          (((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
            (realComparisonComponent G₁ hG₁ c y).hom) ≫
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g q hgq)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' U).obj y) =
      ((canonicalFiberPseudofunctor Y₂.p).map q.op.toLoc).toFunctor.map
        (realComparisonComponent G₁ hG₁ c y).hom := by
  exact
    (canonicalFiberPseudofunctor Y₂.p).mapComp'_naturality_2
      f.op.toLoc g.op.toLoc q.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq f g q hgq)
      (realComparisonComponent G₁ hG₁ c y).hom

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.8.1: `realComparisonComponent` commutes with pullback at the fiber level,
up to the two standard pullback-comparison isomorphisms. -/
private theorem realComparisonComponent_pullback_factor_hom
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {U V : C} (f : V ⟶ U) (y : Y₁.p.Fiber U) :
    ((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
        (realComparisonComponent G₁ hG₁ c y).hom =
      (FibredCategoryMor.pullbackComparison K f y).hom ≫
        (realComparisonComponent G₁ hG₁ c
          (f ^*[canonicalPullbackChoice Y₁.p] y)).hom ≫
        (FibredCategoryMor.pullbackComparison K' f y).inv := by
  apply stack_cover_hom_ext (J := J) Y₂
    (((realComparisonComponentCover (J := J) G₁ hG₁ y).pullback f) ⊓
      realComparisonComponentCover (J := J) G₁ hG₁
        (f ^*[canonicalPullbackChoice Y₁.p] y))
  intro I
  let Ileft :=
    I.map (homOfLE inf_le_left :
      (((realComparisonComponentCover (J := J) G₁ hG₁ y).pullback f) ⊓
        realComparisonComponentCover (J := J) G₁ hG₁
          (f ^*[canonicalPullbackChoice Y₁.p] y)) ⟶
        (realComparisonComponentCover (J := J) G₁ hG₁ y).pullback f)
  let Ibase := Ileft.base
  let Iright :=
    I.map (homOfLE inf_le_right :
      (((realComparisonComponentCover (J := J) G₁ hG₁ y).pullback f) ⊓
        realComparisonComponentCover (J := J) G₁ hG₁
          (f ^*[canonicalPullbackChoice Y₁.p] y)) ⟶
        realComparisonComponentCover (J := J) G₁ hG₁
          (f ^*[canonicalPullbackChoice Y₁.p] y))
  let q : I.Y ⟶ U := I.f ≫ f
  have hLeftShell :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K U).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
              (realComparisonComponent G₁ hG₁ c y).hom) ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' U).obj y) =
        (FibredCategoryMor.pullbackComparison K q y).hom ≫
          realForcedHom G₁ c
            (q ^*[canonicalPullbackChoice Y₁.p] y)
            (realComparisonComponentModel (J := J) G₁ hG₁ y Ibase).1
            (realComparisonComponentModel (J := J) G₁ hG₁ y Ibase).2 ≫
          (FibredCategoryMor.pullbackComparison K' q y).inv := by
    have hShell :=
      realComparisonComponent_mapComp_naturality
        (J := J) G₁ hG₁ c f I.f q rfl y
    have hCover :=
      realComparisonComponent_cover_pullback
        (J := J) G₁ hG₁ c y Ibase
    calc
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K U).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
              (realComparisonComponent G₁ hG₁ c y).hom) ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' U).obj y) =
          ((canonicalFiberPseudofunctor Y₂.p).map q.op.toLoc).toFunctor.map
            (realComparisonComponent G₁ hG₁ c y).hom := hShell
      _ =
          (FibredCategoryMor.pullbackComparison K q y).hom ≫
            realForcedHom G₁ c
              (q ^*[canonicalPullbackChoice Y₁.p] y)
              (realComparisonComponentModel (J := J) G₁ hG₁ y Ibase).1
              (realComparisonComponentModel (J := J) G₁ hG₁ y Ibase).2 ≫
            (FibredCategoryMor.pullbackComparison K' q y).inv := by
          exact hCover
  have hRightShell :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K U).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison K f y).hom ≫
              (realComparisonComponent G₁ hG₁ c
                (f ^*[canonicalPullbackChoice Y₁.p] y)).hom ≫
              (FibredCategoryMor.pullbackComparison K' f y).inv) ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' U).obj y) =
        (FibredCategoryMor.pullbackComparison K q y).hom ≫
          realForcedHom G₁ c
            (q ^*[canonicalPullbackChoice Y₁.p] y)
            (realComparisonComponentModel (J := J) G₁ hG₁
              (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).1
            ((realComparisonComponentModel (J := J) G₁ hG₁
                (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).2 ≪≫
              (mapCompAppIso Y₁.p f I.f q
                (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) y).symm) ≫
          (FibredCategoryMor.pullbackComparison K' q y).inv := by
    have hCoverRight :=
      realComparisonComponent_cover_pullback
        (J := J) G₁ hG₁ c
        (f ^*[canonicalPullbackChoice Y₁.p] y) Iright
    have hCoverRightI :
        ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
            (realComparisonComponent G₁ hG₁ c
              (f ^*[canonicalPullbackChoice Y₁.p] y)).hom =
          (FibredCategoryMor.pullbackComparison K I.f
              (f ^*[canonicalPullbackChoice Y₁.p] y)).hom ≫
            realForcedHom G₁ c
              (I.f ^*[canonicalPullbackChoice Y₁.p]
                (f ^*[canonicalPullbackChoice Y₁.p] y))
              (realComparisonComponentModel (J := J) G₁ hG₁
                (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).1
              (realComparisonComponentModel (J := J) G₁ hG₁
                (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).2 ≫
            (FibredCategoryMor.pullbackComparison K' I.f
              (f ^*[canonicalPullbackChoice Y₁.p] y)).inv := by
      exact hCoverRight
    have hBK := congrArg (fun (t : _ ≅ _) => t.hom)
      (pbc_base_cocycle_iso K f I.f q rfl y)
    have hBK' := congrArg (fun (t : _ ≅ _) => t.inv)
      (pbc_base_cocycle_iso K' f I.f q rfl y)
    simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc] at hBK hBK'
    rw [Functor.map_comp, Functor.map_comp]
    rw [hCoverRightI]
    have hmid := realForcedHom_base_transport (W := I.Y) G₁ c
      (mapCompAppIso Y₁.p f I.f q (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) y)
      (realComparisonComponentModel (J := J) G₁ hG₁
        (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).1
      (realComparisonComponentModel (J := J) G₁ hG₁
        (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).2
    exact
      composeCocycleSandwich
        _ _ _ _ _ _ _ _ _ _ _ _
        hBK hBK' hmid
  have hShellEq :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K U).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor.map
              (realComparisonComponent G₁ hG₁ c y).hom) ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' U).obj y) =
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K U).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison K f y).hom ≫
              (realComparisonComponent G₁ hG₁ c
                (f ^*[canonicalPullbackChoice Y₁.p] y)).hom ≫
              (FibredCategoryMor.pullbackComparison K' f y).inv) ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' U).obj y) := by
    have hModel :=
      realForcedHom_model_indep
        (J := J) G₁ hG₁ c
        (q ^*[canonicalPullbackChoice Y₁.p] y)
        (realComparisonComponentModel (J := J) G₁ hG₁ y Ibase).1
        (realComparisonComponentModel (J := J) G₁ hG₁ y Ibase).2
        (realComparisonComponentModel (J := J) G₁ hG₁
          (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).1
        ((realComparisonComponentModel (J := J) G₁ hG₁
            (f ^*[canonicalPullbackChoice Y₁.p] y) Iright).2 ≪≫
          (mapCompAppIso Y₁.p f I.f q
            (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) y).symm)
    have hMiddle :=
      congrArg
        (fun m =>
          (FibredCategoryMor.pullbackComparison K q y).hom ≫ m ≫
            (FibredCategoryMor.pullbackComparison K' q y).inv)
        hModel
    exact hLeftShell.trans (hMiddle.trans hRightShell.symm)
  have hcancelK :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K U).obj y) ≫
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K U).obj y) =
        𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hcancelK' :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' U).obj y) ≫
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' f.op.toLoc I.f.op.toLoc q.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f I.f q rfl)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' U).obj y) =
        𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  exact
    eqOfConjugationShell
      _ _ _ _ _ _
      hcancelK hcancelK' hShellEq

/-- Helper for Lemma 8.8.1: vertical morphisms transported by a pullback functor are the
`pullbackComparison` conjugate of the fiberwise transported morphism. -/
private theorem pullbackComparison_map_vertical_eq_hom_comp
    {Y Z : FibredCategoryOver C} (F : Y ⟶ Z)
    {U V : C} (f : V ⟶ U) {y y' : Y.p.Fiber U} (d : y ⟶ y') :
    ((canonicalFiberPseudofunctor Z.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor F U).map d) =
      (FibredCategoryMor.pullbackComparison F f y).hom ≫
        (FibredCategoryMor.fiberFunctor F V).map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map d) ≫
        (FibredCategoryMor.pullbackComparison F f y').inv := by
  have h :=
    FibredCategoryMor.pullbackComparison_naturality_over_vertical F f d
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).2 h

/-- Helper for Lemma 8.8.1: the comparison components are natural for vertical arrows inside a
fixed source fiber. -/
private theorem realComparisonComponent_vertical_naturality
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {U : C} {y y' : Y₁.p.Fiber U} (d : y ⟶ y') :
    (FibredCategoryMor.fiberFunctor K U).map d ≫
        (realComparisonComponent G₁ hG₁ c y').hom =
      (realComparisonComponent G₁ hG₁ c y).hom ≫
        (FibredCategoryMor.fiberFunctor K' U).map d := by
  obtain ⟨Scover, hScover⟩ := stackification_common_local_models (J := J) G₁ hG₁ y y'
  apply stack_cover_hom_ext (J := J) Y₂ Scover
  intro I
  obtain ⟨xI, xI', ⟨cxI⟩, ⟨cxI'⟩⟩ := hScover I
  let FY₂ := ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor
  let KfU := FibredCategoryMor.fiberFunctor K U
  let K'fU := FibredCategoryMor.fiberFunctor K' U
  let KfV := FibredCategoryMor.fiberFunctor K I.Y
  let K'fV := FibredCategoryMor.fiberFunctor K' I.Y
  let dI := ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d
  let ηy := (realComparisonComponent G₁ hG₁ c y).hom
  let ηy' := (realComparisonComponent G₁ hG₁ c y').hom
  let ηfy := (realComparisonComponent G₁ hG₁ c
    (I.f ^*[canonicalPullbackChoice Y₁.p] y)).hom
  let ηfy' := (realComparisonComponent G₁ hG₁ c
    (I.f ^*[canonicalPullbackChoice Y₁.p] y')).hom
  let cKy := FibredCategoryMor.pullbackComparison K I.f y
  let cKy' := FibredCategoryMor.pullbackComparison K I.f y'
  let cK'y := FibredCategoryMor.pullbackComparison K' I.f y
  let cK'y' := FibredCategoryMor.pullbackComparison K' I.f y'
  have hLeftMap :
      FY₂.map (KfU.map d ≫ ηy') = FY₂.map (KfU.map d) ≫ FY₂.map ηy' := by
    exact FY₂.map_comp (KfU.map d) ηy'
  have hRightMap :
      FY₂.map (ηy ≫ K'fU.map d) = FY₂.map ηy ≫ FY₂.map (K'fU.map d) := by
    exact FY₂.map_comp ηy (K'fU.map d)
  have hK :
      FY₂.map (KfU.map d) = cKy.hom ≫ KfV.map dI ≫ cKy'.inv := by
    exact pullbackComparison_map_vertical_eq_hom_comp K I.f d
  have hK' :
      FY₂.map (K'fU.map d) = cK'y.hom ≫ K'fV.map dI ≫ cK'y'.inv := by
    exact pullbackComparison_map_vertical_eq_hom_comp K' I.f d
  have hηy :
      FY₂.map ηy = cKy.hom ≫ ηfy ≫ cK'y.inv := by
    exact realComparisonComponent_pullback_factor_hom (J := J) G₁ hG₁ c I.f y
  have hηy' :
      FY₂.map ηy' = cKy'.hom ≫ ηfy' ≫ cK'y'.inv := by
    exact realComparisonComponent_pullback_factor_hom (J := J) G₁ hG₁ c I.f y'
  have hModelChosen : KfV.map dI ≫ ηfy' = ηfy ≫ K'fV.map dI := by
    change KfV.map dI ≫
        (realComparisonComponent G₁ hG₁ c
          (I.f ^*[canonicalPullbackChoice Y₁.p] y')).hom =
      (realComparisonComponent G₁ hG₁ c
          (I.f ^*[canonicalPullbackChoice Y₁.p] y)).hom ≫
        K'fV.map dI
    rw [realComparisonComponent_eq_forced
      (J := J) G₁ hG₁ c
      (I.f ^*[canonicalPullbackChoice Y₁.p] y') xI' cxI']
    rw [realComparisonComponent_eq_forced
      (J := J) G₁ hG₁ c
      (I.f ^*[canonicalPullbackChoice Y₁.p] y) xI cxI]
    exact realForcedHom_model_naturality (J := J) G₁ hG₁ c xI cxI xI' cxI' dI
  change FY₂.map (KfU.map d ≫ ηy') = FY₂.map (ηy ≫ K'fU.map d)
  have hLeftNormalized :
      FY₂.map (KfU.map d ≫ ηy') =
        cKy.hom ≫ (ηfy ≫ K'fV.map dI) ≫ cK'y'.inv := by
    calc
      FY₂.map (KfU.map d ≫ ηy') = FY₂.map (KfU.map d) ≫ FY₂.map ηy' := hLeftMap
      _ = (cKy.hom ≫ KfV.map dI ≫ cKy'.inv) ≫
            (cKy'.hom ≫ ηfy' ≫ cK'y'.inv) := by
            rw [hK, hηy']
            rfl
      _ = cKy.hom ≫ (KfV.map dI ≫ ηfy') ≫ cK'y'.inv := by
            simpa only [Category.assoc] using
              comp_inv_hom_assoc_cancel (cKy.hom ≫ KfV.map dI) cKy'
                (ηfy' ≫ cK'y'.inv)
      _ = cKy.hom ≫ (ηfy ≫ K'fV.map dI) ≫ cK'y'.inv := by
            exact congrArg (fun m ↦ cKy.hom ≫ m ≫ cK'y'.inv) hModelChosen
  have hRightNormalized :
      FY₂.map (ηy ≫ K'fU.map d) =
        cKy.hom ≫ (ηfy ≫ K'fV.map dI) ≫ cK'y'.inv := by
    calc
      FY₂.map (ηy ≫ K'fU.map d) = FY₂.map ηy ≫ FY₂.map (K'fU.map d) := hRightMap
      _ = (cKy.hom ≫ ηfy ≫ cK'y.inv) ≫
            (cK'y.hom ≫ K'fV.map dI ≫ cK'y'.inv) := by
            rw [hηy, hK']
            rfl
      _ = cKy.hom ≫ (ηfy ≫ K'fV.map dI) ≫ cK'y'.inv := by
            simpa only [Category.assoc] using
              comp_inv_hom_assoc_cancel (cKy.hom ≫ ηfy) cK'y
                (K'fV.map dI ≫ cK'y'.inv)
  exact hLeftNormalized.trans hRightNormalized.symm

/-- Helper for Lemma 8.8.1: the comparison components are natural along the canonical cartesian
pullback arrow of a source fiber object. -/
private theorem realComparisonComponent_cartesian_naturality
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {U V : C} (f : V ⟶ U) (y : Y₁.p.Fiber U) :
    (FibredCategoryMor.toFunctor K).map
        ((canonicalPullbackChoice Y₁.p).map f y) ≫
        (realComparisonComponent G₁ hG₁ c y).hom.1 =
      (realComparisonComponent G₁ hG₁ c
          (f ^*[canonicalPullbackChoice Y₁.p] y)).hom.1 ≫
        (FibredCategoryMor.toFunctor K').map
          ((canonicalPullbackChoice Y₁.p).map f y) := by
  let ηy := (realComparisonComponent G₁ hG₁ c y).hom
  let ηfy :=
    (realComparisonComponent G₁ hG₁ c
      (f ^*[canonicalPullbackChoice Y₁.p] y)).hom
  let M := ((canonicalFiberPseudofunctor Y₂.p).map f.op.toLoc).toFunctor
  let cK := FibredCategoryMor.pullbackComparison K f y
  let cK' := FibredCategoryMor.pullbackComparison K' f y
  let cartK' :=
    (canonicalPullbackChoice Y₂.p).map f
      ((FibredCategoryMor.fiberFunctor K' U).obj y)
  have hCore : M.map ηy = cK.hom ≫ ηfy ≫ cK'.inv := by
    exact realComparisonComponent_pullback_factor_hom (J := J) G₁ hG₁ c f y
  have hFactor : cK.inv ≫ M.map ηy = ηfy ≫ cK'.inv := by
    calc
      cK.inv ≫ M.map ηy = cK.inv ≫ (cK.hom ≫ ηfy ≫ cK'.inv) := by
        exact congrArg (fun m ↦ cK.inv ≫ m) hCore
      _ = (cK.inv ≫ cK.hom) ≫ (ηfy ≫ cK'.inv) := by
        simp only [Category.assoc]
      _ = ηfy ≫ cK'.inv := by
        rw [cK.inv_hom_id]
        simp only [Category.id_comp]
  have hPost :
      ((cK.inv ≫ M.map ηy).1) ≫ cartK' =
        ((ηfy ≫ cK'.inv).1) ≫ cartK' := by
    exact congrArg (fun m ↦ m.1 ≫ cartK') hFactor
  have hMap :
      (M.map ηy).1 ≫ cartK' =
        (canonicalPullbackChoice Y₂.p).map f
            ((FibredCategoryMor.fiberFunctor K U).obj y) ≫ ηy.1 := by
    exact FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := Y₂.p) (f := f)
      (φ := ηy)
  have hKpost :
      cK.inv.1 ≫
          (canonicalPullbackChoice Y₂.p).map f
            ((FibredCategoryMor.fiberFunctor K U).obj y) =
        (FibredCategoryMor.toFunctor K).map ((canonicalPullbackChoice Y₁.p).map f y) :=
    FibredCategoryMor.pullbackComparison_inv_postcompose_owner K f y
  have hK'post :
      cK'.inv.1 ≫ cartK' =
        (FibredCategoryMor.toFunctor K').map ((canonicalPullbackChoice Y₁.p).map f y) :=
    FibredCategoryMor.pullbackComparison_inv_postcompose_owner K' f y
  have hStart :
      ((cK.inv ≫ M.map ηy).1) ≫ cartK' =
        (FibredCategoryMor.toFunctor K).map ((canonicalPullbackChoice Y₁.p).map f y) ≫
          ηy.1 := by
    calc
      ((cK.inv ≫ M.map ηy).1) ≫ cartK' =
          cK.inv.1 ≫ ((M.map ηy).1 ≫ cartK') := by
            change (cK.inv.1 ≫ (M.map ηy).1) ≫ cartK' =
              cK.inv.1 ≫ ((M.map ηy).1 ≫ cartK')
            rw [Category.assoc]
      _ = cK.inv.1 ≫
            ((canonicalPullbackChoice Y₂.p).map f
              ((FibredCategoryMor.fiberFunctor K U).obj y) ≫ ηy.1) := by
            exact congrArg (fun m ↦ cK.inv.1 ≫ m) hMap
      _ = (cK.inv.1 ≫
            (canonicalPullbackChoice Y₂.p).map f
              ((FibredCategoryMor.fiberFunctor K U).obj y)) ≫ ηy.1 := by
            rw [← Category.assoc]
      _ = (FibredCategoryMor.toFunctor K).map ((canonicalPullbackChoice Y₁.p).map f y) ≫
            ηy.1 := by
            exact congrArg (fun m ↦ m ≫ ηy.1) hKpost
  have hEnd :
      ηfy.1 ≫
          (FibredCategoryMor.toFunctor K').map ((canonicalPullbackChoice Y₁.p).map f y) =
        ((ηfy ≫ cK'.inv).1) ≫ cartK' := by
    calc
      ηfy.1 ≫
          (FibredCategoryMor.toFunctor K').map ((canonicalPullbackChoice Y₁.p).map f y) =
          ηfy.1 ≫ (cK'.inv.1 ≫ cartK') := by
            exact congrArg (fun m ↦ ηfy.1 ≫ m) hK'post.symm
      _ = ((ηfy ≫ cK'.inv).1) ≫ cartK' := by
            change ηfy.1 ≫ (cK'.inv.1 ≫ cartK') = (ηfy.1 ≫ cK'.inv.1) ≫ cartK'
            rw [Category.assoc]
  exact hStart.symm.trans (hPost.trans hEnd.symm)

/-- Helper for Lemma 8.8.1: every total arrow factors through the chosen cartesian pullback of
its codomain by a vertical arrow in the source fiber. -/
private theorem canonicalPullback_verticalFactor_exists
    {T : Type uY} [Category.{vY} T] (p : T ⥤ C) [p.IsFibered]
    {A B : T} (φ : A ⟶ B) :
    ∃ v : (Functor.Fiber.mk (p := p) (a := A) rfl : p.Fiber (p.obj A)) ⟶
        (p.map φ ^*[canonicalPullbackChoice p]
          (Functor.Fiber.mk (p := p) (a := B) rfl : p.Fiber (p.obj B))),
      v.1 ≫
        (canonicalPullbackChoice p).map (p.map φ)
          (Functor.Fiber.mk (p := p) (a := B) rfl : p.Fiber (p.obj B)) = φ := by
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

/-- Helper for Lemma 8.8.1 (object descent, B3 naturality of the comparison `2`-iso): the global
comparison `2`-iso components `realComparisonComponent` are natural along every morphism `φ` of the
total source category of `Y₁`. This is the naturality square of the based natural transformation
underlying the comparison `2`-isomorphism. -/
private theorem realComparisonComponent_naturality
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {T T' : Y₁.S} (φ : T ⟶ T') :
    (FibredCategoryMor.toFunctor K).map φ ≫ (realComparisonComponent G₁ hG₁ c ⟨T', rfl⟩).hom.1 =
      (realComparisonComponent G₁ hG₁ c ⟨T, rfl⟩).hom.1 ≫
        (FibredCategoryMor.toFunctor K').map φ := by
  let yT : Y₁.p.Fiber (Y₁.p.obj T) :=
    Functor.Fiber.mk (p := Y₁.p) (a := T) rfl
  let yT' : Y₁.p.Fiber (Y₁.p.obj T') :=
    Functor.Fiber.mk (p := Y₁.p) (a := T') rfl
  let yPull : Y₁.p.Fiber (Y₁.p.obj T) :=
    Y₁.p.map φ ^*[canonicalPullbackChoice Y₁.p] yT'
  let cart : yPull.1 ⟶ T' := (canonicalPullbackChoice Y₁.p).map (Y₁.p.map φ) yT'
  obtain ⟨v, hv⟩ := canonicalPullback_verticalFactor_exists Y₁.p φ
  have hcart :=
    realComparisonComponent_cartesian_naturality
      (J := J) G₁ hG₁ c (Y₁.p.map φ) yT'
  have hvertFiber :=
    realComparisonComponent_vertical_naturality
      (J := J) G₁ hG₁ c v
  have hvert :
      (FibredCategoryMor.toFunctor K).map v.1 ≫
          (realComparisonComponent G₁ hG₁ c yPull).hom.1 =
        (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
          (FibredCategoryMor.toFunctor K').map v.1 := by
    exact congrArg (fun m => m.1) hvertFiber
  have hvcart : v.1 ≫ cart = φ := by
    simpa [cart, yT'] using hv
  have hcartTotal :
      (FibredCategoryMor.toFunctor K).map cart ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1 =
        (realComparisonComponent G₁ hG₁ c yPull).hom.1 ≫
          (FibredCategoryMor.toFunctor K').map cart := by
    exact hcart
  have hmapK :
      (FibredCategoryMor.toFunctor K).map (v.1 ≫ cart) =
        (FibredCategoryMor.toFunctor K).map v.1 ≫
          (FibredCategoryMor.toFunctor K).map cart := by
    exact (FibredCategoryMor.toFunctor K).map_comp v.1 cart
  have hmapK' :
      (FibredCategoryMor.toFunctor K').map (v.1 ≫ cart) =
        (FibredCategoryMor.toFunctor K').map v.1 ≫
          (FibredCategoryMor.toFunctor K').map cart := by
    exact (FibredCategoryMor.toFunctor K').map_comp v.1 cart
  change
    (FibredCategoryMor.toFunctor K).map φ ≫
        (realComparisonComponent G₁ hG₁ c yT').hom.1 =
      (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
        (FibredCategoryMor.toFunctor K').map φ
  have hstepStart :
      (FibredCategoryMor.toFunctor K).map φ ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1 =
        (FibredCategoryMor.toFunctor K).map (v.1 ≫ cart) ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1 := by
    exact congrArg
      (fun m ↦
        (FibredCategoryMor.toFunctor K).map m ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1)
      hvcart.symm
  have hstepMapK :
      (FibredCategoryMor.toFunctor K).map (v.1 ≫ cart) ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1 =
        ((FibredCategoryMor.toFunctor K).map v.1 ≫
            (FibredCategoryMor.toFunctor K).map cart) ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1 := by
    exact congrArg
      (fun m ↦ m ≫ (realComparisonComponent G₁ hG₁ c yT').hom.1) hmapK
  have hstepAssocLeft :
      ((FibredCategoryMor.toFunctor K).map v.1 ≫
          (FibredCategoryMor.toFunctor K).map cart) ≫
        (realComparisonComponent G₁ hG₁ c yT').hom.1 =
      (FibredCategoryMor.toFunctor K).map v.1 ≫
        ((FibredCategoryMor.toFunctor K).map cart ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1) := by
    rw [Category.assoc]
  have hstepCart :
      (FibredCategoryMor.toFunctor K).map v.1 ≫
        ((FibredCategoryMor.toFunctor K).map cart ≫
          (realComparisonComponent G₁ hG₁ c yT').hom.1) =
      (FibredCategoryMor.toFunctor K).map v.1 ≫
        ((realComparisonComponent G₁ hG₁ c yPull).hom.1 ≫
          (FibredCategoryMor.toFunctor K').map cart) := by
    exact congrArg (fun m ↦ (FibredCategoryMor.toFunctor K).map v.1 ≫ m) hcartTotal
  have hstepAssocMiddle :
      (FibredCategoryMor.toFunctor K).map v.1 ≫
        ((realComparisonComponent G₁ hG₁ c yPull).hom.1 ≫
          (FibredCategoryMor.toFunctor K').map cart) =
      ((FibredCategoryMor.toFunctor K).map v.1 ≫
          (realComparisonComponent G₁ hG₁ c yPull).hom.1) ≫
        (FibredCategoryMor.toFunctor K').map cart := by
    rw [← Category.assoc]
  have hstepVertical :
      ((FibredCategoryMor.toFunctor K).map v.1 ≫
          (realComparisonComponent G₁ hG₁ c yPull).hom.1) ≫
        (FibredCategoryMor.toFunctor K').map cart =
      ((realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
          (FibredCategoryMor.toFunctor K').map v.1) ≫
        (FibredCategoryMor.toFunctor K').map cart := by
    exact congrArg (fun m ↦ m ≫ (FibredCategoryMor.toFunctor K').map cart) hvert
  have hstepAssocRight :
      ((realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
          (FibredCategoryMor.toFunctor K').map v.1) ≫
        (FibredCategoryMor.toFunctor K').map cart =
      (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
        ((FibredCategoryMor.toFunctor K').map v.1 ≫
          (FibredCategoryMor.toFunctor K').map cart) := by
    rw [Category.assoc]
  have hstepMapK' :
      (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
        ((FibredCategoryMor.toFunctor K').map v.1 ≫
          (FibredCategoryMor.toFunctor K').map cart) =
      (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
        (FibredCategoryMor.toFunctor K').map (v.1 ≫ cart) := by
    exact congrArg
      (fun m ↦ (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫ m) hmapK'.symm
  have hstepEnd :
      (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
        (FibredCategoryMor.toFunctor K').map (v.1 ≫ cart) =
      (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
        (FibredCategoryMor.toFunctor K').map φ := by
    exact congrArg
      (fun m ↦
        (realComparisonComponent G₁ hG₁ c yT).hom.1 ≫
          (FibredCategoryMor.toFunctor K').map m)
      hvcart
  exact
    hstepStart.trans
      (hstepMapK.trans
        (hstepAssocLeft.trans
          (hstepCart.trans
            (hstepAssocMiddle.trans
              (hstepVertical.trans
                (hstepAssocRight.trans (hstepMapK'.trans hstepEnd)))))))

/-- Helper for Lemma 8.8.1 (object descent, inverse naturality of the comparison `2`-iso): the
inverse global comparison `2`-iso components are also natural. This is the hom-naturality
`realComparisonComponent_naturality` read off in reverse, conjugating by the component isos. -/
private theorem realComparisonComponent_inv_naturality
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {T T' : Y₁.S} (φ : T ⟶ T') :
    (FibredCategoryMor.toFunctor K').map φ ≫ (realComparisonComponent G₁ hG₁ c ⟨T', rfl⟩).inv.1 =
      (realComparisonComponent G₁ hG₁ c ⟨T, rfl⟩).inv.1 ≫
        (FibredCategoryMor.toFunctor K).map φ := by
  -- Convert the fiber isomorphisms to total-category isomorphisms, so the inverse square follows
  -- by ordinary cancellation from the hom-naturality square.
  let eT := (Functor.Fiber.fiberInclusion : Y₂.p.Fiber (Y₁.p.obj T) ⥤ Y₂.S).mapIso
    (realComparisonComponent G₁ hG₁ c ⟨T, rfl⟩)
  let eT' := (Functor.Fiber.fiberInclusion : Y₂.p.Fiber (Y₁.p.obj T') ⥤ Y₂.S).mapIso
    (realComparisonComponent G₁ hG₁ c ⟨T', rfl⟩)
  have hhom : (FibredCategoryMor.toFunctor K).map φ ≫ eT'.hom =
      eT.hom ≫ (FibredCategoryMor.toFunctor K').map φ := by
    simpa [eT, eT'] using realComparisonComponent_naturality (J := J) G₁ hG₁ c φ
  change (FibredCategoryMor.toFunctor K').map φ ≫ eT'.inv =
    eT.inv ≫ (FibredCategoryMor.toFunctor K).map φ
  have h1 : (FibredCategoryMor.toFunctor K).map φ =
      (eT.hom ≫ (FibredCategoryMor.toFunctor K').map φ) ≫ eT'.inv :=
    (Iso.eq_comp_inv eT').2 hhom
  have h1' : (FibredCategoryMor.toFunctor K).map φ =
      eT.hom ≫ ((FibredCategoryMor.toFunctor K').map φ ≫ eT'.inv) := by
    simpa [Category.assoc] using h1
  have h2 : eT.inv ≫ (FibredCategoryMor.toFunctor K).map φ =
      (FibredCategoryMor.toFunctor K').map φ ≫ eT'.inv :=
    (Iso.inv_comp_eq eT).2 h1'
  exact h2.symm

/-- Helper for Lemma 8.8.1 (object descent, the based-functor iso of the comparison `2`-iso): the
global comparison `2`-iso components assemble into a based-functor isomorphism
`toBasedFunctor K ≅ toBasedFunctor K'`. The hom/inv based natural transformations have components
the `.1` of the global fiber components; lifting is inherited (vertical), naturality is
`realComparisonComponent_naturality` / `realComparisonComponent_inv_naturality`. -/
noncomputable def realComparisonBasedIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K')) :
    FibredCategoryMor.toBasedFunctor K ≅ FibredCategoryMor.toBasedFunctor K' :=
  -- Totalize the fiber components to a natural isomorphism; their verticality supplies the based
  -- lift condition required by `BasedNatIso.mkNatIso`.
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun T =>
        (Functor.Fiber.fiberInclusion : Y₂.p.Fiber (Y₁.p.obj T) ⥤ Y₂.S).mapIso
          (realComparisonComponent G₁ hG₁ c ⟨T, rfl⟩))
      (fun φ => realComparisonComponent_naturality (J := J) G₁ hG₁ c φ))
    (fun T => (realComparisonComponent G₁ hG₁ c ⟨T, rfl⟩).hom.2)

/-- Helper for Lemma 8.8.1 (object descent, the owner iso of the comparison `2`-iso): the global
comparison `2`-iso components assemble into an owner isomorphism `K ≅ K'`. -/
noncomputable def realComparisonOwnerIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, uY, vY} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K')) :
    K ≅ K' :=
  FibredCategoryMor.ownerIsoOfBasedFunctorIso (realComparisonBasedIso G₁ hG₁ c)

/-- Helper for Lemma 8.8.1 (fullness for isos / `2`-morphism descent): every isomorphism
`c : P.obj H ≅ P.obj H'` in the precomposition category is the image `P.mapIso β` of a stack
`2`-isomorphism `β : H ≅ H'`. -/
private theorem precompose_mapIso_surjective
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (H H' : Y₁ ⟶ Y₂)
    (hHeq : IsEquivalenceOverBase H)
    (hH'eq : IsEquivalenceOverBase H')
    (c : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅
        (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H') :
    ∃ β : H ≅ H',
      (stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β = c := by
  -- Lift the owner-level comparison iso across the full stack hom-category.
  let K : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver :=
    stack_morphism_toFibredCategoryMor H
  let K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver :=
    stack_morphism_toFibredCategoryMor H'
  let cOwner : (G₁ ≫ K) ≅ (G₁ ≫ K') := c
  let βOwner : K ≅ K' :=
    realComparisonOwnerIso (J := J) G₁ hG₁ cOwner
  let β : H ≅ H' :=
    SubTwoCategory.Hom.isoMk (S := stackOverSubTwoCategory J) βOwner trivial trivial
  refine ⟨β, ?_⟩
  -- The remaining equality is checked on total-source components; the constructed component
  -- reduces on `G₁`-images to the original precomposition iso.
  apply fibredCategoryMor_two_iso_ext
  intro T
  -- Evaluate the precomposed iso at `T`, then unfold the owner iso to the glued comparison
  -- component at the image object `G₁(T)`.
  rw [precompose_mapIso_app G₁ β T]
  change (FibredCategoryMor.basedFunctorIsoOfOwnerIso βOwner).hom.toNatTrans.app
      (G₁.toHom.obj T) = c.hom.hom.hom.app T
  have hβOwnerBased :
      FibredCategoryMor.basedFunctorIsoOfOwnerIso βOwner =
        realComparisonBasedIso (J := J) G₁ hG₁ cOwner := by
    rfl
  rw [hβOwnerBased]
  dsimp only [realComparisonBasedIso, BasedNatIso.mkNatIso, NatIso.ofComponents]
  simp only [Functor.mapIso_hom]
  -- The target fiber is indexed by the base of `G₁(T)`. Repackage `T` as an object of that
  -- fiber using the over-base equality of the fibred-category morphism `G₁`.
  let W := Y₁.p.obj (G₁.toHom.obj T)
  have hW : X.p.obj T = W := by
    have h := congrArg (fun q => q.obj T) (FibredCategoryMor.comm G₁)
    exact h.symm
  let x : X.p.Fiber W := ⟨T, hW⟩
  -- With that indexing, the glued component is exactly the image component, so the already-proved
  -- image normal form reduces the equality to the defining component of `c`.
  change Functor.Fiber.fiberInclusion.map
      ((realComparisonComponent G₁ hG₁ c ((FibredCategoryMor.fiberFunctor G₁ W).obj x)).hom) =
    c.hom.hom.hom.app T
  rw [realComparisonComponent_on_image G₁ hG₁ c x]
  rfl

/-- Helper for Lemma 8.8.1: uniqueness belongs to the comparison pair `(H, α)`, not to the raw
type of compatible isomorphisms for a fixed `H`. Given one comparison pair, every other pair is
connected to it by a unique `2`-isomorphism whose image under precomposition carries the second
comparison isomorphism to the first. -/
theorem comparison_stackification_compatible_twoIso_unique_direct_assembly
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) :
    ∀ (H' : Y₁ ⟶ Y₂)
      (α' : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H' ≅ G₂),
      ∃! β : H ≅ H',
        ((stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β) ≪≫ α' =
          α := by
  intro H' α'
  -- Both `H` and `H'` are equivalences over the base.
  have hHeq : IsEquivalenceOverBase H :=
    comparison_stackification_isEquivalenceOverBase (J := J) G₁ G₂ hG₁ hG₂ H α
  have hH'eq : IsEquivalenceOverBase H' :=
    comparison_stackification_isEquivalenceOverBase (J := J) G₁ G₂ hG₁ hG₂ H' α'
  -- The forced comparison iso in the precomposition category.
  let c : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅
      (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H' :=
    α ≪≫ α'.symm
  -- Fullness for isos gives a `β` with `P.mapIso β = c`.
  obtain ⟨β, hβ⟩ := precompose_mapIso_surjective (J := J) G₁ hG₁ H H' hHeq hH'eq c
  refine ⟨β, ?_, ?_⟩
  · -- Existence/compatibility: `P.mapIso β ≪≫ α' = c ≪≫ α' = α`.
    show (stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β ≪≫ α' = α
    rw [hβ]
    show (α ≪≫ α'.symm) ≪≫ α' = α
    rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  · -- Uniqueness via faithfulness.
    intro β' hβ'
    apply precompose_mapIso_injective (J := J) G₁ hG₁ β' β
    -- `P.mapIso β' = α ≪≫ α'.symm = P.mapIso β`.
    have hβ'eq : (stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β' =
        α ≪≫ α'.symm := by
      rw [← hβ', Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    rw [hβ'eq, hβ]

end

end CategoryTheory
