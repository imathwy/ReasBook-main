import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.ComparisonEquivalence
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.ForcedComparisonComponents
import Mathlib.Tactic.StacksAttribute

universe u v

namespace CategoryTheory

open Bicategory BasedFunctor FibredCategoryMor InducedCategory.Hom Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

noncomputable def realForcedHomIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J} (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    ((FibredCategoryMor.fiberFunctor K W).obj y) ≅ ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
  (FibredCategoryMor.fiberFunctor K W).mapIso cx.symm ≪≫ (cFiberComp G₁ c x) ≪≫
    (FibredCategoryMor.fiberFunctor K' W).mapIso cx

-- The pbc base cocycle: for `K : Y₁ ⟶ Y₂`, `fi ≫ i_f = q`, the composite of the `Y₂` mapComp'
-- iso, the `M_fi`-image of `pbc K i_f y`, and `pbc K fi (i_f^*y)` equals `(pbc K q y).hom`
-- post-conjugated by `K_Z` applied to the `Y₁`-mapComp' comparison `q^*y ⟶ fi^*(i_f^*y)`.
set_option backward.isDefEq.respectTransparency false in
private theorem pbc_base_cocycle
    {X Y : FibredCategoryOver C} (K : X ⟶ Y)
    {W Z : C} {Wmid : C} (i_f : Wmid ⟶ W) (fi : Z ⟶ Wmid) (q : Z ⟶ W)
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
  apply Functor.Fiber.hom_ext
  set Kf := FibredCategoryMor.fiberFunctor K W with hKf
  -- The common strongly cartesian witness from `K_Z(fi^*(i_f^*y))` down to `Kf y` over `q`.
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
      rw [hθ]; infer_instance
    rwa [hq] at hcomp
  letI : Y.p.IsStronglyCartesian q θ := hθcart
  -- Abbreviations
  set Ahom := ((canonicalFiberPseudofunctor Y.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
      (by rw [← FibredCategoryMor.comp_toLoc_eq i_f fi q hq])).hom.toNatTrans.app (Kf.obj y)
    with hAhom
  set cI_X := (((canonicalFiberPseudofunctor X.p).mapComp' i_f.op.toLoc fi.op.toLoc q.op.toLoc
      (by rw [← FibredCategoryMor.comp_toLoc_eq i_f fi q hq])).hom.toNatTrans.app y)
    with hcI_X
  -- Both candidates lift `𝟙 Z`.
  have hLlift : Y.p.IsHomLift (𝟙 Z)
      (Ahom.1 ≫
        (((canonicalFiberPseudofunctor Y.p).map fi.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison K i_f y).hom).1 ≫
          (FibredCategoryMor.pullbackComparison K fi
            (i_f ^*[canonicalPullbackChoice X.p] y)).hom.1) :=
    (Ahom ≫
        ((canonicalFiberPseudofunctor Y.p).map fi.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison K i_f y).hom ≫
          (FibredCategoryMor.pullbackComparison K fi
            (i_f ^*[canonicalPullbackChoice X.p] y)).hom).2
  have hRlift : Y.p.IsHomLift (𝟙 Z)
      ((FibredCategoryMor.pullbackComparison K q y).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor K Z).map cI_X).1) :=
    ((FibredCategoryMor.pullbackComparison K q y).hom ≫
      (FibredCategoryMor.fiberFunctor K Z).map cI_X).2
  -- Reduce to checking after postcomposition with the cartesian `θ`.
  refine Functor.IsStronglyCartesian.ext Y.p q θ (𝟙 Z) ?_
  -- Both candidates, postcomposed with `θ`, equal the chosen pullback arrow `(cpc Y).map q (Kf y)`.
  show (Ahom.1 ≫
        (((canonicalFiberPseudofunctor Y.p).map fi.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison K i_f y).hom).1 ≫
          (FibredCategoryMor.pullbackComparison K fi
            (i_f ^*[canonicalPullbackChoice X.p] y)).hom.1) ≫ θ =
      ((FibredCategoryMor.pullbackComparison K q y).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor K Z).map cI_X).1) ≫ θ
  -- The X-side factorization for the `mapComp'` hom component.
  have hXfac : cI_X.1 ≫
        (canonicalPullbackChoice X.p).map fi (i_f ^*[canonicalPullbackChoice X.p] y) ≫
        (canonicalPullbackChoice X.p).map i_f y =
      (canonicalPullbackChoice X.p).map q y := by
    have := FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      X.p i_f fi q hq y
    simpa only [hcI_X] using this
  -- The Y-side factorization for the `mapComp'` hom component (at `Kf y`).
  have hYfac : Ahom.1 ≫
        (canonicalPullbackChoice Y.p).map fi
          (((canonicalFiberPseudofunctor Y.p).map i_f.op.toLoc).toFunctor.obj (Kf.obj y)) ≫
        (canonicalPullbackChoice Y.p).map i_f (Kf.obj y) =
      (canonicalPullbackChoice Y.p).map q (Kf.obj y) := by
    have := FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      Y.p i_f fi q hq (Kf.obj y)
    simpa only [hAhom] using this
  -- `θ` unfolded to its two `K`-image factors.
  have hθ1 : θ =
      K.toHom.map ((canonicalPullbackChoice X.p).map fi (i_f ^*[canonicalPullbackChoice X.p] y)) ≫
        K.toHom.map ((canonicalPullbackChoice X.p).map i_f y) := hθ
  -- The fiber-functor map of `cI_X` is given by its underlying `.1`.
  have hKZ : ((FibredCategoryMor.fiberFunctor K Z).map cI_X).1 = K.toHom.map cI_X.1 := rfl
  -- The `M_fi`-image of `pbc K i_f y` (auto-inferred dom/cod from `φ`).
  have hMfi := FibredCategoryMor.canonical_pullbackFunctor_map_fac Y.p fi
      (FibredCategoryMor.pullbackComparison K i_f y).hom
  -- RHS reduction.
  have hRHS : ((FibredCategoryMor.pullbackComparison K q y).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor K Z).map cI_X).1) ≫ θ =
      (canonicalPullbackChoice Y.p).map q (Kf.obj y) := by
    rw [hKZ, hθ1]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [hXfac]
    exact FibredCategoryMor.pullbackComparison_hom_postcompose K q y
  -- LHS reduction.
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
    -- Reassociate fully to the right (no `simp`, to keep `^*[…]`/`(cpc).map` notation intact).
    rw [Category.assoc, Category.assoc]
    -- Step 1: collapse `(pbc K fi (i_f^*y)).hom.1 ≫ K.map((cpc X).map fi (i_f^*y))`.
    rw [reassoc_of% hpost_fi]
    -- Step 2: push `M_fi(pbc K i_f y).1` past `(cpc Y).map fi (...)` via `hMfi`.
    rw [reassoc_of% hMfi]
    -- Step 3: collapse `(pbc K i_f y).hom.1 ≫ K.map((cpc X).map i_f y)`.
    rw [hpost_if]
    -- Step 4: the Y-side factorization.
    exact hYfac
  rw [hLHS, hRHS]

/-- The mapComp' app component as an iso, with objects ascribed in `^*[…]` (chosen-pullback) form
so it matches the forced-morphism base objects produced by `Mf_realForcedHom_pullback`. -/
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

-- The pbc base cocycle as an iso identity (gives both hom and inv forms).
set_option backward.isDefEq.respectTransparency false in
private theorem pbc_base_cocycle_iso
    {X Y : FibredCategoryOver C} (K : X ⟶ Y)
    {W Z : C} {Wmid : C} (i_f : Wmid ⟶ W) (fi : Z ⟶ Wmid) (q : Z ⟶ W)
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
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, mapCompAppIso]
  exact pbc_base_cocycle K i_f fi q hq y

/-- `realForcedHom` base-transport: conjugating the forced fiber morphism over `y'` by the
fiber-functor images of a base iso `cI : y ≅ y'` recovers the forced morphism over `y` for the
same source object `x'` with the composed model `cx' ≪≫ cI.symm`. Pure unfolding. -/
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
  dsimp only [realForcedHom]
  have hinv : (cx' ≪≫ cI.symm).inv = cI.hom ≫ cx'.inv := rfl
  have hhom : (cx' ≪≫ cI.symm).hom = cx'.hom ≫ cI.inv := rfl
  rw [hinv, hhom, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem realComparisonComponent_comm.{w}
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, w, max u v} J}
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
  -- The single-arrow "transported component" `T i fi` is independent of `(i, fi)`; it equals the
  -- `pbc`-conjugate of a forced morphism over `q^*y`.
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
                (((canonicalFiberPseudofunctor Y₁.p).map fi.op.toLoc).toFunctor.mapIso (model i).2)) ≪≫
              (mapCompAppIso Y₁.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi) y).symm) ≫
          (FibredCategoryMor.pullbackComparison K' q y).inv := by
    intro i fi hfi
    -- Expand `(e i).hom` to the pbc-conjugate form and distribute `M_fi`.
    have hei : (e i).hom =
        (FibredCategoryMor.pullbackComparison K i.f y).hom ≫
          realForcedHom G₁ c (i.f ^*[canonicalPullbackChoice Y₁.p] y) (model i).1 (model i).2 ≫
          (FibredCategoryMor.pullbackComparison K' i.f y).inv := by
      rw [he i]; rfl
    rw [hei, Functor.map_comp, Functor.map_comp]
    -- The pullback bridge for the middle `realForcedHom`.
    rw [Mf_realForcedHom_pullback G₁ c fi (i.f ^*[canonicalPullbackChoice Y₁.p] y) (model i).1 (model i).2]
    -- The pbc base cocycle (K side, `.hom`) and (K' side, `.inv`).
    have hBK := congrArg (fun (t : _ ≅ _) => t.hom) (pbc_base_cocycle_iso K i.f fi q hfi y)
    have hBK' := congrArg (fun (t : _ ≅ _) => t.inv) (pbc_base_cocycle_iso K' i.f fi q hfi y)
    simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc] at hBK hBK'
    -- The goal's raw `mapComp'.app` legs are definitionally the `mapCompAppIso` hom/inv.
    have hAhomK : ((canonicalFiberPseudofunctor Y₂.p).mapComp' i.f.op.toLoc fi.op.toLoc q.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor K W).obj y) =
      (mapCompAppIso Y₂.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)
        ((FibredCategoryMor.fiberFunctor K W).obj y)).hom := rfl
    have hAinvK' : ((canonicalFiberPseudofunctor Y₂.p).mapComp' i.f.op.toLoc fi.op.toLoc q.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor K' W).obj y) =
      (mapCompAppIso Y₂.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi)
        ((FibredCategoryMor.fiberFunctor K' W).obj y)).inv := rfl
    rw [hAhomK, hAinvK']
    -- Reassociate the LHS so the K- and K'-blocks become contiguous.
    simp only [Category.assoc]
    -- Rewrite the K-block `Ahom ≫ M_fi(pbcK).hom ≫ (pbcK fi).hom` to `(pbcK q).hom ≫ K_Z(cI_X.hom)`.
    rw [reassoc_of% hBK]
    -- Rewrite the K'-block `(pbcK' fi).inv ≫ M_fi(pbcK').inv ≫ Ainv` to `K'_Z(cI_X.inv) ≫ (pbcK' q).inv`.
    rw [hBK']
    -- Middle: the conjugated forced morphism is the forced morphism over `q^*y` (base-transport).
    have mid_eq := realForcedHom_base_transport (W := Z) G₁ c
      (mapCompAppIso Y₁.p i.f fi q (FibredCategoryMor.comp_toLoc_eq i.f fi q hfi) y)
      (fi ^*[canonicalPullbackChoice X.p] (model i).1)
      ((FibredCategoryMor.pullbackComparison G₁ fi (model i).1).symm ≪≫
        (((canonicalFiberPseudofunctor Y₁.p).map fi.op.toLoc).toFunctor.mapIso (model i).2))
    rw [reassoc_of% mid_eq]
  -- `T i₁ f₁ = T i₂ f₂` by `key` + model independence over `q^*y`.
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
    -- The two forced morphisms over `q^*y` are equal by model independence.
    rw [realForcedHom_model_indep G₁ hG₁ c (q ^*[canonicalPullbackChoice Y₁.p] y)
      (f₁ ^*[canonicalPullbackChoice X.p] (model i₁).1) _
      (f₂ ^*[canonicalPullbackChoice X.p] (model i₂).1) _]
  -- Unfold the descent-data `.hom` to the two `mapComp'` legs.
  dsimp only [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  -- Cancellation facts: `Ahom ≫ Ainv = id`, `Ainv ≫ Ahom = id` (app level).
  have hcancel_K₁ :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K W).obj y) = 𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  have hcancel_K'₂ :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' W).obj y) ≫
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor K' W).obj y) = 𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app _ _
  -- A1: `M_{f₁}(e i₁) ≫ Ainv_{K'} = Ainv_K ≫ T i₁ f₁`.
  have hA1 :
      ((canonicalFiberPseudofunctor Y₂.p).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' W).obj y) =
        ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
          (((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
            ((canonicalFiberPseudofunctor Y₂.p).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
            ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₁.f.op.toLoc f₁.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₁.f f₁ q hf₁])).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K' W).obj y)) := by
    rw [← Category.assoc, hcancel_K₁, Category.id_comp]
  -- A2: `Ahom_K ≫ M_{f₂}(e i₂) = T i₂ f₂ ≫ Ahom_{K'}`.
  have hA2 :
      ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
          ((canonicalFiberPseudofunctor Y₂.p).map f₂.op.toLoc).toFunctor.map (e i₂).hom =
        (((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K W).obj y) ≫
            ((canonicalFiberPseudofunctor Y₂.p).map f₂.op.toLoc).toFunctor.map (e i₂).hom ≫
            ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor K' W).obj y)) ≫
          ((canonicalFiberPseudofunctor Y₂.p).mapComp' i₂.f.op.toLoc f₂.op.toLoc q.op.toLoc (by rw [← FibredCategoryMor.comp_toLoc_eq i₂.f f₂ q hf₂])).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor K' W).obj y) := by
    rw [Category.assoc, Category.assoc, hcancel_K'₂]
    simp
  -- Assemble: LHS = Ainv_K ≫ (T i₁ f₁) ≫ Ahom_{K'}; RHS = Ainv_K ≫ (T i₂ f₂) ≫ Ahom_{K'}.
  rw [reassoc_of% hA1]
  conv_rhs => rw [Category.assoc, hA2]
  rw [reassoc_of% hTeq]
  simp only [Category.assoc]

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
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence (J := J) (p := Y₂.p)).1 inferInstance W S
  (Functor.FullyFaithful.ofFullyFaithful Φ).preimageIso ddIso

-- KEY: pullback of rcc along a cover arrow equals (e I).hom (existential model form)
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
  -- M_{I.f}.map (preimage g) = (Φ.map (preimage g)).hom I = (ddIso.hom).hom I = (e I).hom
  change (Φ.map ((Functor.FullyFaithful.ofFullyFaithful Φ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem realComparisonComponent_eq_forced.{w}
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, w, max u v} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    (realComparisonComponent G₁ hG₁ c y).hom = realForcedHom G₁ c y x cx := by
  apply stack_cover_hom_ext (J := J) Y₂ (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose
  intro I
  obtain ⟨xI, cxI, hI⟩ := realComparisonComponent_pullback_eq G₁ hG₁ c y I
  rw [hI, Mf_realForcedHom_pullback G₁ c I.f y x cx]
  -- Both middles are realForcedHom over (I.f^*y) for two models; equal by model_indep.
  rw [realForcedHom_model_indep G₁ hG₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y)
    xI cxI
    (I.f ^*[canonicalPullbackChoice X.p] x)
    ((FibredCategoryMor.pullbackComparison G₁ I.f x).symm ≪≫
      (((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.mapIso cx))]

end

end CategoryTheory
