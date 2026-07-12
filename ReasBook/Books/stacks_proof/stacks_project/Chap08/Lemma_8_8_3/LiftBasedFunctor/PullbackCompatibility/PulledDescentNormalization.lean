import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.LocalModelComparison

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

theorem stackificationLiftObjectDescentData_hom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (y : S'.p.Fiber U)
    (q : V ⟶ U)
    {I₁ I₂ : (stackificationLiftObjectCover (J := J) G hG y).Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    (stackificationLiftObjectDescentData X G hG F y).hom q f₁ f₂ hf₁ hf₂ =
      stackificationLiftObjectTransition X G hG F y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        q f₁ f₂ hf₁ hf₂ := by
  rfl

theorem stackificationLiftPulledObjectModelPullbackIso_comp_eq
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U V W : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    {I₁ I₂ : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow}
    (f₁ : W ⟶ I₁.Y) (f₂ : W ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = f₁ ≫ I₁.f) :
    (stackificationLiftObjectModelPullbackIso (J := J) G y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        (f₁ ≫ I₁.f ≫ f) I₁.base f₁ (by
          simp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base])).hom ≫
      (stackificationLiftObjectModelPullbackIso (J := J) G y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        (f₁ ≫ I₁.f ≫ f) I₂.base f₂ (by
          simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
            Category.assoc] using congrArg (fun t => t ≫ f) hf₂)).inv =
    (stackificationLiftObjectModelPullbackIso (J := J) G
        (f ^*[canonicalPullbackChoice S'.p] y)
        (stackificationLiftPulledObjectCover (J := J) G hG f y)
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y)
        (f₁ ≫ I₁.f) I₁ f₁ rfl).hom ≫
      (stackificationLiftObjectModelPullbackIso (J := J) G
        (f ^*[canonicalPullbackChoice S'.p] y)
        (stackificationLiftPulledObjectCover (J := J) G hG f y)
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y)
        (f₁ ≫ I₁.f) I₂ f₂ hf₂).inv := by
  dsimp only [stackificationLiftObjectModelPullbackIso,
    stackificationLiftPulledObjectCoverModel]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, mapCompAppIso, Category.assoc]
  conv_rhs =>
    erw [((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor.map_comp]
    erw [((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor.map_comp]
  let Fp := canonicalFiberPseudofunctor S'.p
  let q : W ⟶ V := f₁ ≫ I₁.f
  let q' : W ⟶ U := f₁ ≫ I₁.f ≫ f
  let κ₁f := Fp.mapComp' f.op.toLoc I₁.f.op.toLoc (I₁.f ≫ f).op.toLoc
    (FibredCategoryMor.comp_toLoc_eq f I₁.f (I₁.f ≫ f) rfl)
  let κ₁ := Fp.mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc (by
    simpa [q] using
      (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q rfl))
  let κt := Fp.mapComp' f.op.toLoc q.op.toLoc q'.op.toLoc (by
    simpa [q, q', Category.assoc] using
      (FibredCategoryMor.comp_toLoc_eq f q q' rfl))
  let κbase₁ := Fp.mapComp' I₁.base.f.op.toLoc f₁.op.toLoc q'.op.toLoc (by
    simpa [q', stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
      Category.assoc] using
      (FibredCategoryMor.comp_toLoc_eq I₁.base.f f₁ q'
        (by simp [q', stackificationLiftPulledObjectCover,
          GrothendieckTopology.Cover.Arrow.base, Category.assoc])))
  let κ₂f := Fp.mapComp' f.op.toLoc I₂.f.op.toLoc (I₂.f ≫ f).op.toLoc
    (FibredCategoryMor.comp_toLoc_eq f I₂.f (I₂.f ≫ f) rfl)
  let κ₂ := Fp.mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc (by
    simpa [q] using
      (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂))
  let κbase₂ := Fp.mapComp' I₂.base.f.op.toLoc f₂.op.toLoc q'.op.toLoc (by
    simpa [q', stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
      Category.assoc] using
      (FibredCategoryMor.comp_toLoc_eq I₂.base.f f₂ q'
        (by
          simpa [q', stackificationLiftPulledObjectCover,
            GrothendieckTopology.Cover.Arrow.base, Category.assoc] using
            congrArg (fun t => t ≫ f) hf₂)))
  have hbase₁ :
      κbase₁.inv.toNatTrans.app y =
        (Fp.map f₁.op.toLoc).toFunctor.map (κ₁f.hom.toNatTrans.app y) ≫
          κ₁.inv.toNatTrans.app (f ^*[canonicalPullbackChoice S'.p] y) ≫
            κt.inv.toNatTrans.app y := by
    dsimp only [Fp, q, q']
    simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
      Category.assoc, κ₁f, κ₁, κt, κbase₁] using
      (Pseudofunctor.mapComp'₀₂₃_inv_app
        (F := canonicalFiberPseudofunctor S'.p)
        (f₀₁ := f.op.toLoc) (f₁₂ := I₁.f.op.toLoc) (f₂₃ := f₁.op.toLoc)
        (f₀₂ := (I₁.f ≫ f).op.toLoc) (f₁₃ := (f₁ ≫ I₁.f).op.toLoc)
        (f := (f₁ ≫ I₁.f ≫ f).op.toLoc)
        (h₀₂ := FibredCategoryMor.comp_toLoc_eq f I₁.f (I₁.f ≫ f) rfl)
        (h₁₃ := by
          simpa using
            (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ (f₁ ≫ I₁.f) rfl))
        (hf := by
          simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
            Category.assoc] using
            (FibredCategoryMor.comp_toLoc_eq I₁.base.f f₁ (f₁ ≫ I₁.f ≫ f)
              (by simp [stackificationLiftPulledObjectCover,
                GrothendieckTopology.Cover.Arrow.base, Category.assoc])))
        y)
  have hbase₂ :
      κbase₂.hom.toNatTrans.app y =
        κt.hom.toNatTrans.app y ≫
          κ₂.hom.toNatTrans.app (f ^*[canonicalPullbackChoice S'.p] y) ≫
            (Fp.map f₂.op.toLoc).toFunctor.map (κ₂f.inv.toNatTrans.app y) := by
    dsimp only [Fp, q, q']
    simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
      Category.assoc, κ₂f, κ₂, κt, κbase₂] using
      (Pseudofunctor.mapComp'₀₂₃_hom_app
        (F := canonicalFiberPseudofunctor S'.p)
        (f₀₁ := f.op.toLoc) (f₁₂ := I₂.f.op.toLoc) (f₂₃ := f₂.op.toLoc)
        (f₀₂ := (I₂.f ≫ f).op.toLoc) (f₁₃ := (f₁ ≫ I₁.f).op.toLoc)
        (f := (f₁ ≫ I₁.f ≫ f).op.toLoc)
        (h₀₂ := FibredCategoryMor.comp_toLoc_eq f I₂.f (I₂.f ≫ f) rfl)
        (h₁₃ := by
          simpa using
            (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ (f₁ ≫ I₁.f) hf₂))
        (hf := by
          simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
            Category.assoc] using
            (FibredCategoryMor.comp_toLoc_eq I₂.base.f f₂ (f₁ ≫ I₁.f ≫ f)
              (by
                simpa [stackificationLiftPulledObjectCover,
                  GrothendieckTopology.Cover.Arrow.base, Category.assoc] using
                  congrArg (fun t => t ≫ f) hf₂)))
        y)
  erw [hbase₁, hbase₂]
  dsimp only [κ₁f, κ₁, κ₂, κ₂f, Fp, q]
  let c := ((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor.map
    (((canonicalFiberPseudofunctor S'.p).mapComp' f.op.toLoc I₁.f.op.toLoc
      (I₁.f ≫ f).op.toLoc
      (FibredCategoryMor.comp_toLoc_eq f I₁.f (I₁.f ≫ f) rfl)).hom.toNatTrans.app y)
  let d := ((canonicalFiberPseudofunctor S'.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc
    (f₁ ≫ I₁.f).op.toLoc
    (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ (f₁ ≫ I₁.f) rfl)).inv.toNatTrans.app
      (f ^*[canonicalPullbackChoice S'.p] y)
  let e := κt.inv.toNatTrans.app y
  let e' := κt.hom.toNatTrans.app y
  let g := ((canonicalFiberPseudofunctor S'.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc
    (f₁ ≫ I₁.f).op.toLoc
    (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ (f₁ ≫ I₁.f) hf₂)).hom.toNatTrans.app
      (f ^*[canonicalPullbackChoice S'.p] y)
  let h := ((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor.map
    (((canonicalFiberPseudofunctor S'.p).mapComp' f.op.toLoc I₂.f.op.toLoc
      (I₂.f ≫ f).op.toLoc
      (FibredCategoryMor.comp_toLoc_eq f I₂.f (I₂.f ≫ f) rfl)).inv.toNatTrans.app y)
  have hmid : ((c ≫ d ≫ e) ≫ e' ≫ g ≫ h) = c ≫ d ≫ g ≫ h := by
    dsimp only [e, e']
    have hκ : κt.inv.toNatTrans.app y ≫ κt.hom.toNatTrans.app y =
        𝟙 (((canonicalFiberPseudofunctor S'.p).map (f₁ ≫ I₁.f).op.toLoc).toFunctor.obj
          (f ^*[canonicalPullbackChoice S'.p] y)) := by
      exact Cat.Hom.inv_hom_id_toNatTrans_app κt y
    calc
      ((c ≫ d ≫ κt.inv.toNatTrans.app y) ≫ κt.hom.toNatTrans.app y ≫ g ≫ h) =
          (c ≫ d) ≫ (κt.inv.toNatTrans.app y ≫ κt.hom.toNatTrans.app y) ≫ g ≫ h := by
            simp only [Category.assoc]
      _ = (c ≫ d) ≫ 𝟙 _ ≫ g ≫ h := by
            exact congrArg (fun t => (c ≫ d) ≫ t ≫ g ≫ h) hκ
      _ = c ≫ d ≫ g ≫ h := by
            simp only [Category.assoc, Category.id_comp]
  slice_lhs 3 4 => exact hmid
  dsimp only [c, d, g, h]
  let b := ((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor.map
    (stackificationLiftObjectModel (J := J) G hG y I₁.base).2.hom
  let i := ((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor.map
    (stackificationLiftObjectModel (J := J) G hG y I₂.base).2.inv
  let j := (FibredCategoryMor.pullbackComparison G f₂
    (stackificationLiftObjectModel (J := J) G hG y I₂.base).1).hom
  have htail : (c ≫ d ≫ g ≫ h) ≫ i = c ≫ d ≫ g ≫ (h ≫ i) := by
    simp only [Category.assoc]
  slice_lhs 3 6 => exact htail
  have hfront : b ≫ (c ≫ d ≫ g ≫ h ≫ i) ≫ j =
      ((b ≫ c) ≫ d ≫ g ≫ h ≫ i) ≫ j := by
    simp only [Category.assoc]
  slice_lhs 2 7 => exact hfront
  dsimp only [b, i, j, c, d, g, h]
  let a := (FibredCategoryMor.pullbackComparison G f₁
    (stackificationLiftObjectModel (J := J) G hG y I₁.base).1).inv
  let bc := b ≫ c
  let hi := h ≫ i
  change a ≫ (bc ≫ d ≫ g ≫ h ≫ i) ≫ j =
    a ≫ bc ≫ d ≫ g ≫ hi ≫ j
  dsimp only [bc, hi]
  have htail2 :
      ((b ≫ c) ≫ d ≫ g ≫ h) ≫ i =
        (b ≫ c) ≫ d ≫ g ≫ (h ≫ i) := by
    simp only [Category.assoc]
  slice_rhs 2 5 => exact htail2.symm
  rw [htail2]
  rfl

theorem stackificationLiftPulledDescentData_hom_eq_transition
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V W : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (q : W ⟶ V)
    {I₁ I₂ : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow}
    (f₁ : W ⟶ I₁.Y) (f₂ : W ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    let Fp := canonicalFiberPseudofunctor X.p
    let mid₁ := (FibredCategoryMor.fiberFunctor F I₁.Y).obj
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I₁).1
    let mid₂ := (FibredCategoryMor.fiberFunctor F I₂.Y).obj
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I₂).1
    ((Fp.map f₁.op.toLoc).toFunctor.map
        ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I₁.Y)))).app mid₁).symm.hom) ≫
      (stackificationLiftPulledObjectDescentData X G hG F f y).hom q f₁ f₂ hf₁ hf₂ =
    stackificationLiftObjectTransition X G hG F
        (f ^*[canonicalPullbackChoice S'.p] y)
        (stackificationLiftPulledObjectCover (J := J) G hG f y)
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y)
        q f₁ f₂ hf₁ hf₂ ≫
      ((Fp.map f₂.op.toLoc).toFunctor.map
        ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I₂.Y)))).app mid₂).symm.hom) := by
  classical
  subst q
  dsimp only
    [stackificationLiftPulledObjectDescentData,
      stackificationLiftPulledObjectDescentPullFunctor,
      Pseudofunctor.DescentData.pullFunctor,
      Pseudofunctor.DescentData.pullFunctorObj]
  rw [Pseudofunctor.DescentData.pullFunctorObjHom_eq
    (F := canonicalFiberPseudofunctor X.p)
    (f := fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow => I.f)
    (f' := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow => I.f)
    (p := f)
    (α := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow => I.base)
    (p' := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow => 𝟙 I.Y)
    (w := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow => by
      simp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base])
    (D := stackificationLiftObjectDescentData X G hG F y)
    (f₁ ≫ I₁.f) f₁ f₂ ((f₁ ≫ I₁.f) ≫ f) f₁ f₂
    (hf₁' := by simp)
    (hf₂' := by simp)]
  dsimp only [stackificationLiftPulledObjectCoverModel, stackificationLiftObjectTransition]
  simp only [Category.assoc]
  let Fp := canonicalFiberPseudofunctor X.p
  let D := stackificationLiftObjectDescentData X G hG F y
  let M₁ := D.obj I₁.base
  let M₂ := D.obj I₂.base
  have hleftcancel :
      ((Fp.map f₁.op.toLoc).toFunctor.map
          ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I₁.Y)))).app M₁).symm.hom) ≫
        (Fp.mapComp' (𝟙 I₁.Y).op.toLoc f₁.op.toLoc f₁.op.toLoc (by simp)).inv.toNatTrans.app M₁ =
      𝟙 _ := by
    have hB :
        (Fp.mapComp' (𝟙 I₁.Y).op.toLoc f₁.op.toLoc f₁.op.toLoc (by simp)).inv.toNatTrans.app M₁ =
          (Fp.map f₁.op.toLoc).toFunctor.map
            ((Fp.mapId (LocallyDiscrete.mk (op I₁.Y))).hom.toNatTrans.app M₁) ≫
          eqToHom (by simp) := by
      dsimp only [Fp, M₁, D]
      simpa only [op_id, Quiver.Hom.id_toLoc] using
        (Pseudofunctor.mapComp'_id_comp_inv_app
          (F := canonicalFiberPseudofunctor X.p)
          (f := f₁.op.toLoc)
          ((stackificationLiftObjectDescentData X G hG F y).obj I₁.base))
    rw [hB]
    change
      (Fp.map f₁.op.toLoc).toFunctor.map
          ((Fp.mapId (LocallyDiscrete.mk (op I₁.Y))).inv.toNatTrans.app M₁) ≫
        (Fp.map f₁.op.toLoc).toFunctor.map
          ((Fp.mapId (LocallyDiscrete.mk (op I₁.Y))).hom.toNatTrans.app M₁) ≫
        eqToHom (by simp) =
      𝟙 _
    rw [← (Fp.map f₁.op.toLoc).toFunctor.map_comp_assoc]
    rw [Cat.Hom.inv_hom_id_toNatTrans_app]
    simp only [Functor.map_id, Category.id_comp, eqToHom_refl]
  erw [reassoc_of% hleftcancel]
  dsimp only [Cat.Hom.id_toFunctor, Functor.id_obj]
  rw [Category.id_comp]
  have hright :
      (Fp.mapComp' (𝟙 I₂.Y).op.toLoc f₂.op.toLoc f₂.op.toLoc (by simp)).hom.toNatTrans.app M₂ =
        eqToHom (by simp) ≫
          (Fp.map f₂.op.toLoc).toFunctor.map
            ((Fp.mapId (LocallyDiscrete.mk (op I₂.Y))).inv.toNatTrans.app M₂) := by
    dsimp only [Fp, M₂, D]
    simpa only [op_id, Quiver.Hom.id_toLoc] using
      (Pseudofunctor.mapComp'_id_comp_hom_app
        (F := canonicalFiberPseudofunctor X.p)
        (f := f₂.op.toLoc)
        ((stackificationLiftObjectDescentData X G hG F y).obj I₂.base))
  erw [hright]
  dsimp only [Cat.Hom.id_toFunctor, Functor.id_obj]
  simp only [eqToHom_refl]
  rw [stackificationLiftObjectDescentData_hom]
  dsimp only [stackificationLiftObjectTransition]
  rw [stackificationLiftPulledObjectModelPullbackIso_comp_eq (G := G) (hG := hG) f y f₁ f₂ hf₂]
  let δ :=
    (stackificationLiftObjectModelPullbackIso (J := J) G
        (f ^*[canonicalPullbackChoice S'.p] y)
        (stackificationLiftPulledObjectCover (J := J) G hG f y)
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y)
        (f₁ ≫ I₁.f) I₁ f₁ rfl).hom ≫
      (stackificationLiftObjectModelPullbackIso (J := J) G
        (f ^*[canonicalPullbackChoice S'.p] y)
        (stackificationLiftPulledObjectCover (J := J) G hG f y)
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y)
        (f₁ ≫ I₁.f) I₂ f₂ hf₂).inv
  let A := (FibredCategoryMor.pullbackComparison F f₁
    (stackificationLiftObjectModel (J := J) G hG y I₁.base).1).hom
  let B := stackificationLiftHomExtensionFiberMap X G hG F
    (f₁ ^*[canonicalPullbackChoice S.p]
      (stackificationLiftObjectModel (J := J) G hG y I₁.base).1)
    (f₂ ^*[canonicalPullbackChoice S.p]
      (stackificationLiftObjectModel (J := J) G hG y I₂.base).1)
    δ
  let Cmap := (FibredCategoryMor.pullbackComparison F f₂
    (stackificationLiftObjectModel (J := J) G hG y I₂.base).1).inv
  let T := (Fp.map f₂.op.toLoc).toFunctor.map
    ((Fp.mapId (LocallyDiscrete.mk (op I₂.Y))).inv.toNatTrans.app M₂)
  change ((A ≫ B ≫ Cmap) ≫ 𝟙 _ ≫ T) = A ≫ B ≫ Cmap ≫ T
  rw [Category.id_comp]
  simp only [Category.assoc]

end

end CategoryTheory
