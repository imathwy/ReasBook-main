import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.BaseChangeData
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.MapIdCancellation
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.Global

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The pulled-back descent data of an already-glued object is compatible with a vertical
map on the original object, after evaluating on a branch of the pulled vertical common cover. -/
theorem stackificationLiftPulledGluedObjectDescentIso_verticalMap
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U)
    {y₀ y₁ : S'.p.Fiber U} (d : y₀ ⟶ y₁)
    (I : ((stackificationLiftVerticalCommonCover (J := J) G hG y₀ y₁).pullback f).Arrow) :
    let I₀ : (stackificationLiftPulledObjectCover (J := J) G hG f y₀).Arrow :=
      ⟨I.Y, I.f, by
        dsimp [stackificationLiftPulledObjectCover,
          stackificationLiftVerticalCommonCover] at I
        exact I.base.hf.1⟩
    let I₁ : (stackificationLiftPulledObjectCover (J := J) G hG f y₁).Arrow :=
      ⟨I.Y, I.f, by
        dsimp [stackificationLiftPulledObjectCover,
          stackificationLiftVerticalCommonCover] at I
        exact I.base.hf.2⟩
    let Fp := canonicalFiberPseudofunctor X.p
    let M := ((Fp).map I.f.op.toLoc).toFunctor
    let Hbase := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₀ I₀).1
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₁ I₁).1
      ((stackificationLiftObjectModel (J := J) G hG y₀ I₀.base).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I₀.base.f.op.toLoc).toFunctor.map d ≫
        (stackificationLiftObjectModel (J := J) G hG y₁ I₁.base).2.inv)
    (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₀).inv.hom I₀ ≫
        M.map (((Fp).map f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d)) ≫
        (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₁).hom.hom I₁ =
      (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map Hbase := by
  intro I₀ I₁ Fp M Hbase
  dsimp only [Hbase]
  simp only [stackificationLiftPulledGluedObjectDescentIso,
    stackificationLiftPulledObjectDescentData,
    stackificationLiftPulledObjectDescentPullFunctor,
    Pseudofunctor.DescentData.pullFunctor,
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.isoMapOfCommSq_eq,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv,
    Pseudofunctor.DescentData.comp_hom,
    Category.assoc]
  dsimp [stackificationLiftPulledObjectCover,
    GrothendieckTopology.Cover.Arrow.base,
    stackificationLiftPulledObjectCoverModel]
  rw [Pseudofunctor.mapComp'_comp_id_inv_app]
  rw [Pseudofunctor.mapComp'_comp_id_hom_app]
  simp only [Category.assoc]
  let z₀ := stackificationLiftObjectGlued X G hG F y₀
  let z₁ := stackificationLiftObjectGlued X G hG F y₁
  let v := stackificationLiftVerticalMap X G hG F d
  let idIso := Fp.mapId (LocallyDiscrete.mk (op I.Y))
  let K := ((Fp.map (f.op.toLoc ≫ I.f.op.toLoc)).toFunctor)
  let mid₀ := (FibredCategoryMor.fiberFunctor F I.Y).obj
    (stackificationLiftObjectModel (J := J) G hG y₀ I₀.base).1
  let mid₁ := (FibredCategoryMor.fiberFunctor F I.Y).obj
    (stackificationLiftObjectModel (J := J) G hG y₁ I₁.base).1
  let eInv₀ := (stackificationLiftObjectGluedIso X G hG F y₀).inv.hom I₀.base
  let eHom₀ := (stackificationLiftObjectGluedIso X G hG F y₀).hom.hom I₀.base
  let eInv₁ := (stackificationLiftObjectGluedIso X G hG F y₁).inv.hom I₁.base
  let eHom₁ := (stackificationLiftObjectGluedIso X G hG F y₁).hom.hom I₁.base
  let cast₀ : K.obj z₀ ⟶
      (((Fp.toDescentData
        (fun I : (stackificationLiftObjectCover (J := J) G hG y₀).Arrow ↦ I.f)).obj z₀).obj
        I₀.base) :=
    eqToHom (by
      dsimp [K, z₀, Fp, I₀, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base])
  let cast₁ : K.obj z₁ ⟶ K.obj z₁ :=
    eqToHom (by
      dsimp [K, z₁, Fp, I₁, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base])
  let κ₀ := (Fp.mapComp' f.op.toLoc I.f.op.toLoc
    (f.op.toLoc ≫ I.f.op.toLoc) rfl).hom.toNatTrans.app z₀
  let κ₁ := (Fp.mapComp' f.op.toLoc I.f.op.toLoc
    (f.op.toLoc ≫ I.f.op.toLoc) rfl).inv.toNatTrans.app z₁
  let mv := M.map ((Fp.map f.op.toLoc).toFunctor.map v)
  have hfront :
      ((Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv₀) ≫
          idIso.hom.toNatTrans.app (K.obj z₀) =
        idIso.hom.toNatTrans.app mid₀ ≫ eInv₀ := by
    dsimp only [eInv₀, idIso, K, mid₀, z₀, Fp]
    simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] using
      (idIso.hom.toNatTrans.naturality
        ((stackificationLiftObjectGluedIso X G hG F y₀).inv.hom I₀.base))
  have hback :
      idIso.inv.toNatTrans.app (K.obj z₁) ≫
          ((Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eHom₁) =
        eHom₁ ≫ idIso.inv.toNatTrans.app mid₁ := by
    dsimp only [eHom₁, idIso, K, mid₁, z₁, Fp]
    simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] using
      (idIso.inv.toNatTrans.naturality
        ((stackificationLiftObjectGluedIso X G hG F y₁).hom.hom I₁.base)).symm
  have hfrontCast :
      (((Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv₀ ≫
          idIso.hom.toNatTrans.app (K.obj z₀)) ≫ cast₀) =
        (idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀ := by
    exact congrArg (fun t => t ≫ cast₀) hfront
  have hfrontCastAssoc :
      (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv₀ ≫
          (idIso.hom.toNatTrans.app (K.obj z₀) ≫ cast₀) =
        (idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀ := by
    rw [← Category.assoc]
    exact hfrontCast
  have hfrontK :
      (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv₀ ≫
          ((idIso.hom.toNatTrans.app (K.obj z₀) ≫ cast₀) ≫ κ₀) =
        ((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ κ₀ := by
    rw [← Category.assoc]
    exact congrArg (fun t => t ≫ κ₀) hfrontCastAssoc
  have hfrontKM :
      (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv₀ ≫
          (((idIso.hom.toNatTrans.app (K.obj z₀) ≫ cast₀) ≫ κ₀) ≫ mv) =
        (((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ κ₀) ≫ mv := by
    rw [← Category.assoc]
    exact congrArg (fun t => t ≫ mv) hfrontK
  have hfrontKM_assoc :
      (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv₀ ≫
          ((idIso.hom.toNatTrans.app (K.obj z₀) ≫ cast₀ ≫ κ₀) ≫ mv) =
        (((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ κ₀) ≫ mv := by
    simpa only [Category.assoc] using hfrontKM
  dsimp only [I₀, I₁, eInv₀, eHom₁, idIso, K, cast₀, cast₁, κ₀, κ₁, mv, v, z₀, z₁, Fp,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] at hfront hback hfrontCast hfrontCastAssoc hfrontK hfrontKM hfrontKM_assoc ⊢
  slice_lhs 1 5 => exact hfrontKM_assoc
  have hκtail :
      κ₀ ≫ mv ≫
          (κ₁ ≫ (cast₁ ≫ idIso.inv.toNatTrans.app (K.obj z₁) ≫
            (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eHom₁)) =
        K.map v ≫
          (cast₁ ≫ idIso.inv.toNatTrans.app (K.obj z₁) ≫
            (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eHom₁) := by
    exact
      Pseudofunctor.mapComp_hom_map_inv_assoc Fp f I.f v
        (cast₁ ≫ idIso.inv.toNatTrans.app (K.obj z₁) ≫
          (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eHom₁)
  have hκtail_prefix :
      (((((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ κ₀) ≫ mv) ≫
          (((κ₁ ≫ cast₁) ≫ idIso.inv.toNatTrans.app (K.obj z₁)) ≫
            (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eHom₁)) =
        ((((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ K.map v) ≫
          (cast₁ ≫ idIso.inv.toNatTrans.app (K.obj z₁) ≫
            (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eHom₁)) := by
    simpa only [Category.assoc] using
      congrArg (fun t => ((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ t)
        hκtail
  dsimp only [I₀, I₁, eInv₀, eHom₁, idIso, K, cast₀, cast₁, κ₀, κ₁, mv, v, z₀, z₁, Fp,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] at hκtail_prefix
  refine hκtail_prefix.trans ?_
  have htail :
      (((((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ K.map v) ≫ cast₁) ≫
          idIso.inv.toNatTrans.app (K.obj z₁)) ≫
        (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eHom₁ =
      (((((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ K.map v) ≫ cast₁) ≫
        eHom₁) ≫ idIso.inv.toNatTrans.app mid₁ := by
    simpa only [Category.assoc] using
      Pseudofunctor.mapId_inv_map_assoc₂ Fp I.Y eHom₁
        (((((idIso.hom.toNatTrans.app mid₀ ≫ eInv₀) ≫ cast₀) ≫ K.map v) ≫ cast₁))
  dsimp only [I₀, I₁, eInv₀, eHom₁, idIso, K, cast₀, cast₁, κ₀, κ₁, mv, v, z₀, z₁, Fp,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] at htail
  have htail' := htail
  simp only [Category.assoc] at htail'
  simp only [Category.assoc]
  refine htail'.trans ?_
  have hmiddle :
      eInv₀ ≫ cast₀ ≫ K.map v ≫ cast₁ ≫ eHom₁ = Hbase := by
    have hv := stackificationLiftVerticalMap_local X G hG F d I.base
    have hvK :
        K.map v = stackificationLiftVerticalLocalMap X G hG F d I.base := by
      dsimp only [K, v, Fp]
      simpa [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] using hv
    have hlocalnorm :
        stackificationLiftVerticalLocalMap X G hG F d I.base =
          (stackificationLiftObjectGluedLocalIso X G hG F y₀ I₀.base).hom ≫
            Hbase ≫
            (stackificationLiftObjectGluedLocalIso X G hG F y₁ I₁.base).inv := by
      dsimp [stackificationLiftVerticalLocalMap, Hbase, I₀, I₁,
        stackificationLiftPulledObjectCoverModel,
        stackificationLiftVerticalCommonCover_left,
        stackificationLiftVerticalCommonCover_right, stackificationLiftVerticalCommonCover,
        stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
      rfl
    rw [hvK]
    rw [hlocalnorm]
    dsimp [eInv₀, eHom₁, cast₀, cast₁, stackificationLiftObjectGluedLocalIso]
    let L₀ := stackificationLiftObjectGluedLocalIso X G hG F y₀ I₀.base
    let L₁ := stackificationLiftObjectGluedLocalIso X G hG F y₁ I₁.base
    change L₀.inv ≫ 𝟙 (K.obj z₀) ≫
        ((L₀.hom ≫ Hbase ≫ L₁.inv) ≫ 𝟙 (K.obj z₁) ≫ L₁.hom) =
      Hbase
    have hcomp₀ : L₀.inv ≫ 𝟙 (K.obj z₀) = L₀.inv := by
      simpa only [K, z₀, Fp, I₀, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base] using (Category.comp_id L₀.inv)
    have hcomp₁ : L₁.inv ≫ 𝟙 (K.obj z₁) = L₁.inv := by
      simpa only [K, z₁, Fp, I₁, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base] using (Category.comp_id L₁.inv)
    simp only [Category.assoc]
    slice_lhs 1 2 => exact hcomp₀
    slice_lhs 4 5 => exact hcomp₁
    slice_lhs 1 2 => exact L₀.inv_hom_id
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 2 3 => exact L₁.inv_hom_id
    simpa only [I₀, I₁, stackificationLiftPulledObjectCoverModel,
      stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] using
      (Category.comp_id Hbase)
  dsimp only [I₀, I₁, eInv₀, eHom₁, idIso, K, cast₀, cast₁, κ₀, κ₁, mv, v, z₀, z₁, Fp,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] at hmiddle ⊢
  have hreplace :
      (Fp.mapId (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app mid₀ ≫
          (eInv₀ ≫ cast₀ ≫ K.map v ≫ cast₁ ≫ eHom₁) ≫
          (Fp.mapId (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app mid₁ =
        (Fp.mapId (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app mid₀ ≫
          Hbase ≫
          (Fp.mapId (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app mid₁ := by
    exact congrArg
      (fun t => (Fp.mapId (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app mid₀ ≫
        t ≫ (Fp.mapId (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app mid₁)
      hmiddle
  have hreplace' :
      (Fp.mapId (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app mid₀ ≫
          eInv₀ ≫ cast₀ ≫ K.map v ≫ cast₁ ≫ eHom₁ ≫
          (Fp.mapId (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app mid₁ =
        (Fp.mapId (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app mid₀ ≫
          Hbase ≫
          (Fp.mapId (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app mid₁ := by
    simpa only [Category.assoc] using
      hreplace
  refine hreplace'.trans ?_
  simpa [stackificationLiftObjectDescentData, Category.assoc] using
    (Pseudofunctor.mapId_hom_comp_inv Fp I.Y Hbase)

end

end CategoryTheory
