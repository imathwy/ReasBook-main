import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.BaseChangeData
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.MapIdCancellation

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Local normalization for the pulled-glued descent isomorphism: its forward component followed
by the identity pseudofunctor comparison is the canonical two-leg pullback comparison followed by
the original glued local isomorphism. -/
theorem stackificationLiftPulledGluedObjectDescentIso_hom_comp_mapId_hom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let Ibase := I.base
    let mid := (FibredCategoryMor.fiberFunctor F I.Y).obj
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
    let κGlued := mapCompAppIso X.p f I.f (I.f ≫ f)
      (FibredCategoryMor.comp_toLoc_eq f I.f (I.f ≫ f) rfl)
      (stackificationLiftObjectGlued X G hG F y)
    (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
        ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I.Y)))).app mid).hom =
      κGlued.inv ≫
        (stackificationLiftObjectGluedLocalIso X G hG F y Ibase).hom := by
  intro Fp Ibase mid κGlued
  dsimp only [mid]
  simp only [stackificationLiftPulledGluedObjectDescentIso,
    stackificationLiftPulledObjectDescentData,
    stackificationLiftPulledObjectDescentPullFunctor,
    Pseudofunctor.DescentData.pullFunctor,
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.isoMapOfCommSq_eq,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Pseudofunctor.DescentData.comp_hom,
    Category.assoc]
  dsimp [κGlued, stackificationLiftPulledObjectCover,
    GrothendieckTopology.Cover.Arrow.base,
    stackificationLiftPulledObjectCoverModel]
  let Fp := canonicalFiberPseudofunctor X.p
  let e := (stackificationLiftObjectGluedIso X G hG F y).hom.hom Ibase
  let A := (Fp.mapComp' f.op.toLoc I.f.op.toLoc
    (f.op.toLoc ≫ I.f.op.toLoc)
    (FibredCategoryMor.comp_toLoc_eq f I.f (I.f ≫ f) rfl)).inv.toNatTrans.app
      (stackificationLiftObjectGlued X G hG F y)
  let Aκ := (Fp.mapComp' f.op.toLoc I.f.op.toLoc
    (I.f ≫ f).op.toLoc
    (FibredCategoryMor.comp_toLoc_eq f I.f (I.f ≫ f) rfl)).inv.toNatTrans.app
      (stackificationLiftObjectGlued X G hG F y)
  have hid :
      (Fp.mapId (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app
          ((Fp.map (f.op.toLoc ≫ I.f.op.toLoc)).toFunctor.obj
            (stackificationLiftObjectGlued X G hG F y)) ≫
        (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map e ≫
        (Fp.mapId (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor F I.Y).obj
            (stackificationLiftObjectModel (J := J) G hG y Ibase).1) =
      e := by
    simpa [Fp, e, Ibase] using
      Pseudofunctor.mapId_inv_map_hom_hom Fp I.Y e
  let compHom := (Fp.mapComp' (f.op.toLoc ≫ I.f.op.toLoc)
    (𝟙 (LocallyDiscrete.mk (op I.Y))) (f.op.toLoc ≫ I.f.op.toLoc)
    (by simp)).hom.toNatTrans.app (stackificationLiftObjectGlued X G hG F y)
  let mapE := (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map e
  let idHom' :=
    (Fp.mapId (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftObjectModel (J := J) G hG y Ibase).1)
  have htail : compHom ≫ mapE ≫ idHom' = e := by
    dsimp [compHom, mapE, idHom']
    rw [Pseudofunctor.mapComp'_comp_id_hom_app]
    simpa [Fp, e, Ibase, Category.assoc] using hid
  have hcalc : ((A ≫ compHom) ≫ mapE) ≫ idHom' = A ≫ e := by
    calc
      ((A ≫ compHom) ≫ mapE) ≫ idHom' =
          A ≫ (compHom ≫ mapE ≫ idHom') := by
        simp only [Category.assoc]
      _ = A ≫ e := by
        exact congrArg (fun t => A ≫ t) htail
  have hAκ : A ≫ e = Aκ ≫ e := by
    dsimp [A, Aκ]
  have hcalc' : (A ≫ compHom) ≫ (mapE ≫ idHom') = Aκ ≫ e := by
    simpa only [Category.assoc] using hcalc.trans hAκ
  dsimp only [A, Aκ, compHom, mapE, idHom', e, κGlued, mapCompAppIso,
    stackificationLiftObjectGluedLocalIso] at hcalc' ⊢
  dsimp only [Fp, Ibase, stackificationLiftPulledObjectCover,
    GrothendieckTopology.Cover.Arrow.base] at hcalc' ⊢
  exact hcalc'

/-- Inverse local normalization for the pulled-glued descent isomorphism. -/
theorem stackificationLiftPulledGluedObjectDescentIso_mapId_inv_comp_inv
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let Ibase := I.base
    let mid := (FibredCategoryMor.fiberFunctor F I.Y).obj
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
    let κGlued := mapCompAppIso X.p f I.f (I.f ≫ f)
      (FibredCategoryMor.comp_toLoc_eq f I.f (I.f ≫ f) rfl)
      (stackificationLiftObjectGlued X G hG F y)
    ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I.Y)))).app mid).symm.hom ≫
        (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).inv.hom I =
      (stackificationLiftObjectGluedLocalIso X G hG F y Ibase).inv ≫
        κGlued.hom := by
  intro Fp Ibase mid κGlued
  let PG := stackificationLiftPulledGluedObjectDescentIso X G hG F f y
  let idIso := (Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I.Y)))).app mid
  let L := stackificationLiftObjectGluedLocalIso X G hG F y Ibase
  have hhom :=
    stackificationLiftPulledGluedObjectDescentIso_hom_comp_mapId_hom X G hG F f y I
  dsimp only at hhom
  change PG.hom.hom I ≫ idIso.hom = κGlued.inv ≫ L.hom at hhom
  have hPGhom : PG.hom.hom I ≫ PG.inv.hom I = 𝟙 _ := by
    have h := congrArg (fun η => Pseudofunctor.DescentData.Hom.hom η I) PG.hom_inv_id
    simpa only [Pseudofunctor.DescentData.comp_hom] using h
  have hPG : PG.inv.hom I ≫ PG.hom.hom I = 𝟙 _ := by
    have h := congrArg (fun η => Pseudofunctor.DescentData.Hom.hom η I) PG.inv_hom_id
    simpa only [Pseudofunctor.DescentData.comp_hom] using h
  haveI : IsIso (PG.hom.hom I) := ⟨⟨PG.inv.hom I, hPGhom, hPG⟩⟩
  have hId : idIso.inv ≫ idIso.hom = 𝟙 _ := idIso.inv_hom_id
  have hId' : idIso.inv ≫ 𝟙 _ ≫ idIso.hom = 𝟙 _ := by
    simpa only [Category.id_comp] using hId
  apply (cancel_mono (PG.hom.hom I ≫ idIso.hom)).1
  change (idIso.inv ≫ PG.inv.hom I) ≫ PG.hom.hom I ≫ idIso.hom =
    (L.inv ≫ κGlued.hom) ≫ PG.hom.hom I ≫ idIso.hom
  simp only [Category.assoc]
  slice_lhs 2 3 => exact hPG
  slice_lhs 1 3 => exact hId'
  slice_rhs 3 4 => exact hhom
  have hκtail : κGlued.hom ≫ κGlued.inv ≫ L.hom = L.hom := by
    rw [← Category.assoc]
    rw [κGlued.hom_inv_id]
    simp only [Category.id_comp]
  slice_rhs 2 4 => exact hκtail
  exact L.inv_hom_id.symm

end

namespace Pseudofunctor

section IdentityTail

variable {C : Type u} [Category.{v} C]

/-- Identity-tail normalization for a threefold composite in the canonical fiber
pseudofunctor.  This is the local pseudofunctor coherence used in the composition
cocycle, comparing the two bracketings of `a ≫ b ≫ c`. -/
theorem mapComp_id_assoc_tail_app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS})
    {U V W Y : C} (f : V ⟶ U) (g : W ⟶ V) (i : Y ⟶ W)
    (z : F.obj (LocallyDiscrete.mk (op U))) :
    let loc := LocallyDiscrete.mk (op Y)
    let a := f.op.toLoc
    let b := g.op.toLoc
    let c := i.op.toLoc
    (F.mapId loc).inv.toNatTrans.app ((F.map (a ≫ b ≫ c)).toFunctor.obj z) ≫
        ((F.mapComp' (a ≫ b ≫ c) (𝟙 loc) (a ≫ b ≫ c)
            (by rw [Category.comp_id])).inv.toNatTrans.app z ≫
          (F.mapComp' ((a ≫ b) ≫ c) (𝟙 loc) (a ≫ b ≫ c)
            (by rw [Category.comp_id, Category.assoc])).hom.toNatTrans.app z) ≫
        (F.mapId loc).hom.toNatTrans.app ((F.map ((a ≫ b) ≫ c)).toFunctor.obj z) =
      (F.mapComp' a (b ≫ c) (a ≫ b ≫ c) (by simp)).hom.toNatTrans.app z ≫
        (F.mapComp' a (b ≫ c) ((a ≫ b) ≫ c)
          (by simp [Category.assoc])).inv.toNatTrans.app z := by
  intro loc a b c
  rw [Pseudofunctor.mapComp'_comp_id_inv_app]
  dsimp [loc]
  simp only [Category.comp_id, Category.assoc]
  slice_lhs 1 2 =>
    exact Cat.Hom.inv_hom_id_toNatTrans_app
      (F.mapId (LocallyDiscrete.mk (op Y))) ((F.map (a ≫ b ≫ c)).toFunctor.obj z)
  simp [Pseudofunctor.mapComp', F.mapComp_id_right_hom,
    Bicategory.Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom, Category.assoc]
  slice_lhs 2 3 =>
    exact Cat.Hom.inv_hom_id_toNatTrans_app
      (F.mapId (LocallyDiscrete.mk (op Y))) ((F.map ((a ≫ b) ≫ c)).toFunctor.obj z)
  slice_rhs 1 2 =>
    exact Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp a (b ≫ c)) z
  change eqToHom _ ≫ 𝟙 ((F.map ((a ≫ b) ≫ c)).toFunctor.obj z) =
    𝟙 ((F.map (a ≫ b ≫ c)).toFunctor.obj z) ≫ eqToHom _
  simp only [Category.comp_id, Category.id_comp]

end IdentityTail

end Pseudofunctor

end CategoryTheory
