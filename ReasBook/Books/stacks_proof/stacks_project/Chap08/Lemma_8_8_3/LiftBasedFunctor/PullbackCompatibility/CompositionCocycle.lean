import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.VerticalNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityPullback
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.MapCompCocycle
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.CompositionCocycleLocal
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.CompositionCocycleModel

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Composition cocycle for the glued object pullback comparison.

This is the isolated composition blocker for Chap08 Lemma 8 8 3.  It says that comparing the
glued object with a two-step pullback and then normalizing along the canonical pullback-composition
isomorphism agrees with the direct comparison for the composite base map. -/
theorem stackificationLiftObjectPullbackComparison_comp_inv
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V W : C} (g : W ⟶ V) (f : V ⟶ U) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (y : S'.p.Fiber U) :
    (stackificationLiftObjectPullbackComparison X G hG F g
        (f ^*[canonicalPullbackChoice S'.p] y)).inv ≫
      stackificationLiftVerticalMap X G hG F
        (mapCompAppIso S'.p f g gf
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf) y).inv ≫
      (stackificationLiftObjectPullbackComparison X G hG F gf y).hom =
        ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (stackificationLiftObjectPullbackComparison X G hG F f y).hom ≫
        (mapCompAppIso X.p f g gf
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)
          (stackificationLiftObjectGlued X G hG F y)).inv := by
  subst gf
  apply stack_cover_hom_ext (J := J) X
    (stackificationLiftPulledObjectCover (J := J) G hG (g ≫ f) y)
  intro I
  let If : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow :=
    ⟨I.Y, I.f ≫ g, by
      dsimp [stackificationLiftPulledObjectCover] at I ⊢
      simpa [Category.assoc] using I.hf⟩
  let Ig : (stackificationLiftPulledObjectCover (J := J) G hG g
      (f ^*[canonicalPullbackChoice S'.p] y)).Arrow :=
    ⟨I.Y, I.f, by
      dsimp [stackificationLiftPulledObjectCover]
      exact (stackificationLiftPulledToObjectCover (J := J) G hG f y If).hf⟩
  let Iv : (stackificationLiftVerticalCommonCover (J := J) G hG
      (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y))
      ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y)).Arrow :=
    ⟨I.Y, I.f, by
      exact ⟨(stackificationLiftPulledToObjectCover (J := J) G hG g
          (f ^*[canonicalPullbackChoice S'.p] y) Ig).hf,
        (stackificationLiftPulledToObjectCover (J := J) G hG (g ≫ f) y I).hf⟩⟩
  let M := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
  change M.map
      ((stackificationLiftObjectPullbackComparison X G hG F g
          (f ^*[canonicalPullbackChoice S'.p] y)).inv ≫
        stackificationLiftVerticalMap X G hG F
          (mapCompAppIso S'.p f g (g ≫ f)
            (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) y).inv ≫
          (stackificationLiftObjectPullbackComparison X G hG F (g ≫ f) y).hom) =
    M.map
      (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (stackificationLiftObjectPullbackComparison X G hG F f y).hom ≫
        (mapCompAppIso X.p f g (g ≫ f)
          (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl)
          (stackificationLiftObjectGlued X G hG F y)).inv)
  rw [M.map_comp]
  rw [M.map_comp]
  rw [M.map_comp]
  simp only [Category.assoc]
  rw [stackificationLiftObjectPullbackComparison_local_inv X G hG F g
    (f ^*[canonicalPullbackChoice S'.p] y) Ig]
  rw [stackificationLiftVerticalMap_local X G hG F
    (mapCompAppIso S'.p f g (g ≫ f)
      (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) y).inv Iv]
  rw [stackificationLiftObjectPullbackComparison_local_hom X G hG F (g ≫ f) y I]
  let κXgI := mapCompAppIso X.p g I.f (I.f ≫ g)
    (FibredCategoryMor.comp_toLoc_eq g I.f (I.f ≫ g) rfl)
    (stackificationLiftObjectGlued X G hG F
      (f ^*[canonicalPullbackChoice S'.p] y))
  let κXgItarget := mapCompAppIso X.p g I.f (I.f ≫ g)
    (FibredCategoryMor.comp_toLoc_eq g I.f (I.f ≫ g) rfl)
    (f ^*[canonicalPullbackChoice X.p] stackificationLiftObjectGlued X G hG F y)
  let κXfIg := mapCompAppIso X.p f (I.f ≫ g) (I.f ≫ (g ≫ f))
    (FibredCategoryMor.comp_toLoc_eq f (I.f ≫ g) (I.f ≫ (g ≫ f)) (by
      simp [Category.assoc]))
    (stackificationLiftObjectGlued X G hG F y)
  let κXgfI := mapCompAppIso X.p (g ≫ f) I.f (I.f ≫ (g ≫ f))
    (FibredCategoryMor.comp_toLoc_eq (g ≫ f) I.f (I.f ≫ (g ≫ f)) rfl)
    (stackificationLiftObjectGlued X G hG F y)
  have hR₀ :
      M.map (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (stackificationLiftObjectPullbackComparison X G hG F f y).hom) =
        κXgI.inv ≫
          ((canonicalFiberPseudofunctor X.p).map (I.f ≫ g).op.toLoc).toFunctor.map
            (stackificationLiftObjectPullbackComparison X G hG F f y).hom ≫
          κXgItarget.hom := by
    simpa [M, κXgI, κXgItarget] using
      mapCompAppIso_inv_comp_map_map_hom X.p g I.f
        (stackificationLiftObjectPullbackComparison X G hG F f y).hom
  rw [hR₀]
  rw [stackificationLiftObjectPullbackComparison_local_hom X G hG F f y If]
  have hR₁ :
      κXgItarget.hom ≫
        M.map (mapCompAppIso X.p f g (g ≫ f)
          (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl)
          (stackificationLiftObjectGlued X G hG F y)).inv =
        κXfIg.inv ≫ κXgfI.hom := by
    simpa [M, κXgItarget, κXfIg, κXgfI] using
      mapCompAppIso_hom_comp_map_inv X.p f g I.f (g ≫ f) rfl
        (stackificationLiftObjectGlued X G hG F y)
  let Df := (stackificationLiftPulledObjectDescentComparison X G hG F f y).hom.hom If
  let Bf := (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).inv.hom If
  have hR₁' :
      (κXgI.inv ≫ ((Df ≫ Bf) ≫ κXgItarget.hom)) ≫
          M.map (mapCompAppIso X.p f g (g ≫ f)
            (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl)
            (stackificationLiftObjectGlued X G hG F y)).inv =
        κXgI.inv ≫ Df ≫ Bf ≫ κXfIg.inv ≫ κXgfI.hom := by
    simpa only [Category.assoc] using
      congrArg (fun t => (κXgI.inv ≫ (Df ≫ Bf)) ≫ t) hR₁
  change _ =
    (κXgI.inv ≫ ((Df ≫ Bf) ≫ κXgItarget.hom)) ≫
      M.map (mapCompAppIso X.p f g (g ≫ f)
        (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl)
        (stackificationLiftObjectGlued X G hG F y)).inv
  rw [hR₁']
  simp only [Category.assoc]
  dsimp only [Df, Bf]
  rw [stackificationLiftPulledObjectDescentComparison_hom_hom]
  rw [stackificationLiftPulledObjectDescentComparison_hom_hom]
  have hDgInv :
      (stackificationLiftPulledObjectDescentComparison X G hG F g
          (f ^*[canonicalPullbackChoice S'.p] y)).inv.hom Ig =
        (stackificationLiftPulledLocalIso X G hG F g
          (f ^*[canonicalPullbackChoice S'.p] y) Ig).inv := by
    rfl
  rw [hDgInv]
  rw [stackificationLiftPulledLocalIso_inv]
  rw [stackificationLiftPulledLocalIso_hom]
  rw [stackificationLiftPulledLocalIso_hom]
  have hPGg :=
    stackificationLiftPulledGluedObjectDescentIso_hom_comp_mapId_hom X G hG F g
    (f ^*[canonicalPullbackChoice S'.p] y) Ig
  dsimp only at hPGg
  simp only [Category.assoc]
  let PgInv := (stackificationLiftPulledModelComparisonIso X G hG F g
    (f ^*[canonicalPullbackChoice S'.p] y) Ig).inv
  let LgInv := (stackificationLiftObjectGluedLocalIso X G hG F
    (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y))
    (stackificationLiftPulledToObjectCover (J := J) G hG g
      (f ^*[canonicalPullbackChoice S'.p] y) Ig)).inv
  have hPGg' :
      (stackificationLiftPulledGluedObjectDescentIso X G hG F g
          (f ^*[canonicalPullbackChoice S'.p] y)).hom.hom Ig ≫
        ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
          (LocallyDiscrete.mk (op Ig.Y)))).app
            ((FibredCategoryMor.fiberFunctor F Ig.Y).obj
              (stackificationLiftPulledObjectCoverModel (J := J) G hG g
                (f ^*[canonicalPullbackChoice S'.p] y) Ig).1)).hom ≫
        PgInv ≫ LgInv =
        κXgI.inv ≫
        (stackificationLiftObjectGluedLocalIso X G hG F
          (f ^*[canonicalPullbackChoice S'.p] y) Ig.base).hom ≫
        PgInv ≫ LgInv := by
    have h := congrArg (fun t => t ≫ PgInv ≫ LgInv) hPGg
    dsimp only [PgInv, LgInv, κXgI] at h
    calc
      (stackificationLiftPulledGluedObjectDescentIso X G hG F g
            (f ^*[canonicalPullbackChoice S'.p] y)).hom.hom Ig ≫
          ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
            (LocallyDiscrete.mk (op Ig.Y)))).app
              ((FibredCategoryMor.fiberFunctor F Ig.Y).obj
                (stackificationLiftPulledObjectCoverModel (J := J) G hG g
                  (f ^*[canonicalPullbackChoice S'.p] y) Ig).1)).hom ≫
          PgInv ≫ LgInv =
        ((stackificationLiftPulledGluedObjectDescentIso X G hG F g
            (f ^*[canonicalPullbackChoice S'.p] y)).hom.hom Ig ≫
          ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
            (LocallyDiscrete.mk (op Ig.Y)))).app
              ((FibredCategoryMor.fiberFunctor F Ig.Y).obj
                (stackificationLiftPulledObjectCoverModel (J := J) G hG g
                  (f ^*[canonicalPullbackChoice S'.p] y) Ig).1)).hom) ≫
          PgInv ≫ LgInv := by
          simp only [Category.assoc]
      _ =
        (κXgI.inv ≫
          (stackificationLiftObjectGluedLocalIso X G hG F
            (f ^*[canonicalPullbackChoice S'.p] y) Ig.base).hom) ≫
          PgInv ≫ LgInv := by
          exact h
      _ =
        κXgI.inv ≫
          (stackificationLiftObjectGluedLocalIso X G hG F
            (f ^*[canonicalPullbackChoice S'.p] y) Ig.base).hom ≫
          PgInv ≫ LgInv := by
          simp only [Category.assoc]
  dsimp [canonicalPullbackChoice, PgInv, LgInv] at hPGg' ⊢
  slice_lhs 1 4 => exact hPGg'
  simp only [Category.assoc]
  have hPGgf :=
    stackificationLiftPulledGluedObjectDescentIso_mapId_inv_comp_inv X G hG F (g ≫ f) y I
  dsimp only at hPGgf
  have hPGgf' :
      ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op I.Y)))).app
          ((FibredCategoryMor.fiberFunctor F I.Y).obj
            (stackificationLiftPulledObjectCoverModel (J := J) G hG (g ≫ f) y I).1)).symm.hom ≫
        (stackificationLiftPulledGluedObjectDescentIso X G hG F (g ≫ f) y).inv.hom I =
      (stackificationLiftObjectGluedLocalIso X G hG F y I.base).inv ≫
        κXgfI.hom := by
    simpa [κXgfI, Category.assoc] using hPGgf
  have hPGf :=
    stackificationLiftPulledGluedObjectDescentIso_mapId_inv_comp_inv X G hG F f y If
  dsimp only at hPGf
  let κXfIf := mapCompAppIso X.p f If.f (If.f ≫ f)
    (FibredCategoryMor.comp_toLoc_eq f If.f (If.f ≫ f) rfl)
    (stackificationLiftObjectGlued X G hG F y)
  have hPGf' :
      ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op If.Y)))).app
          ((FibredCategoryMor.fiberFunctor F If.Y).obj
            (stackificationLiftPulledObjectCoverModel (J := J) G hG f y If).1)).symm.hom ≫
        (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).inv.hom If =
      (stackificationLiftObjectGluedLocalIso X G hG F y If.base).inv ≫
        κXfIf.hom := by
    simpa [κXfIf, Category.assoc] using hPGf
  dsimp [canonicalPullbackChoice] at hPGgf' hPGf' ⊢
  let LgBaseHom := (stackificationLiftObjectGluedLocalIso X G hG F
    (f ^*[canonicalPullbackChoice S'.p] y) Ig.base).hom
  let PgInv' := (stackificationLiftPulledModelComparisonIso X G hG F g
    (f ^*[canonicalPullbackChoice S'.p] y) Ig).inv
  let LggInv := (stackificationLiftObjectGluedLocalIso X G hG F
    (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y))
    (stackificationLiftPulledToObjectCover (J := J) G hG g
      (f ^*[canonicalPullbackChoice S'.p] y) Ig)).inv
  let Vloc := stackificationLiftVerticalLocalMap X G hG F
    (mapCompAppIso S'.p f g (g ≫ f)
      (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) y).inv Iv
  let LgfHom := (stackificationLiftObjectGluedLocalIso X G hG F
    ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y)
    (stackificationLiftPulledToObjectCover (J := J) G hG (g ≫ f) y I)).hom
  let PgfHom := (stackificationLiftPulledModelComparisonIso X G hG F (g ≫ f) y I).hom
  let idgf :=
    ((canonicalFiberPseudofunctor X.p).mapId
      (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor F I.Y).obj
          (stackificationLiftPulledObjectCoverModel (J := J) G hG (g ≫ f) y I).1)
  let PGgfInv := (stackificationLiftPulledGluedObjectDescentIso X G hG F (g ≫ f) y).inv.hom I
  let LgfBaseInv := (stackificationLiftObjectGluedLocalIso X G hG F y I.base).inv
  let LfHom := (stackificationLiftObjectGluedLocalIso X G hG F
    (f ^*[canonicalPullbackChoice S'.p] y)
    (stackificationLiftPulledToObjectCover (J := J) G hG f y If)).hom
  let PfHom := (stackificationLiftPulledModelComparisonIso X G hG F f y If).hom
  let idf :=
    ((canonicalFiberPseudofunctor X.p).mapId
      (LocallyDiscrete.mk (op If.Y))).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor F If.Y).obj
          (stackificationLiftPulledObjectCoverModel (J := J) G hG f y If).1)
  let PGfInv := (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).inv.hom If
  let LfBaseInv := (stackificationLiftObjectGluedLocalIso X G hG F y If.base).inv
  have hTailgf :
      (LgfHom ≫ PgfHom ≫ idgf) ≫ PGgfInv =
        LgfHom ≫ PgfHom ≫ LgfBaseInv ≫ κXgfI.hom := by
    calc
      (LgfHom ≫ PgfHom ≫ idgf) ≫ PGgfInv =
          LgfHom ≫ PgfHom ≫ (idgf ≫ PGgfInv) := by
        simp only [Category.assoc]
      _ = LgfHom ≫ PgfHom ≫ (LgfBaseInv ≫ κXgfI.hom) := by
        exact congrArg (fun t => LgfHom ≫ PgfHom ≫ t) hPGgf'
      _ = LgfHom ≫ PgfHom ≫ LgfBaseInv ≫ κXgfI.hom := by
        simp only [Category.assoc]
  have hTailf :
      (LfHom ≫ PfHom ≫ idf) ≫ PGfInv =
        LfHom ≫ PfHom ≫ LfBaseInv ≫ κXfIf.hom := by
    calc
      (LfHom ≫ PfHom ≫ idf) ≫ PGfInv =
          LfHom ≫ PfHom ≫ (idf ≫ PGfInv) := by
        simp only [Category.assoc]
      _ = LfHom ≫ PfHom ≫ (LfBaseInv ≫ κXfIf.hom) := by
        exact congrArg (fun t => LfHom ≫ PfHom ≫ t) hPGf'
      _ = LfHom ≫ PfHom ≫ LfBaseInv ≫ κXfIf.hom := by
        simp only [Category.assoc]
  have hLtail := congrArg
    (fun t => (κXgI.inv ≫ LgBaseHom ≫ PgInv' ≫ LggInv) ≫ Vloc ≫ t)
    hTailgf
  have hRtail := congrArg
    (fun t => κXgI.inv ≫ t ≫ κXfIg.inv ≫ κXgfI.hom)
    hTailf
  have hCore :
      LgBaseHom ≫ PgInv' ≫ LggInv ≫ Vloc ≫ LgfHom ≫ PgfHom ≫
          LgfBaseInv =
        LfHom ≫ PfHom ≫ LfBaseInv ≫ κXfIf.hom ≫ κXfIg.inv := by
    let Izg := stackificationLiftPulledToObjectCover (J := J) G hG g
      (f ^*[canonicalPullbackChoice S'.p] y) Ig
    let Izgf := stackificationLiftPulledToObjectCover (J := J) G hG (g ≫ f) y I
    let Lleft := stackificationLiftObjectGluedLocalIso X G hG F
      (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y)) Izg
    let Lright := stackificationLiftObjectGluedLocalIso X G hG F
      ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y) Izgf
    let Hmid := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG
        (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y)) Izg).1
      (stackificationLiftObjectModel (J := J) G hG
        ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y) Izgf).1
      ((stackificationLiftObjectModel (J := J) G hG
          (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y)) Izg).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
          (mapCompAppIso S'.p f g (g ≫ f)
            (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) y).inv ≫
        (stackificationLiftObjectModel (J := J) G hG
          ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y) Izgf).2.inv)
    have hVloc : Vloc = Lleft.hom ≫ Hmid ≫ Lright.inv := by
      dsimp [Vloc, Lleft, Lright, Hmid, Izg, Izgf,
        stackificationLiftVerticalLocalMap,
        stackificationLiftVerticalCommonCover_left,
        stackificationLiftVerticalCommonCover_right,
        stackificationLiftPulledToObjectCover, Iv, Ig,
        GrothendieckTopology.Cover.Arrow.map]
      rfl
    have hCancel :
        LgBaseHom ≫ PgInv' ≫ LggInv ≫ Vloc ≫ LgfHom ≫ PgfHom ≫ LgfBaseInv =
          LgBaseHom ≫ PgInv' ≫ Hmid ≫ PgfHom ≫ LgfBaseInv := by
      rw [hVloc]
      change LgBaseHom ≫ PgInv' ≫ Lleft.inv ≫
          (Lleft.hom ≫ Hmid ≫ Lright.inv) ≫
          Lright.hom ≫ PgfHom ≫ LgfBaseInv =
        LgBaseHom ≫ PgInv' ≫ Hmid ≫ PgfHom ≫ LgfBaseInv
      calc
        LgBaseHom ≫ PgInv' ≫ Lleft.inv ≫
            (Lleft.hom ≫ Hmid ≫ Lright.inv) ≫
            Lright.hom ≫ PgfHom ≫ LgfBaseInv =
          LgBaseHom ≫ PgInv' ≫ (Lleft.inv ≫ Lleft.hom) ≫
              Hmid ≫ (Lright.inv ≫ Lright.hom) ≫
              PgfHom ≫ LgfBaseInv := by
            simp only [Category.assoc]
        _ = LgBaseHom ≫ PgInv' ≫ Hmid ≫ PgfHom ≫ LgfBaseInv := by
            have hleft :
                LgBaseHom ≫ PgInv' ≫ (Lleft.inv ≫ Lleft.hom) ≫ Hmid ≫
                    (Lright.inv ≫ Lright.hom) ≫ PgfHom ≫ LgfBaseInv =
                  LgBaseHom ≫ PgInv' ≫ (𝟙 _) ≫ Hmid ≫
                    (Lright.inv ≫ Lright.hom) ≫ PgfHom ≫ LgfBaseInv := by
              exact congrArg
                (fun t => LgBaseHom ≫ PgInv' ≫ t ≫ Hmid ≫
                  (Lright.inv ≫ Lright.hom) ≫ PgfHom ≫ LgfBaseInv)
                Lleft.inv_hom_id
            have hright :
                LgBaseHom ≫ PgInv' ≫ (𝟙 _) ≫ Hmid ≫
                    (Lright.inv ≫ Lright.hom) ≫ PgfHom ≫ LgfBaseInv =
                  LgBaseHom ≫ PgInv' ≫ (𝟙 _) ≫ Hmid ≫
                    (𝟙 _) ≫ PgfHom ≫ LgfBaseInv := by
              exact congrArg
                (fun t => LgBaseHom ≫ PgInv' ≫ (𝟙 _) ≫ Hmid ≫ t ≫
                  PgfHom ≫ LgfBaseInv)
                Lright.inv_hom_id
            exact hleft.trans <| hright.trans <| by
              simp only [Category.id_comp]
    refine hCancel.trans ?_
    have hLgLf : LgBaseHom = LfHom := by
      dsimp [LgBaseHom, LfHom, Ig, If, stackificationLiftPulledToObjectCover,
        stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
    rw [hLgLf]
    let IbaseF : (stackificationLiftObjectCover (J := J) G hG y).Arrow := If.base
    let IbaseGf : (stackificationLiftObjectCover (J := J) G hG y).Arrow := I.base
    let qbase : I.Y ⟶ U := (I.f ≫ g) ≫ f
    have hfBaseF : (𝟙 I.Y) ≫ IbaseF.f = qbase := by
      dsimp [IbaseF, qbase, If, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base]
      simp only [Category.id_comp]
    have hfBaseGf : (𝟙 I.Y) ≫ IbaseGf.f = qbase := by
      dsimp [IbaseGf, qbase, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base]
      simp only [Category.id_comp, Category.assoc]
    let Tbase := stackificationLiftObjectTransition X G hG F y
      (stackificationLiftObjectCover (J := J) G hG y)
      (stackificationLiftObjectModel (J := J) G hG y)
      qbase (I₁ := IbaseF) (I₂ := IbaseGf) (𝟙 I.Y) (𝟙 I.Y)
      hfBaseF hfBaseGf
    let midBaseF := (FibredCategoryMor.fiberFunctor F I.Y).obj
      (stackificationLiftObjectModel (J := J) G hG y IbaseF).1
    let midBaseGf := (FibredCategoryMor.fiberFunctor F I.Y).obj
      (stackificationLiftObjectModel (J := J) G hG y IbaseGf).1
    let idBaseF :=
      ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app midBaseF
    let idBaseGf :=
      ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app midBaseGf
    have hInvTail :
        idBaseF ≫ Tbase ≫ idBaseGf ≫ LgfBaseInv =
          LfBaseInv ≫ κXfIf.hom ≫ κXfIg.inv := by
      let Fp := canonicalFiberPseudofunctor X.p
      let loc := LocallyDiscrete.mk (op I.Y)
      let z := stackificationLiftObjectGlued X G hG F y
      let Dhom :=
        (((Fp.toDescentData
          (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)).obj
            z).hom (q := qbase) (i₁ := IbaseF) (i₂ := IbaseGf)
              (f₁ := 𝟙 I.Y) (f₂ := 𝟙 I.Y) hfBaseF hfBaseGf)
      let targetF := ((Fp.map IbaseF.f.op.toLoc).toFunctor.obj z)
      let targetGf := ((Fp.map IbaseGf.f.op.toLoc).toFunctor.obj z)
      let idTargetF := (Fp.mapId loc).inv.toNatTrans.app targetF
      let idTargetGf := (Fp.mapId loc).hom.toNatTrans.app targetGf
      have hDesc :
          idTargetF ≫ Dhom ≫ idTargetGf = κXfIf.hom ≫ κXfIg.inv := by
        dsimp [idTargetF, idTargetGf, Dhom, targetF, targetGf, Fp, loc, z,
          IbaseF, IbaseGf, qbase, κXfIf, κXfIg, mapCompAppIso, If]
        exact Pseudofunctor.mapComp_id_assoc_tail_app
          (canonicalFiberPseudofunctor X.p) f g I.f
          (stackificationLiftObjectGlued X G hG F y)
      have hglued := stackificationLiftObjectGluedLocalIso_inv_comm
        X G hG F y qbase (I₁ := IbaseF) (I₂ := IbaseGf)
        (𝟙 I.Y) (𝟙 I.Y) hfBaseF hfBaseGf
      change
        ((Fp.map (𝟙 loc)).toFunctor.map LfBaseInv) ≫ Dhom =
          Tbase ≫ ((Fp.map (𝟙 loc)).toFunctor.map LgfBaseInv) at hglued
      have hright :
          ((Fp.map (𝟙 loc)).toFunctor.map LgfBaseInv) ≫ idTargetGf =
            idBaseGf ≫ LgfBaseInv := by
        dsimp only [idTargetGf, idBaseGf, Fp, loc, targetGf]
        simpa only [Functor.id_map] using
          ((canonicalFiberPseudofunctor X.p).mapId
            (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.naturality LgfBaseInv
      have hleft :
          idBaseF ≫ ((Fp.map (𝟙 loc)).toFunctor.map LfBaseInv) =
            LfBaseInv ≫ idTargetF := by
        dsimp only [idTargetF, idBaseF, Fp, loc, targetF]
        simpa only [Functor.id_map] using
          (((canonicalFiberPseudofunctor X.p).mapId
            (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.naturality LfBaseInv).symm
      have hleftTail :
          idBaseF ≫ (((Fp.map (𝟙 loc)).toFunctor.map LfBaseInv ≫ Dhom) ≫
              idTargetGf) =
            (LfBaseInv ≫ idTargetF) ≫ Dhom ≫ idTargetGf := by
        calc
          idBaseF ≫ (((Fp.map (𝟙 loc)).toFunctor.map LfBaseInv ≫ Dhom) ≫
              idTargetGf) =
            idBaseF ≫ ((Fp.map (𝟙 loc)).toFunctor.map LfBaseInv) ≫ Dhom ≫
              idTargetGf := by
              simp only [Category.assoc]
          _ = (LfBaseInv ≫ idTargetF) ≫ Dhom ≫ idTargetGf := by
              exact (reassoc_of% hleft) (Dhom ≫ idTargetGf)
      simp only [Category.assoc]
      slice_lhs 3 4 => exact hright.symm
      slice_lhs 2 3 => exact (reassoc_of% hglued.symm) idTargetGf
      slice_lhs 1 2 => exact hleftTail
      slice_lhs 2 4 => exact hDesc
      rfl
    have hModel :
        PgInv' ≫ Hmid ≫ PgfHom =
          PfHom ≫ idBaseF ≫ Tbase ≫ idBaseGf := by
      exact stackificationLiftPulledModelComparisonIso_comp_cocycle X G hG F g f y I
    calc
      LfHom ≫ PgInv' ≫ Hmid ≫ PgfHom ≫ LgfBaseInv =
          LfHom ≫ (PgInv' ≫ Hmid ≫ PgfHom) ≫ LgfBaseInv := by
        simp only [Category.assoc]
      _ = LfHom ≫ (PfHom ≫ idBaseF ≫ Tbase ≫ idBaseGf) ≫ LgfBaseInv := by
        exact congrArg (fun t => LfHom ≫ t ≫ LgfBaseInv) hModel
      _ = LfHom ≫ PfHom ≫
          (idBaseF ≫ Tbase ≫ idBaseGf ≫ LgfBaseInv) := by
        simp only [Category.assoc]
      _ = LfHom ≫ PfHom ≫ (LfBaseInv ≫ κXfIf.hom ≫ κXfIg.inv) := by
        exact congrArg (fun t => LfHom ≫ PfHom ≫ t) hInvTail
      _ = LfHom ≫ PfHom ≫ LfBaseInv ≫ κXfIf.hom ≫ κXfIg.inv := by
        simp only [Category.assoc]
  refine hLtail.trans ?_
  calc
    (κXgI.inv ≫ LgBaseHom ≫ PgInv' ≫ LggInv) ≫ Vloc ≫
        LgfHom ≫ PgfHom ≫ LgfBaseInv ≫ κXgfI.hom =
      κXgI.inv ≫ (LgBaseHom ≫ PgInv' ≫ LggInv ≫ Vloc ≫
        LgfHom ≫ PgfHom ≫ LgfBaseInv) ≫ κXgfI.hom := by
        simp only [Category.assoc]
    _ =
      κXgI.inv ≫ (LfHom ≫ PfHom ≫ LfBaseInv ≫ κXfIf.hom ≫
        κXfIg.inv) ≫ κXgfI.hom := by
        exact congrArg (fun t => κXgI.inv ≫ t ≫ κXgfI.hom) hCore
    _ = κXgI.inv ≫ LfHom ≫ PfHom ≫ LfBaseInv ≫ κXfIf.hom ≫
        κXfIg.inv ≫ κXgfI.hom := by
        simp only [Category.assoc]
    _ = κXgI.inv ≫ (LfHom ≫ PfHom ≫ LfBaseInv ≫ κXfIf.hom) ≫
        κXfIg.inv ≫ κXgfI.hom := by
        simp only [Category.assoc]
    _ = κXgI.inv ≫ ((LfHom ≫ PfHom ≫ idf) ≫ PGfInv) ≫
        κXfIg.inv ≫ κXgfI.hom := by
        exact hRtail.symm
    _ = κXgI.inv ≫
        ((stackificationLiftObjectGluedLocalIso X G hG F
              (f ^*[canonicalPullbackChoice S'.p] y)
              (stackificationLiftPulledToObjectCover (J := J) G hG f y If)).hom ≫
          (stackificationLiftPulledModelComparisonIso X G hG F f y If).hom ≫
            ((canonicalFiberPseudofunctor X.p).mapId
              (LocallyDiscrete.mk (op If.Y))).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor F If.Y).obj
                (stackificationLiftPulledObjectCoverModel (J := J) G hG f y If).1)) ≫
          (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).inv.hom If ≫
        κXfIg.inv ≫ κXgfI.hom := by
        dsimp only [LfHom, PfHom, idf, PGfInv]
        simp only [Category.assoc]

end

end CategoryTheory
