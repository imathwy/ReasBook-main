import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.SourceComparisonLocal
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.VerticalNaturality
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.MapCompCocycle

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the object pullback comparison is compatible with the
source-image glued identification for objects in the image of the stackification morphism. -/
theorem stackificationLiftObjectSourceImage_pullback_compatibility
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (x : S.p.Fiber U) :
    (stackificationLiftObjectPullbackComparison X G hG F f
        ((FibredCategoryMor.fiberFunctor G U).obj x)).inv ≫
      stackificationLiftVerticalMap X G hG F
        (FibredCategoryMor.pullbackComparison G f x).hom ≫
      (stackificationLiftObjectSourceImageGluedIso X G hG F
        (f ^*[canonicalPullbackChoice S.p] x)).hom =
    ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom ≫
      (FibredCategoryMor.pullbackComparison F f x).hom := by
  apply stack_cover_hom_ext (J := J) X
    (stackificationLiftPulledObjectCover (J := J) G hG f
      ((FibredCategoryMor.fiberFunctor G U).obj x))
  intro I
  let M := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
  change M.map
      ((stackificationLiftObjectPullbackComparison X G hG F f
          ((FibredCategoryMor.fiberFunctor G U).obj x)).inv ≫
        stackificationLiftVerticalMap X G hG F
          (FibredCategoryMor.pullbackComparison G f x).hom ≫
        (stackificationLiftObjectSourceImageGluedIso X G hG F
          (f ^*[canonicalPullbackChoice S.p] x)).hom) =
    M.map (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom ≫
      (FibredCategoryMor.pullbackComparison F f x).hom)
  rw [M.map_comp]
  rw [M.map_comp]
  rw [M.map_comp]
  rw [stackificationLiftObjectPullbackComparison_local_inv X G hG F f
      ((FibredCategoryMor.fiberFunctor G U).obj x) I]
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let z : S'.p.Fiber V := f ^*[canonicalPullbackChoice S'.p] y
  let xz : S.p.Fiber V := f ^*[canonicalPullbackChoice S.p] x
  let d : z ⟶ (FibredCategoryMor.fiberFunctor G V).obj xz :=
    (FibredCategoryMor.pullbackComparison G f x).hom
  let Iz : (stackificationLiftObjectCover (J := J) G hG z).Arrow :=
    stackificationLiftPulledToObjectCover (J := J) G hG f y I
  let xp : S.p.Fiber I.Y :=
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
  let ep :=
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).2
  let Md := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d
  let Iright : (stackificationLiftObjectCover (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G V).obj xz)).Arrow :=
    ⟨I.Y, I.f, by
      refine ⟨xp, ?_⟩
      refine ⟨ep ≪≫ ?_⟩
      simpa [y, z, xz] using
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.mapIso
          (FibredCategoryMor.pullbackComparison G f x)⟩
  let Iv : (stackificationLiftVerticalCommonCover (J := J) G hG z
      ((FibredCategoryMor.fiberFunctor G V).obj xz)).Arrow :=
    ⟨I.Y, I.f, by
      exact ⟨Iz.hf, Iright.hf⟩⟩
  have hIv_left :
      stackificationLiftVerticalCommonCover_left (J := J) G hG z
        ((FibredCategoryMor.fiberFunctor G V).obj xz) Iv = Iz := by
    ext <;> rfl
  have hIv_right :
      stackificationLiftVerticalCommonCover_right (J := J) G hG z
        ((FibredCategoryMor.fiberFunctor G V).obj xz) Iv = Iright := by
    ext <;> rfl
  have hVert :
      M.map (stackificationLiftVerticalMap X G hG F d) =
        stackificationLiftVerticalLocalMap X G hG F d Iv := by
    dsimp only [M]
    exact stackificationLiftVerticalMap_local X G hG F d Iv
  rw [hVert]
  have hTargetSource :
      M.map (stackificationLiftObjectSourceImageGluedIso X G hG F xz).hom =
        (stackificationLiftObjectGluedLocalIso X G hG F
          ((FibredCategoryMor.fiberFunctor G V).obj xz) Iright).hom ≫
          (stackificationLiftObjectSourceImageLocalIso X G hG F xz Iright).inv := by
    simpa [M, xz] using
      stackificationLiftObjectSourceImageGluedIso_local_hom X G hG F xz Iright
  rw [hTargetSource]
  let xLeft :=
    (stackificationLiftObjectModel (J := J) G hG z Iz).1
  let xRight :=
    (stackificationLiftObjectModel (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G V).obj xz) Iright).1
  let cLeft :=
    (stackificationLiftObjectModel (J := J) G hG z Iz).2
  let cRight :=
    (stackificationLiftObjectModel (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G V).obj xz) Iright).2
  let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj xLeft) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xRight) :=
    cLeft.hom ≫ Md ≫ cRight.inv
  let H := stackificationLiftHomExtensionFiberMap X G hG F xLeft xRight α
  have hVerticalLocal :
      stackificationLiftVerticalLocalMap X G hG F d Iv =
        (stackificationLiftObjectGluedLocalIso X G hG F z Iz).hom ≫
          H ≫
          (stackificationLiftObjectGluedLocalIso X G hG F
            ((FibredCategoryMor.fiberFunctor G V).obj xz) Iright).inv := by
    dsimp [stackificationLiftVerticalLocalMap]
    cases hIv_left
    cases hIv_right
    rfl
  rw [hVerticalLocal]
  have hDescInv :
      (stackificationLiftPulledObjectDescentComparison X G hG F f y).inv.hom I =
        (stackificationLiftPulledLocalIso X G hG F f y I).inv := by
    rfl
  rw [hDescInv]
  rw [stackificationLiftPulledLocalIso_inv]
  let K := ((canonicalFiberPseudofunctor X.p).map (I.f ≫ f).op.toLoc).toFunctor
  let Ibase : (stackificationLiftObjectCover (J := J) G hG y).Arrow :=
    I.base
  let κGlued :=
    mapCompAppIso X.p f I.f (I.f ≫ f)
      (FibredCategoryMor.comp_toLoc_eq f I.f (I.f ≫ f) rfl)
      (stackificationLiftObjectGlued X G hG F y)
  let κF :=
    mapCompAppIso X.p f I.f (I.f ≫ f)
      (FibredCategoryMor.comp_toLoc_eq f I.f (I.f ≫ f) rfl)
      ((FibredCategoryMor.fiberFunctor F U).obj x)
  have hMapMap :
      M.map (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom) =
        κGlued.inv ≫
          K.map (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom ≫
          κF.hom := by
    simpa [M, K, κGlued, κF] using
      mapCompAppIso_inv_comp_map_map_hom X.p f I.f
        (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom
  rw [hMapMap]
  have hSourceBase :
      K.map (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom =
        (stackificationLiftObjectGluedLocalIso X G hG F y Ibase).hom ≫
          (stackificationLiftObjectSourceImageLocalIso X G hG F x Ibase).inv := by
    simpa [K, y, Ibase] using
      stackificationLiftObjectSourceImageGluedIso_local_hom X G hG F x Ibase
  rw [hSourceBase]
  let mid := (FibredCategoryMor.fiberFunctor F I.Y).obj
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
  let idHom :=
    ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
      (LocallyDiscrete.mk (op I.Y)))).app mid).hom
  have hPulledGluedSource :
      (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫ idHom =
        κGlued.inv ≫
          (stackificationLiftObjectGluedLocalIso X G hG F y Ibase).hom := by
    dsimp only [idHom, mid]
    simp only [stackificationLiftPulledGluedObjectDescentIso,
      stackificationLiftPulledObjectDescentData,
      stackificationLiftPulledObjectDescentPullFunctor,
      Pseudofunctor.DescentData.pullFunctor,
      Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
      Pseudofunctor.isoMapOfCommSq_eq,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Pseudofunctor.DescentData.comp_hom,
      Category.assoc]
    dsimp [κGlued, K, y, stackificationLiftPulledObjectCover,
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
      simpa [Fp, e, y, stackificationLiftPulledObjectCover,
        Ibase] using
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
      simpa [Fp, e, y, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base, Category.assoc] using hid
    have hcalc : ((A ≫ compHom) ≫ mapE) ≫ idHom' = A ≫ e := by
      calc
        ((A ≫ compHom) ≫ mapE) ≫ idHom' =
          A ≫ (compHom ≫ mapE ≫ idHom') := by
            simp only [Category.assoc]
        _ = A ≫ e := by
            exact congrArg (fun t => A ≫ t) htail
    have hcalc2 : ((A ≫ compHom) ≫ mapE) ≫ idHom' = A ≫ e := by
      exact hcalc
    have hAκ : A ≫ e = Aκ ≫ e := by
      dsimp [A, Aκ]
    have hcalc3 : ((A ≫ compHom) ≫ mapE) ≫ idHom' = Aκ ≫ e :=
      hcalc2.trans hAκ
    have hcalc4 : (A ≫ compHom) ≫ (mapE ≫ idHom') = Aκ ≫ e := by
      simpa only [Category.assoc] using hcalc3
    dsimp only [A, Aκ, compHom, mapE, idHom', e, κGlued, mapCompAppIso,
      stackificationLiftObjectGluedLocalIso] at hcalc4 ⊢
    dsimp only [Fp, y, Ibase, stackificationLiftPulledObjectCover,
      GrothendieckTopology.Cover.Arrow.base] at hcalc4 ⊢
    exact hcalc4
  let Lbase := stackificationLiftObjectGluedLocalIso X G hG F y Ibase
  let sxbase := stackificationLiftObjectSourceImageLocalIso X G hG F x Ibase
  let P := stackificationLiftPulledModelComparisonIso X G hG F f y I
  let Lz := stackificationLiftObjectGluedLocalIso X G hG F z Iz
  let Lright := stackificationLiftObjectGluedLocalIso X G hG F
    ((FibredCategoryMor.fiberFunctor G V).obj xz) Iright
  let sxright := stackificationLiftObjectSourceImageLocalIso X G hG F xz Iright
  let cFf := FibredCategoryMor.pullbackComparison F f x
  have hCoreHom :
      sxbase.hom ≫ P.inv ≫ H =
        κF.hom ≫ M.map cFf.hom ≫ sxright.hom := by
    let q : I.Y ⟶ U := I.f ≫ f
    let κS :=
      mapCompAppIso S.p f I.f q
        (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) x
    let κG :=
      mapCompAppIso S'.p f I.f q
        (FibredCategoryMor.comp_toLoc_eq f I.f q rfl) y
    let cFq := FibredCategoryMor.pullbackComparison F q x
    let cGq := FibredCategoryMor.pullbackComparison G q x
    let cGI := FibredCategoryMor.pullbackComparison G I.f xz
    let cFI := FibredCategoryMor.pullbackComparison F I.f xz
    let cGf := FibredCategoryMor.pullbackComparison G f x
    let MG := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor
    have hFcomp :
        κF.hom ≫ M.map cFf.hom ≫ cFI.hom =
          cFq.hom ≫ (FibredCategoryMor.fiberFunctor F I.Y).map κS.hom := by
      dsimp only [κF, M, cFf, cFI, cFq, κS, q, xz, mapCompAppIso]
      exact pullbackComparison_mapComp_hom_cocycle F f I.f (I.f ≫ f) rfl x
    have hGcomp :
        cGq.inv ≫ κG.hom ≫ MG.map cGf.hom =
          (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫ cGI.inv := by
      have hGh :
          κG.hom ≫ MG.map cGf.hom ≫ cGI.hom =
            cGq.hom ≫ (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom := by
        dsimp only [κG, MG, cGf, cGI, cGq, κS, q, xz, mapCompAppIso]
        exact pullbackComparison_mapComp_hom_cocycle G f I.f (I.f ≫ f) rfl x
      have hGh' :
          cGq.inv ≫ κG.hom ≫ MG.map cGf.hom ≫ cGI.hom =
            (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom := by
        calc
          cGq.inv ≫ κG.hom ≫ MG.map cGf.hom ≫ cGI.hom =
              cGq.inv ≫ (κG.hom ≫ MG.map cGf.hom ≫ cGI.hom) := by
                simp only [Category.assoc]
          _ = cGq.inv ≫
              (cGq.hom ≫ (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom) := by
                rw [hGh]
          _ = (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom := by
                rw [← Category.assoc, cGq.inv_hom_id]
                simp only [Category.id_comp]
      calc
        cGq.inv ≫ κG.hom ≫ MG.map cGf.hom =
            (cGq.inv ≫ κG.hom ≫ MG.map cGf.hom) ≫ 𝟙 _ := by
              simp only [Category.comp_id]
        _ = (cGq.inv ≫ κG.hom ≫ MG.map cGf.hom) ≫ (cGI.hom ≫ cGI.inv) := by
              exact congrArg
                (fun t => (cGq.inv ≫ κG.hom ≫ MG.map cGf.hom) ≫ t)
                cGI.hom_inv_id.symm
        _ = (cGq.inv ≫ κG.hom ≫ MG.map cGf.hom ≫ cGI.hom) ≫ cGI.inv := by
              simp only [Category.assoc]
        _ = (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫ cGI.inv := by
              rw [hGh']
    let αbase :=
      (FibredCategoryMor.pullbackComparison G Ibase.f x).inv ≫
        (stackificationLiftObjectModel (J := J) G hG y Ibase).2.inv
    let βbase :=
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).2.hom ≫
        (stackificationLiftObjectModel (J := J) G hG z Iz).2.inv
    have hCompBasePulled :
        stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x)
            (stackificationLiftObjectModel (J := J) G hG y Ibase).1 αbase ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
            xLeft βbase =
          stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xLeft
            (αbase ≫ βbase) := by
      exact (stackificationLiftHomExtensionFiberMap_comp X G hG F αbase βbase).symm
    have hCompLeftAll :
        stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xLeft
            (αbase ≫ βbase) ≫
          stackificationLiftHomExtensionFiberMap X G hG F xLeft xRight α =
        stackificationLiftHomExtensionFiberMap X G hG F
          (Ibase.f ^*[canonicalPullbackChoice S.p] x) xRight
          ((αbase ≫ βbase) ≫ α) := by
      exact (stackificationLiftHomExtensionFiberMap_comp X G hG F (αbase ≫ βbase) α).symm
    have hα_all :
        (αbase ≫ βbase) ≫ α =
          (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫
            cGI.inv ≫ cRight.inv := by
      have hGtail := congrArg (fun t => t ≫ cRight.inv) hGcomp
      dsimp only [αbase, βbase, α, Ibase, stackificationLiftPulledObjectCoverModel]
      simp only [Iso.trans_hom, Category.assoc]
      let cybase := (stackificationLiftObjectModel (J := J) G hG y Ibase).2
      change cGq.inv ≫ cybase.inv ≫
          ((cybase.hom ≫ κG.hom ≫ cLeft.inv) ≫ cLeft.hom ≫
            MG.map cGf.hom ≫ cRight.inv) =
        (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫ cGI.inv ≫
          cRight.inv
      calc
        cGq.inv ≫ cybase.inv ≫
            ((cybase.hom ≫ κG.hom ≫ cLeft.inv) ≫ cLeft.hom ≫
              MG.map cGf.hom ≫ cRight.inv) =
          cGq.inv ≫ (cybase.inv ≫ cybase.hom) ≫ κG.hom ≫
            cLeft.inv ≫ cLeft.hom ≫ MG.map cGf.hom ≫ cRight.inv := by
            simp only [Category.assoc]
        _ =
          cGq.inv ≫ 𝟙 _ ≫ κG.hom ≫ cLeft.inv ≫ cLeft.hom ≫
            MG.map cGf.hom ≫ cRight.inv := by
            have hcy := congrArg
              (fun t => cGq.inv ≫ t ≫ κG.hom ≫ cLeft.inv ≫
                cLeft.hom ≫ MG.map cGf.hom ≫ cRight.inv)
              cybase.inv_hom_id
            exact hcy
        _ =
          cGq.inv ≫ κG.hom ≫ (cLeft.inv ≫ cLeft.hom) ≫
            MG.map cGf.hom ≫ cRight.inv := by
            simp only [Category.id_comp, Category.comp_id, Category.assoc]
        _ =
          cGq.inv ≫ κG.hom ≫
            𝟙 (Iz.f ^*[canonicalPullbackChoice S'.p] z) ≫
              MG.map cGf.hom ≫ cRight.inv := by
            have hc := congrArg
              (fun t => cGq.inv ≫ κG.hom ≫ t ≫ MG.map cGf.hom ≫ cRight.inv)
              cLeft.inv_hom_id
            exact hc
        _ =
          cGq.inv ≫ κG.hom ≫ MG.map cGf.hom ≫ cRight.inv := by
            dsimp only [Iz, z, stackificationLiftPulledToObjectCover]
            change cGq.inv ≫ κG.hom ≫ 𝟙 (MG.obj z) ≫
                MG.map cGf.hom ≫ cRight.inv =
              cGq.inv ≫ κG.hom ≫ MG.map cGf.hom ≫ cRight.inv
            slice_lhs 2 3 =>
              exact Category.comp_id κG.hom
            simp only [Category.assoc]
            rfl
        _ =
          (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫ cGI.inv ≫
            cRight.inv := by
            calc
              cGq.inv ≫ κG.hom ≫ MG.map cGf.hom ≫ cRight.inv =
                  (cGq.inv ≫ κG.hom ≫ MG.map cGf.hom) ≫ cRight.inv := by
                    simp only [Category.assoc]
              _ = ((FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫
                    cGI.inv) ≫ cRight.inv := by
                    exact hGtail
              _ = (FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫
                    cGI.inv ≫ cRight.inv := by
                    simp only [Category.assoc]
    have hBasePulledAll :
        stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x)
            (stackificationLiftObjectModel (J := J) G hG y Ibase).1 αbase ≫
          (stackificationLiftHomExtensionFiberMap X G hG F
              (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
              xLeft βbase ≫ H) =
          stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xLeft
            (αbase ≫ βbase) ≫ H := by
      calc
        stackificationLiftHomExtensionFiberMap X G hG F
              (Ibase.f ^*[canonicalPullbackChoice S.p] x)
              (stackificationLiftObjectModel (J := J) G hG y Ibase).1 αbase ≫
            (stackificationLiftHomExtensionFiberMap X G hG F
                (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
                xLeft βbase ≫ H) =
          (stackificationLiftHomExtensionFiberMap X G hG F
              (Ibase.f ^*[canonicalPullbackChoice S.p] x)
              (stackificationLiftObjectModel (J := J) G hG y Ibase).1 αbase ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
              xLeft βbase) ≫ H := by
            rw [Category.assoc]
        _ =
          stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xLeft
            (αbase ≫ βbase) ≫ H := by
            exact congrArg (fun t => t ≫ H) hCompBasePulled
    dsimp only [sxbase, P, H, sxright, cFf]
    dsimp only [stackificationLiftObjectSourceImageLocalIso]
    rw [stackificationLiftPulledModelComparisonIso_inv]
    simp only [Category.assoc]
    dsimp only [αbase, βbase, xLeft, y, z, xz, Ibase, Iz, Iright, stackificationLiftPulledObjectCoverModel,
      stackificationLiftPulledToObjectCover, GrothendieckTopology.Cover.Arrow.base] at *
    slice_lhs 2 4 =>
      exact hBasePulledAll
    have hLeftAllPref := congrArg
      (fun t => (FibredCategoryMor.pullbackComparison F (I.f ≫ f) x).hom ≫ t)
      hCompLeftAll
    dsimp only [q, cFq] at hLeftAllPref
    refine hLeftAllPref.trans ?_
    let T := stackificationLiftHomExtensionFiberMap X G hG F
      (I.f ^*[canonicalPullbackChoice S.p] xz) xRight
      (cGI.inv ≫ cRight.inv)
    have hTransport :
        stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xRight
            ((FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫
              cGI.inv ≫ cRight.inv) =
          (FibredCategoryMor.fiberFunctor F I.Y).map κS.hom ≫ T := by
      have h :=
        stackificationLiftHomExtensionFiberMap_transport_of_sourceIso X G hG F
          κS (Iso.refl xRight) (cGI.inv ≫ cRight.inv)
      dsimp only [T]
      simpa only [q, Ibase, Iso.refl_inv, Functor.map_id, Category.comp_id,
        Category.assoc] using h
    have hAll :
        stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xRight
            ((αbase ≫ βbase) ≫ α) =
          (FibredCategoryMor.fiberFunctor F I.Y).map κS.hom ≫ T := by
      calc
        stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xRight
            ((αbase ≫ βbase) ≫ α) =
          stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xRight
            ((FibredCategoryMor.fiberFunctor G I.Y).map κS.hom ≫
              cGI.inv ≫ cRight.inv) := by
            exact congrArg
              (stackificationLiftHomExtensionFiberMap X G hG F
                (Ibase.f ^*[canonicalPullbackChoice S.p] x) xRight)
              hα_all
        _ = (FibredCategoryMor.fiberFunctor F I.Y).map κS.hom ≫ T :=
            hTransport
    calc
      (FibredCategoryMor.pullbackComparison F (I.f ≫ f) x).hom ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            (Ibase.f ^*[canonicalPullbackChoice S.p] x) xRight
            ((αbase ≫ βbase) ≫ α) =
        (FibredCategoryMor.pullbackComparison F (I.f ≫ f) x).hom ≫
          ((FibredCategoryMor.fiberFunctor F I.Y).map κS.hom ≫ T) := by
          exact congrArg
            (fun t => (FibredCategoryMor.pullbackComparison F (I.f ≫ f) x).hom ≫ t)
            hAll
      _ =
        ((FibredCategoryMor.pullbackComparison F (I.f ≫ f) x).hom ≫
          (FibredCategoryMor.fiberFunctor F I.Y).map κS.hom) ≫ T := by
          simp only [Category.assoc]
      _ = (κF.hom ≫ M.map cFf.hom ≫ cFI.hom) ≫ T := by
          rw [← hFcomp]
      _ = κF.hom ≫ M.map cFf.hom ≫ cFI.hom ≫ T := by
          simp only [Category.assoc]
  have hCoreCancel :
      P.inv ≫ H ≫ sxright.inv =
        sxbase.inv ≫ κF.hom ≫ M.map cFf.hom := by
    calc
      P.inv ≫ H ≫ sxright.inv =
        sxbase.inv ≫ sxbase.hom ≫ P.inv ≫ H ≫ sxright.inv := by
          exact (sxbase.inv_hom_id_assoc (P.inv ≫ H ≫ sxright.inv)).symm
      _ = sxbase.inv ≫ (sxbase.hom ≫ P.inv ≫ H) ≫ sxright.inv := by
          simp only [Category.assoc]
      _ = sxbase.inv ≫ (κF.hom ≫ M.map cFf.hom ≫ sxright.hom) ≫
          sxright.inv := by
          rw [hCoreHom]
          rfl
      _ = sxbase.inv ≫ κF.hom ≫ M.map cFf.hom := by
          calc
            sxbase.inv ≫ (κF.hom ≫ M.map cFf.hom ≫ sxright.hom) ≫
                sxright.inv =
              sxbase.inv ≫ κF.hom ≫ M.map cFf.hom ≫
                (sxright.hom ≫ sxright.inv) := by
                simp only [Category.assoc]
            _ = sxbase.inv ≫ κF.hom ≫ M.map cFf.hom ≫ 𝟙 _ := by
                simpa only [Category.assoc] using congrArg
                  (fun t => sxbase.inv ≫ κF.hom ≫ M.map cFf.hom ≫ t)
                  sxright.hom_inv_id
            _ = sxbase.inv ≫ κF.hom ≫ M.map cFf.hom := by
                simp only [Category.comp_id]
  change
    (((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
          idHom ≫ P.inv ≫ Lz.inv) ≫
        (Lz.hom ≫ H ≫ Lright.inv) ≫ Lright.hom ≫ sxright.inv) =
      (κGlued.inv ≫ (Lbase.hom ≫ sxbase.inv) ≫ κF.hom) ≫
        M.map cFf.hom
  calc
    (((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
          idHom ≫ P.inv ≫ Lz.inv) ≫
        (Lz.hom ≫ H ≫ Lright.inv) ≫ Lright.hom ≫ sxright.inv) =
      ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
          idHom) ≫ P.inv ≫ H ≫ sxright.inv := by
        calc
          (((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
                idHom ≫ P.inv ≫ Lz.inv) ≫
              (Lz.hom ≫ H ≫ Lright.inv) ≫ Lright.hom ≫ sxright.inv) =
            ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
                idHom) ≫ P.inv ≫ (Lz.inv ≫ Lz.hom) ≫
              H ≫ (Lright.inv ≫ Lright.hom) ≫ sxright.inv := by
              simp only [Category.assoc]
          _ =
            ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
                idHom) ≫ P.inv ≫ 𝟙 _ ≫ H ≫
              (Lright.inv ≫ Lright.hom) ≫ sxright.inv := by
              exact congrArg
                (fun t =>
                  ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
                    idHom) ≫ P.inv ≫ t ≫ H ≫
                  (Lright.inv ≫ Lright.hom) ≫ sxright.inv)
                Lz.inv_hom_id
          _ =
            ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
                idHom) ≫ P.inv ≫ 𝟙 _ ≫ H ≫ 𝟙 _ ≫ sxright.inv := by
              exact congrArg
                (fun t =>
                  ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
                    idHom) ≫ P.inv ≫ 𝟙 _ ≫ H ≫ t ≫ sxright.inv)
                Lright.inv_hom_id
          _ =
            ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
                idHom) ≫ P.inv ≫ H ≫ sxright.inv := by
              simp only [Category.id_comp, Category.comp_id, Category.assoc]
    _ = (κGlued.inv ≫ Lbase.hom) ≫ P.inv ≫ H ≫ sxright.inv := by
        dsimp only [Lbase]
        exact congrArg (fun t => t ≫ P.inv ≫ H ≫ sxright.inv)
          hPulledGluedSource
    _ = (κGlued.inv ≫ Lbase.hom) ≫
          (sxbase.inv ≫ κF.hom ≫ M.map cFf.hom) := by
        calc
          (κGlued.inv ≫ Lbase.hom) ≫ P.inv ≫ H ≫ sxright.inv =
            (κGlued.inv ≫ Lbase.hom) ≫ (P.inv ≫ H ≫ sxright.inv) := by
              simp only [Category.assoc]
          _ = (κGlued.inv ≫ Lbase.hom) ≫
              (sxbase.inv ≫ κF.hom ≫ M.map cFf.hom) := by
              exact congrArg (fun t => (κGlued.inv ≫ Lbase.hom) ≫ t)
                hCoreCancel
    _ = (κGlued.inv ≫ (Lbase.hom ≫ sxbase.inv) ≫ κF.hom) ≫
          M.map cFf.hom := by
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 3: the pullback/source-image compatibility, rewritten with the
inverse pullback-comparison map on the source side. -/
theorem stackificationLiftObjectSourceImage_pullback_compatibility_inv
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (x : S.p.Fiber U) :
    stackificationLiftVerticalMap X G hG F
        (FibredCategoryMor.pullbackComparison G f x).inv ≫
      (stackificationLiftObjectPullbackComparison X G hG F f
        ((FibredCategoryMor.fiberFunctor G U).obj x)).hom ≫
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom =
    (stackificationLiftObjectSourceImageGluedIso X G hG F
        (f ^*[canonicalPullbackChoice S.p] x)).hom ≫
      (FibredCategoryMor.pullbackComparison F f x).inv := by
  let cG := FibredCategoryMor.pullbackComparison G f x
  let cF := FibredCategoryMor.pullbackComparison F f x
  let P := stackificationLiftObjectPullbackComparison X G hG F f
    ((FibredCategoryMor.fiberFunctor G U).obj x)
  let sx := stackificationLiftObjectSourceImageGluedIso X G hG F x
  let sxp := stackificationLiftObjectSourceImageGluedIso X G hG F
    (f ^*[canonicalPullbackChoice S.p] x)
  let M := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  have h :=
    stackificationLiftObjectSourceImage_pullback_compatibility X G hG F f x
  have hpre :
      stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom =
        P.hom ≫ M.map sx.hom ≫ cF.hom := by
    calc
      stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom =
          P.hom ≫ (P.inv ≫
            stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom) := by
          calc
            stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom =
                𝟙 _ ≫ (stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom) := by
                simp only [Category.id_comp]
            _ = (P.hom ≫ P.inv) ≫
                (stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom) := by
                rw [P.hom_inv_id]
            _ = P.hom ≫ (P.inv ≫
                stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom) := by
                simp only [Category.assoc]
      _ = P.hom ≫ (M.map sx.hom ≫ cF.hom) := by
          exact congrArg (fun t => P.hom ≫ t) h
      _ = P.hom ≫ M.map sx.hom ≫ cF.hom := by
          rfl
  have hcancel :
      stackificationLiftVerticalMap X G hG F cG.inv ≫
        stackificationLiftVerticalMap X G hG F cG.hom =
      𝟙 _ := by
    calc
      stackificationLiftVerticalMap X G hG F cG.inv ≫
          stackificationLiftVerticalMap X G hG F cG.hom =
        stackificationLiftVerticalMap X G hG F (cG.inv ≫ cG.hom) := by
          exact (stackificationLiftVerticalMap_comp X G hG F cG.inv cG.hom).symm
      _ = stackificationLiftVerticalMap X G hG F (𝟙 _) := by
          rw [cG.inv_hom_id]
      _ = 𝟙 _ := by
          exact stackificationLiftVerticalMap_id X G hG F _
  calc
    stackificationLiftVerticalMap X G hG F cG.inv ≫ P.hom ≫ M.map sx.hom =
        (stackificationLiftVerticalMap X G hG F cG.inv ≫ P.hom ≫ M.map sx.hom ≫
          cF.hom) ≫ cF.inv := by
        calc
          stackificationLiftVerticalMap X G hG F cG.inv ≫ P.hom ≫ M.map sx.hom =
              (stackificationLiftVerticalMap X G hG F cG.inv ≫ P.hom ≫ M.map sx.hom) ≫
                𝟙 _ := by
                simp only [Category.comp_id]
          _ = (stackificationLiftVerticalMap X G hG F cG.inv ≫ P.hom ≫ M.map sx.hom) ≫
                (cF.hom ≫ cF.inv) := by
                exact congrArg
                  (fun t =>
                    (stackificationLiftVerticalMap X G hG F cG.inv ≫ P.hom ≫
                      M.map sx.hom) ≫ t)
                  cF.hom_inv_id.symm
          _ = (stackificationLiftVerticalMap X G hG F cG.inv ≫ P.hom ≫ M.map sx.hom ≫
                cF.hom) ≫ cF.inv := by
                simp only [Category.assoc]
    _ = (stackificationLiftVerticalMap X G hG F cG.inv ≫
          stackificationLiftVerticalMap X G hG F cG.hom ≫ sxp.hom) ≫ cF.inv := by
        rw [hpre]
    _ = ((stackificationLiftVerticalMap X G hG F cG.inv ≫
          stackificationLiftVerticalMap X G hG F cG.hom) ≫ sxp.hom) ≫ cF.inv := by
        simp only [Category.assoc]
    _ = (𝟙 _ ≫ sxp.hom) ≫ cF.inv := by
        exact congrArg (fun t => (t ≫ sxp.hom) ≫ cF.inv) hcancel
    _ = sxp.hom ≫ cF.inv := by
        simp only [Category.id_comp]

/-- Helper for Chap08 Lemma 8 8 3: source-image naturality for a vertical source arrow followed
by the inverse source-side pullback comparison. This is the fiber-level core used for total
arrows after appending the chosen cartesian map. -/
theorem stackificationLiftObjectSourceImage_arrowCore_naturality
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) {x : S.p.Fiber V} (x' : S.p.Fiber U)
    (v : x ⟶ f ^*[canonicalPullbackChoice S.p] x') :
    stackificationLiftVerticalMap X G hG F
        ((FibredCategoryMor.fiberFunctor G V).map v ≫
          (FibredCategoryMor.pullbackComparison G f x').inv) ≫
      (stackificationLiftObjectPullbackComparison X G hG F f
        ((FibredCategoryMor.fiberFunctor G U).obj x')).hom ≫
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageGluedIso X G hG F x').hom =
    (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom ≫
      (FibredCategoryMor.fiberFunctor F V).map v ≫
      (FibredCategoryMor.pullbackComparison F f x').inv := by
  let cG := FibredCategoryMor.pullbackComparison G f x'
  let cF := FibredCategoryMor.pullbackComparison F f x'
  let P := stackificationLiftObjectPullbackComparison X G hG F f
    ((FibredCategoryMor.fiberFunctor G U).obj x')
  let sx := stackificationLiftObjectSourceImageGluedIso X G hG F x
  let sxp := stackificationLiftObjectSourceImageGluedIso X G hG F
    (f ^*[canonicalPullbackChoice S.p] x')
  let sx' := stackificationLiftObjectSourceImageGluedIso X G hG F x'
  let M := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  have hpull :=
    stackificationLiftObjectSourceImage_pullback_compatibility_inv X G hG F f x'
  have hvert :=
    stackificationLiftVerticalMap_sourceImage_naturality X G hG F v
  calc
    stackificationLiftVerticalMap X G hG F
          ((FibredCategoryMor.fiberFunctor G V).map v ≫ cG.inv) ≫
        P.hom ≫ M.map sx'.hom =
        (stackificationLiftVerticalMap X G hG F
            ((FibredCategoryMor.fiberFunctor G V).map v) ≫
          stackificationLiftVerticalMap X G hG F cG.inv) ≫
        P.hom ≫ M.map sx'.hom := by
        rw [stackificationLiftVerticalMap_comp]
    _ =
        stackificationLiftVerticalMap X G hG F
            ((FibredCategoryMor.fiberFunctor G V).map v) ≫
          (stackificationLiftVerticalMap X G hG F cG.inv ≫
            P.hom ≫ M.map sx'.hom) := by
        simp only [Category.assoc]
    _ =
        stackificationLiftVerticalMap X G hG F
            ((FibredCategoryMor.fiberFunctor G V).map v) ≫
          (sxp.hom ≫ cF.inv) := by
        exact congrArg
          (fun t =>
            stackificationLiftVerticalMap X G hG F
              ((FibredCategoryMor.fiberFunctor G V).map v) ≫ t)
          hpull
    _ =
        (stackificationLiftVerticalMap X G hG F
            ((FibredCategoryMor.fiberFunctor G V).map v) ≫ sxp.hom) ≫
          cF.inv := by
        simp only [Category.assoc]
    _ =
        (sx.hom ≫ (FibredCategoryMor.fiberFunctor F V).map v) ≫
          cF.inv := by
        exact congrArg (fun t => t ≫ cF.inv) hvert
    _ =
        sx.hom ≫ (FibredCategoryMor.fiberFunctor F V).map v ≫ cF.inv := by
        simp only [Category.assoc]

end
end CategoryTheory
