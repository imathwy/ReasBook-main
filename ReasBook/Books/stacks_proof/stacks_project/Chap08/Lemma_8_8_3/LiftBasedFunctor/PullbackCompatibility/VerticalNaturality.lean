import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The lift's object pullback comparison is natural for vertical maps. -/
theorem stackificationLiftObjectPullbackComparison_verticalMap
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U)
    {y₀ y₁ : S'.p.Fiber U} (d : y₀ ⟶ y₁) :
    stackificationLiftVerticalMap X G hG F
        (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) =
      (stackificationLiftObjectPullbackComparison X G hG F f y₀).hom ≫
        ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d) ≫
        (stackificationLiftObjectPullbackComparison X G hG F f y₁).inv := by
  apply stack_cover_hom_ext (J := J) X
    ((stackificationLiftVerticalCommonCover (J := J) G hG y₀ y₁).pullback f)
  intro I
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
  let Iv : (stackificationLiftVerticalCommonCover (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y₀)
      (f ^*[canonicalPullbackChoice S'.p] y₁)).Arrow :=
    ⟨I.Y, I.f, by
      exact ⟨(stackificationLiftPulledToObjectCover (J := J) G hG f y₀ I₀).hf,
        (stackificationLiftPulledToObjectCover (J := J) G hG f y₁ I₁).hf⟩⟩
  let Fp := canonicalFiberPseudofunctor X.p
  let M := ((Fp).map I.f.op.toLoc).toFunctor
  change M.map (stackificationLiftVerticalMap X G hG F
        (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d)) =
      M.map ((stackificationLiftObjectPullbackComparison X G hG F f y₀).hom ≫
        ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d) ≫
        (stackificationLiftObjectPullbackComparison X G hG F f y₁).inv)
  rw [M.map_comp]
  rw [M.map_comp]
  rw [stackificationLiftVerticalMap_local X G hG F
    (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) Iv]
  rw [stackificationLiftObjectPullbackComparison_local_hom X G hG F f y₀ I₀]
  have hInvM :
      M.map (stackificationLiftObjectPullbackComparison X G hG F f y₁).inv =
        (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₁).hom.hom I₁ ≫
          (stackificationLiftPulledObjectDescentComparison X G hG F f y₁).inv.hom I₁ := by
    simpa [M] using
      stackificationLiftObjectPullbackComparison_local_inv X G hG F f y₁ I₁
  let A₀ := (stackificationLiftPulledObjectDescentComparison X G hG F f y₀).hom.hom I₀
  let B₀ := (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₀).inv.hom I₀
  let MV := M.map (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
    (stackificationLiftVerticalMap X G hG F d))
  have hR :
      ((A₀ ≫ B₀) ≫ MV) ≫
          M.map (stackificationLiftObjectPullbackComparison X G hG F f y₁).inv =
        ((A₀ ≫ B₀) ≫ MV) ≫
          ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y₁).hom.hom I₁ ≫
            (stackificationLiftPulledObjectDescentComparison X G hG F f y₁).inv.hom I₁) := by
    exact congrArg (fun t => ((A₀ ≫ B₀) ≫ MV) ≫ t) hInvM
  have hR' :
      ((stackificationLiftPulledObjectDescentComparison X G hG F f y₀).hom.hom I₀ ≫
          (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₀).inv.hom I₀) ≫
        M.map (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d)) ≫
          ((stackificationLiftPulledGluedObjectDescentIso X G hG F f y₁).hom.hom I₁ ≫
            (stackificationLiftPulledObjectDescentComparison X G hG F f y₁).inv.hom I₁) =
      ((stackificationLiftPulledObjectDescentComparison X G hG F f y₀).hom.hom I₀ ≫
          (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₀).inv.hom I₀) ≫
        M.map (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d)) ≫
          M.map (stackificationLiftObjectPullbackComparison X G hG F f y₁).inv := by
    simpa only [A₀, B₀, MV, Category.assoc] using hR.symm
  refine Eq.trans ?_ hR'
  have hPG := stackificationLiftPulledGluedObjectDescentIso_verticalMap X G hG F f d I
  dsimp only [I₀, I₁, Fp, M] at hPG
  let Hbase := stackificationLiftHomExtensionFiberMap X G hG F
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₀ I₀).1
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₁ I₁).1
    ((stackificationLiftObjectModel (J := J) G hG y₀ I₀.base).2.hom ≫
      ((canonicalFiberPseudofunctor S'.p).map I₀.base.f.op.toLoc).toFunctor.map d ≫
      (stackificationLiftObjectModel (J := J) G hG y₁ I₁.base).2.inv)
  let G₁ := (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₁).hom.hom I₁
  let C₁ := (stackificationLiftPulledObjectDescentComparison X G hG F f y₁).inv.hom I₁
  have hPG' :
      B₀ ≫ MV ≫ G₁ =
        (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map Hbase := by
    simpa [B₀, MV, G₁, Hbase, M, Fp, I₀, I₁,
      stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
      Category.assoc] using hPG
  have hRmid :
      ((stackificationLiftPulledObjectDescentComparison X G hG F f y₀).hom.hom I₀ ≫
          (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₀).inv.hom I₀) ≫
        M.map (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d)) ≫
          (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₁).hom.hom I₁ ≫
          (stackificationLiftPulledObjectDescentComparison X G hG F f y₁).inv.hom I₁ =
        (stackificationLiftPulledObjectDescentComparison X G hG F f y₀).hom.hom I₀ ≫
          (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map Hbase ≫
          C₁ := by
    calc
      ((stackificationLiftPulledObjectDescentComparison X G hG F f y₀).hom.hom I₀ ≫
            (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₀).inv.hom I₀) ≫
          M.map (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            (stackificationLiftVerticalMap X G hG F d)) ≫
            (stackificationLiftPulledGluedObjectDescentIso X G hG F f y₁).hom.hom I₁ ≫
            (stackificationLiftPulledObjectDescentComparison X G hG F f y₁).inv.hom I₁ =
          A₀ ≫ (B₀ ≫ MV ≫ G₁) ≫ C₁ := by
        simp only [A₀, B₀, MV, G₁, C₁, Category.assoc]
        rfl
      _ = A₀ ≫ (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map Hbase ≫ C₁ := by
        rw [hPG']
        rfl
  refine Eq.trans ?_ hRmid.symm
  rw [stackificationLiftPulledObjectDescentComparison_hom_hom]
  change stackificationLiftVerticalLocalMap X G hG F
      (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) Iv =
    (stackificationLiftPulledLocalIso X G hG F f y₀ I₀).hom ≫
      (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map Hbase ≫
      (stackificationLiftPulledLocalIso X G hG F f y₁ I₁).inv
  rw [stackificationLiftPulledLocalIso_hom]
  rw [stackificationLiftPulledLocalIso_inv]
  let L₀ := (stackificationLiftObjectGluedLocalIso X G hG F
    (f ^*[canonicalPullbackChoice S'.p] y₀)
    (stackificationLiftPulledToObjectCover (J := J) G hG f y₀ I₀)).hom
  let L₁ := (stackificationLiftObjectGluedLocalIso X G hG F
    (f ^*[canonicalPullbackChoice S'.p] y₁)
    (stackificationLiftPulledToObjectCover (J := J) G hG f y₁ I₁)).inv
  let E₀ := (stackificationLiftPulledModelComparisonIso X G hG F f y₀ I₀).hom
  let E₁ := (stackificationLiftPulledModelComparisonIso X G hG F f y₁ I₁).inv
  let mid₀ := (FibredCategoryMor.fiberFunctor F I₀.Y).obj
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₀ I₀).1
  let mid₁ := (FibredCategoryMor.fiberFunctor F I₁.Y).obj
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₁ I₁).1
  let id₀ :=
    ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
      (LocallyDiscrete.mk (op I₀.Y)))).app mid₀).symm.hom
  let id₁ :=
    ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
      (LocallyDiscrete.mk (op I₁.Y)))).app mid₁).hom
  let mapH := (Fp.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map Hbase
  have hId :
      id₀ ≫ mapH ≫ id₁ = Hbase := by
    simpa [Fp, I₀, I₁, mid₀, mid₁, id₀, id₁, mapH] using
      Pseudofunctor.mapId_inv_map_hom_hom (canonicalFiberPseudofunctor X.p) I.Y Hbase
  have hCore :
      E₀ ≫ Hbase ≫ E₁ =
        stackificationLiftHomExtensionFiberMap X G hG F
          (stackificationLiftObjectModel (J := J) G hG
            (f ^*[canonicalPullbackChoice S'.p] y₀)
            (stackificationLiftVerticalCommonCover_left (J := J) G hG
              (f ^*[canonicalPullbackChoice S'.p] y₀)
              (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).1
          (stackificationLiftObjectModel (J := J) G hG
            (f ^*[canonicalPullbackChoice S'.p] y₁)
            (stackificationLiftVerticalCommonCover_right (J := J) G hG
              (f ^*[canonicalPullbackChoice S'.p] y₀)
              (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).1
          ((stackificationLiftObjectModel (J := J) G hG
              (f ^*[canonicalPullbackChoice S'.p] y₀)
              (stackificationLiftVerticalCommonCover_left (J := J) G hG
                (f ^*[canonicalPullbackChoice S'.p] y₀)
                (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).2.hom ≫
            ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
              (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) ≫
            (stackificationLiftObjectModel (J := J) G hG
              (f ^*[canonicalPullbackChoice S'.p] y₁)
              (stackificationLiftVerticalCommonCover_right (J := J) G hG
                (f ^*[canonicalPullbackChoice S'.p] y₀)
                (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).2.inv) := by
    simpa [E₀, E₁, Hbase, I₀, I₁, Iv] using
      stackificationLiftPulledModelComparisonIso_verticalMap X G hG F f d I
  change stackificationLiftVerticalLocalMap X G hG F
      (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) Iv =
    (L₀ ≫ E₀ ≫ id₀) ≫ mapH ≫ (id₁ ≫ E₁ ≫ L₁)
  calc
    stackificationLiftVerticalLocalMap X G hG F
        (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) Iv =
        L₀ ≫ (E₀ ≫ Hbase ≫ E₁) ≫ L₁ := by
      have hVert :
          stackificationLiftVerticalLocalMap X G hG F
              (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) Iv =
            L₀ ≫
              (stackificationLiftHomExtensionFiberMap X G hG F
                (stackificationLiftObjectModel (J := J) G hG
                  (f ^*[canonicalPullbackChoice S'.p] y₀)
                  (stackificationLiftVerticalCommonCover_left (J := J) G hG
                    (f ^*[canonicalPullbackChoice S'.p] y₀)
                    (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).1
                (stackificationLiftObjectModel (J := J) G hG
                  (f ^*[canonicalPullbackChoice S'.p] y₁)
                  (stackificationLiftVerticalCommonCover_right (J := J) G hG
                    (f ^*[canonicalPullbackChoice S'.p] y₀)
                    (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).1
                ((stackificationLiftObjectModel (J := J) G hG
                    (f ^*[canonicalPullbackChoice S'.p] y₀)
                    (stackificationLiftVerticalCommonCover_left (J := J) G hG
                      (f ^*[canonicalPullbackChoice S'.p] y₀)
                      (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).2.hom ≫
                  ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
                    (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) ≫
                  (stackificationLiftObjectModel (J := J) G hG
                    (f ^*[canonicalPullbackChoice S'.p] y₁)
                    (stackificationLiftVerticalCommonCover_right (J := J) G hG
                      (f ^*[canonicalPullbackChoice S'.p] y₀)
                      (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).2.inv)) ≫ L₁ := by
        dsimp [L₀, L₁, stackificationLiftVerticalLocalMap, Hbase, Iv, I₀, I₁,
          stackificationLiftPulledToObjectCover,
          stackificationLiftVerticalCommonCover_left,
          stackificationLiftVerticalCommonCover_right]
        rfl
      exact hVert.trans ((congrArg (fun t => L₀ ≫ t ≫ L₁) hCore).symm)
    _ = (L₀ ≫ E₀ ≫ id₀) ≫ mapH ≫ (id₁ ≫ E₁ ≫ L₁) := by
      simp only [Category.assoc]
      slice_rhs 3 5 => exact hId
      rw [Category.assoc]
      rfl

end

end CategoryTheory
