import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityCommon
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityPullback

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

theorem stackificationLiftBasedFunctorIdentity_sourceArrow_eq_transport
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    let y : S'.p.Fiber (S'.p.obj T) :=
      Functor.Fiber.mk (p := S'.p) (a := T) rfl
    let pb : S'.p.Fiber (S'.p.obj T) :=
      stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)
    let Ic := stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I
    let Il := stackificationLiftVerticalCommonCover_left (J := J) G hG y pb Ic
    let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj
          (stackificationLiftObjectModel (J := J) G hG y Il).1) ⟶
        ((FibredCategoryMor.fiberFunctor G I.Y).obj
          (stackificationLiftObjectModel (J := J) G hG y I.base).1) :=
      (((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
          ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
            (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
          (stackificationLiftObjectModel (J := J) G hG pb
            (stackificationLiftPulledToObjectCover (J := J) G hG
              (S'.p.map (𝟙 T)) y I)).2.inv) ≫
          ((stackificationLiftObjectModel (J := J) G hG pb
            (stackificationLiftPulledToObjectCover (J := J) G hG
              (S'.p.map (𝟙 T)) y I)).2.hom ≫
            (stackificationLiftPulledObjectCoverModel (J := J) G hG
              (S'.p.map (𝟙 T)) y I).2.inv))
    α =
      (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
        eqToHom (congrArg
          (fun k => k ^*[canonicalPullbackChoice S'.p] y)
          (by simp : I.f = I.f ≫ S'.p.map (𝟙 T))) ≫
        (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv := by
  intro y pb Ic Il α
  have hv := stackificationLiftArrowVerticalFactor_id_mapCompAppIso_inv
    (J := J) (S' := S') T I.Y I.f
  dsimp only [α]
  dsimp only [stackificationLiftPulledObjectCoverModel]
  simp only [Iso.trans_inv, Category.assoc]
  let epb := (stackificationLiftObjectModel (J := J) G hG pb
    (stackificationLiftPulledToObjectCover (J := J) G hG
      (S'.p.map (𝟙 T)) y I)).2
  let A :=
    (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
      ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))
  let K :=
    (mapCompAppIso S'.p (S'.p.map (𝟙 T)) I.f (I.f ≫ S'.p.map (𝟙 T))
      (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) I.f
        (I.f ≫ S'.p.map (𝟙 T)) rfl) y).inv
  let D := (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv
  calc
    (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
          ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
              (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
        epb.inv ≫ epb.hom ≫
          (mapCompAppIso S'.p (S'.p.map (𝟙 T)) I.f (I.f ≫ S'.p.map (𝟙 T))
            (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) I.f
              (I.f ≫ S'.p.map (𝟙 T)) rfl) y).inv ≫
        (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv =
      (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
        (((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
              (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
          (mapCompAppIso S'.p (S'.p.map (𝟙 T)) I.f (I.f ≫ S'.p.map (𝟙 T))
            (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) I.f
              (I.f ≫ S'.p.map (𝟙 T)) rfl) y).inv) ≫
        (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv := by
        have hsmall : A ≫ epb.inv ≫ epb.hom ≫ K ≫ D = A ≫ K ≫ D := by
          calc
            A ≫ epb.inv ≫ epb.hom ≫ K ≫ D =
                A ≫ (epb.inv ≫ epb.hom) ≫ K ≫ D := by
                  simp only [Category.assoc]
            _ = A ≫ 𝟙 _ ≫ K ≫ D := by
                  exact congrArg (fun t => A ≫ t ≫ K ≫ D) epb.inv_hom_id
            _ = A ≫ K ≫ D := by
                  simp only [Category.id_comp]
        simpa only [A, K, D, Category.assoc] using hsmall
    _ =
      (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
        eqToHom (congrArg
          (fun k => k ^*[canonicalPullbackChoice S'.p] y)
          (by simp : I.f = I.f ≫ S'.p.map (𝟙 T))) ≫
        (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv := by
        exact congrArg
          (fun t =>
            (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫ t ≫
              (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv)
          hv

theorem stackificationLiftBasedFunctorIdentity_sourceMiddle
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    let y : S'.p.Fiber (S'.p.obj T) :=
      Functor.Fiber.mk (p := S'.p) (a := T) rfl
    let pb : S'.p.Fiber (S'.p.obj T) :=
      stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)
    let Ic := stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I
    let Il := stackificationLiftVerticalCommonCover_left (J := J) G hG y pb Ic
    ((canonicalFiberPseudofunctor S'.p).map (𝟙 I.Y).op.toLoc).toFunctor.map
        (eqToHom (congrArg
          (fun k => k ^*[canonicalPullbackChoice S'.p] y)
          (by simp : I.f = I.f ≫ S'.p.map (𝟙 T))) :
          I.f ^*[canonicalPullbackChoice S'.p] y ⟶
            (I.f ≫ S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y) =
      (mapCompAppIso S'.p Il.f (𝟙 I.Y) I.f
        (FibredCategoryMor.comp_toLoc_eq Il.f (𝟙 I.Y) I.f
          (by
            dsimp [Il, Ic, pb, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
              stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
              stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
            simp)) y).inv ≫
      (mapCompAppIso S'.p I.base.f (𝟙 I.Y) I.f
        (FibredCategoryMor.comp_toLoc_eq I.base.f (𝟙 I.Y) I.f
          (by
            dsimp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
            simp)) y).hom := by
  intro y pb Ic Il
  apply Functor.Fiber.hom_ext
  let e : I.f = I.f ≫ S'.p.map (𝟙 T) := by simp
  let φe : I.f ^*[canonicalPullbackChoice S'.p] y ⟶
      (I.f ≫ S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y :=
    eqToHom (congrArg (fun k => k ^*[canonicalPullbackChoice S'.p] y) e)
  let M := ((canonicalFiberPseudofunctor S'.p).map (𝟙 I.Y).op.toLoc).toFunctor
  let hIl : (𝟙 I.Y) ≫ Il.f = I.f := by
    dsimp [Il, Ic, pb, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
      stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
      stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
    simp
  let hbase : (𝟙 I.Y) ≫ I.base.f = I.f := by
    dsimp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
    simp
  let κl := mapCompAppIso S'.p Il.f (𝟙 I.Y) I.f
    (FibredCategoryMor.comp_toLoc_eq Il.f (𝟙 I.Y) I.f hIl) y
  let κb := mapCompAppIso S'.p I.base.f (𝟙 I.Y) I.f
    (FibredCategoryMor.comp_toLoc_eq I.base.f (𝟙 I.Y) I.f hbase) y
  let θ :=
    (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
        (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
      (canonicalPullbackChoice S'.p).map I.base.f y
  have hθcart : S'.p.IsStronglyCartesian ((𝟙 I.Y) ≫ I.base.f) θ := by
    have hcartId : S'.p.IsStronglyCartesian (𝟙 I.Y)
        ((canonicalPullbackChoice S'.p).map (𝟙 I.Y)
          (I.base.f ^*[canonicalPullbackChoice S'.p] y)) :=
      (canonicalPullbackChoice S'.p).isStronglyCartesian (𝟙 I.Y)
        (I.base.f ^*[canonicalPullbackChoice S'.p] y)
    have hcartBase : S'.p.IsStronglyCartesian I.base.f
        ((canonicalPullbackChoice S'.p).map I.base.f y) :=
      (canonicalPullbackChoice S'.p).isStronglyCartesian I.base.f y
    change S'.p.IsStronglyCartesian ((𝟙 I.Y) ≫ I.base.f)
      (((canonicalPullbackChoice S'.p).map (𝟙 I.Y)
          (I.base.f ^*[canonicalPullbackChoice S'.p] y)) ≫
        (canonicalPullbackChoice S'.p).map I.base.f y)
    exact @CategoryTheory.Functor.IsStronglyCartesian.comp _ _ _ _ S'.p
      _ _ _ _ _ _ _ _ _ _ hcartId hcartBase
  have hLeftLift : S'.p.IsHomLift (𝟙 I.Y) (M.map φe).1 := (M.map φe).2
  have hRightLift : S'.p.IsHomLift (𝟙 I.Y) ((κl.inv ≫ κb.hom).1) :=
    (κl.inv ≫ κb.hom).2
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ S'.p _ _ _ _
    ((𝟙 I.Y) ≫ I.base.f) θ hθcart _ _ (𝟙 I.Y)
    (M.map φe).1 ((κl.inv ≫ κb.hom).1) hLeftLift hRightLift ?_
  have hmap :
      (M.map φe).1 ≫
          (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            ((I.f ≫ S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y) =
        (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (I.f ^*[canonicalPullbackChoice S'.p] y) ≫ φe.1 := by
    dsimp only [M, φe]
    exact FibredCategoryMor.canonical_pullbackFunctor_map_fac S'.p (𝟙 I.Y)
      (eqToHom (congrArg (fun k => k ^*[canonicalPullbackChoice S'.p] y) e))
  have heqfac :
      φe.1 ≫ (canonicalPullbackChoice S'.p).map (I.f ≫ S'.p.map (𝟙 T)) y =
        (canonicalPullbackChoice S'.p).map I.f y := by
    dsimp only [φe]
    exact eqToHom_pullbackMap_fac S'.p I.f (I.f ≫ S'.p.map (𝟙 T)) e y
  have hleft :
      (M.map φe).1 ≫ θ =
        (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
          (canonicalPullbackChoice S'.p).map I.f y := by
    dsimp only [θ]
    calc
      (M.map φe).1 ≫
          ((canonicalPullbackChoice S'.p).map (𝟙 I.Y)
              (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
            (canonicalPullbackChoice S'.p).map I.base.f y) =
        ((M.map φe).1 ≫
          (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
              ((I.f ≫ S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y)) ≫
            (canonicalPullbackChoice S'.p).map (I.f ≫ S'.p.map (𝟙 T)) y := by
          dsimp [hbase, stackificationLiftPulledObjectCover,
            GrothendieckTopology.Cover.Arrow.base]
          simp only [Category.assoc]
      _ =
        ((canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (I.f ^*[canonicalPullbackChoice S'.p] y) ≫ φe.1) ≫
          (canonicalPullbackChoice S'.p).map (I.f ≫ S'.p.map (𝟙 T)) y := by
          exact congrArg
            (fun t => t ≫
              (canonicalPullbackChoice S'.p).map (I.f ≫ S'.p.map (𝟙 T)) y)
            hmap
      _ =
        (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
          (φe.1 ≫
            (canonicalPullbackChoice S'.p).map (I.f ≫ S'.p.map (𝟙 T)) y) := by
          simp only [Category.assoc]
      _ =
        (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
          (canonicalPullbackChoice S'.p).map I.f y := by
          exact congrArg
            (fun t => (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
              (I.f ^*[canonicalPullbackChoice S'.p] y) ≫ t)
            heqfac
  have hκb :
      κb.hom.1 ≫
          (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
        (canonicalPullbackChoice S'.p).map I.base.f y =
      (canonicalPullbackChoice S'.p).map I.f y := by
    dsimp only [κb, mapCompAppIso]
    simpa using
      (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        S'.p I.base.f (𝟙 I.Y) I.f hbase y)
  have hκl :
      κl.inv.1 ≫ (canonicalPullbackChoice S'.p).map I.f y =
        (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (Il.f ^*[canonicalPullbackChoice S'.p] y) ≫
          (canonicalPullbackChoice S'.p).map Il.f y := by
    dsimp only [κl]
    exact mapCompAppIso_inv_comp_pullbackMap S'.p Il.f (𝟙 I.Y) I.f hIl y
  have hIl_map :
      (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
          (Il.f ^*[canonicalPullbackChoice S'.p] y) ≫
        (canonicalPullbackChoice S'.p).map Il.f y =
      (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
          (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
        (canonicalPullbackChoice S'.p).map I.f y := by
    dsimp [Il, Ic, pb, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
      stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
      stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
  have hright :
      (κl.inv ≫ κb.hom).1 ≫ θ =
        (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
            (I.f ^*[canonicalPullbackChoice S'.p] y) ≫
          (canonicalPullbackChoice S'.p).map I.f y := by
    dsimp only [θ]
    have hmid :
        (κl.inv ≫ κb.hom).1 ≫
            ((canonicalPullbackChoice S'.p).map (𝟙 I.Y)
                (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
              (canonicalPullbackChoice S'.p).map I.base.f y) =
          κl.inv.1 ≫ (canonicalPullbackChoice S'.p).map I.f y := by
      calc
        (κl.inv ≫ κb.hom).1 ≫
            ((canonicalPullbackChoice S'.p).map (𝟙 I.Y)
                (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
              (canonicalPullbackChoice S'.p).map I.base.f y) =
          κl.inv.1 ≫
            (κb.hom.1 ≫
              (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
                  (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
                (canonicalPullbackChoice S'.p).map I.base.f y) := by
            change (κl.inv.1 ≫ κb.hom.1) ≫
                ((canonicalPullbackChoice S'.p).map (𝟙 I.Y)
                  (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
                (canonicalPullbackChoice S'.p).map I.base.f y) =
              κl.inv.1 ≫
                (κb.hom.1 ≫
                  (canonicalPullbackChoice S'.p).map (𝟙 I.Y)
                      (I.base.f ^*[canonicalPullbackChoice S'.p] y) ≫
                    (canonicalPullbackChoice S'.p).map I.base.f y)
            simp only [Category.assoc]
        _ = κl.inv.1 ≫ (canonicalPullbackChoice S'.p).map I.f y := by
            exact congrArg (fun t => κl.inv.1 ≫ t) hκb
    exact hmid.trans (hκl.trans hIl_map)
  exact hleft.trans hright.symm

end

end CategoryTheory
