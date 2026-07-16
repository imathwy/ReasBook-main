import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityFront

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Front identity normalization: the local extension map appearing in the identity branch is
exactly the overlap transition after restricting along the identity on the branch base. -/
theorem stackificationLiftBasedFunctorIdentity_BE_eq_transition
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
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
    let BE := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y Il).1
      (stackificationLiftPulledObjectCoverModel (J := J) G hG
        (S'.p.map (𝟙 T)) y I).1
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
    ((canonicalFiberPseudofunctor X.p).map (𝟙 I.Y).op.toLoc).toFunctor.map BE =
      stackificationLiftObjectTransition X G hG F y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y)
        I.f
        (I₁ := Il) (I₂ := I.base)
        (𝟙 I.Y) (𝟙 I.Y)
        (by
          dsimp [Il, Ic, pb, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
            stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
            stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
          simp)
        (by
          dsimp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
          simp) := by
  intro y pb Ic Il BE
  dsimp only [BE]
  let x₁ := (stackificationLiftObjectModel (J := J) G hG y Il).1
  let x₂ := (stackificationLiftObjectModel (J := J) G hG y I.base).1
  let xp := (stackificationLiftPulledObjectCoverModel (J := J) G hG
    (S'.p.map (𝟙 T)) y I).1
  let cy₁ := (stackificationLiftObjectModel (J := J) G hG y Il).2
  let cy₂ := (stackificationLiftObjectModel (J := J) G hG y I.base).2
  let cyp := (stackificationLiftPulledObjectCoverModel (J := J) G hG
    (S'.p.map (𝟙 T)) y I).2
  have hxp : xp = x₂ := by
    dsimp [xp, x₂, stackificationLiftPulledObjectCoverModel]
  subst xp
  dsimp only [stackificationLiftObjectTransition]
  let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj x₁) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj x₂) :=
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
  let β :
      (FibredCategoryMor.fiberFunctor G I.Y).obj
          ((𝟙 I.Y) ^*[canonicalPullbackChoice S.p] x₁) ⟶
        (FibredCategoryMor.fiberFunctor G I.Y).obj
          ((𝟙 I.Y) ^*[canonicalPullbackChoice S.p] x₂) :=
    (stackificationLiftObjectModelPullbackIso (J := J) G y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y) I.f Il (𝟙 I.Y)
        (by
          dsimp [Il, Ic, pb, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
            stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
            stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
          simp)).hom ≫
      (stackificationLiftObjectModelPullbackIso (J := J) G y
        (stackificationLiftObjectCover (J := J) G hG y)
        (stackificationLiftObjectModel (J := J) G hG y) I.f I.base (𝟙 I.Y)
        (by
          dsimp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
          simp)).inv
  have hsource :
      ((canonicalFiberPseudofunctor S'.p).map (𝟙 I.Y).op.toLoc).toFunctor.map α =
        (FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₁).hom ≫
          β ≫ (FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₂).inv := by
    let e : I.f = I.f ≫ S'.p.map (𝟙 T) := by simp
    let φe : I.f ^*[canonicalPullbackChoice S'.p] y ⟶
        (I.f ≫ S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y :=
      eqToHom (congrArg (fun k => k ^*[canonicalPullbackChoice S'.p] y) e)
    let Msrc := ((canonicalFiberPseudofunctor S'.p).map (𝟙 I.Y).op.toLoc).toFunctor
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
    have hαnorm := stackificationLiftBasedFunctorIdentity_sourceArrow_eq_transport
      (J := J) G hG T I
    dsimp only at hαnorm
    have hmid := stackificationLiftBasedFunctorIdentity_sourceMiddle (J := J) G hG T I
    dsimp only at hmid
    have hαmap :
        Msrc.map α =
          Msrc.map ((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
            φe ≫ (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv) := by
      exact congrArg Msrc.map hαnorm
    have hdecomp :
        Msrc.map ((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
            φe ≫ (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv) =
          Msrc.map (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
            Msrc.map φe ≫
            Msrc.map (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv := by
      rw [Msrc.map_comp, Msrc.map_comp]
    have hmiddle :
        Msrc.map (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
            Msrc.map φe ≫
            Msrc.map (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv =
          Msrc.map (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
            (κl.inv ≫ κb.hom) ≫
            Msrc.map (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv := by
      exact congrArg
        (fun t =>
          Msrc.map (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫ t ≫
            Msrc.map (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv)
        hmid
    have hbeta :
        Msrc.map (stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
            (κl.inv ≫ κb.hom) ≫
            Msrc.map (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv =
          (FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₁).hom ≫
            β ≫ (FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₂).inv := by
      let c₁ := FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₁
      let c₂ := FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₂
      let A :=
        Msrc.map (stackificationLiftObjectModel (J := J) G hG y Il).2.hom
      let K := κl.inv
      let L := κb.hom
      let D :=
        Msrc.map (stackificationLiftObjectModel (J := J) G hG y I.base).2.inv
      change A ≫ (K ≫ L) ≫ D =
        c₁.hom ≫ β ≫ c₂.inv
      dsimp only [β, K, L, A, D, κl, κb, stackificationLiftObjectModelPullbackIso, c₁, c₂,
        Msrc, cy₁, cy₂, x₁, x₂]
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
        Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
      change A ≫ K ≫ L ≫ D =
        c₁.hom ≫ (c₁.inv ≫ A ≫ K) ≫ (L ≫ D ≫ c₂.hom) ≫ c₂.inv
      symm
      calc
        c₁.hom ≫ (c₁.inv ≫ A ≫ K) ≫ (L ≫ D ≫ c₂.hom) ≫ c₂.inv =
          (c₁.hom ≫ c₁.inv) ≫ A ≫ K ≫ L ≫ D ≫ (c₂.hom ≫ c₂.inv) := by
          simp only [Category.assoc]
        _ =
          A ≫ K ≫ L ≫ D := by
          rw [c₁.hom_inv_id]
          simp only [Category.id_comp]
          change A ≫ K ≫ L ≫ D ≫ (c₂.hom ≫ c₂.inv) = A ≫ K ≫ L ≫ D
          exact (congrArg (fun t => A ≫ K ≫ L ≫ D ≫ t) c₂.hom_inv_id).trans
            (congrArg (fun t => A ≫ K ≫ L ≫ t) (Category.comp_id D))
    exact hαmap.trans (hdecomp.trans (hmiddle.trans hbeta))
  change ((canonicalFiberPseudofunctor X.p).map (𝟙 I.Y).op.toLoc).toFunctor.map
      (stackificationLiftHomExtensionFiberMap X G hG F x₁ x₂ α) =
    (FibredCategoryMor.pullbackComparison F (𝟙 I.Y) x₁).hom ≫
      stackificationLiftHomExtensionFiberMap X G hG F
        ((𝟙 I.Y) ^*[canonicalPullbackChoice S.p] x₁)
        ((𝟙 I.Y) ^*[canonicalPullbackChoice S.p] x₂) β ≫
      (FibredCategoryMor.pullbackComparison F (𝟙 I.Y) x₂).inv
  have hmap :=
    stackificationLiftHomExtensionFiberMap_pullback X G hG F (𝟙 I.Y) α
  have happ :=
    stackificationLiftHomExtension_app_pullbackComparison X G hG F (𝟙 I.Y) β
  have hsourceApp :
      (stackificationLiftHomExtension X G hG F x₁ x₂).app (op (Over.mk (𝟙 I.Y)))
        (((canonicalFiberPseudofunctor S'.p).map (𝟙 I.Y).op.toLoc).toFunctor.map α) =
      (stackificationLiftHomExtension X G hG F x₁ x₂).app (op (Over.mk (𝟙 I.Y)))
        ((FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₁).hom ≫
          β ≫ (FibredCategoryMor.pullbackComparison G (𝟙 I.Y) x₂).inv) := by
    exact congrArg
      ((stackificationLiftHomExtension X G hG F x₁ x₂).app
        (op (Over.mk (𝟙 I.Y)))) hsource
  exact hmap.symm.trans (hsourceApp.trans happ)

end

end CategoryTheory
