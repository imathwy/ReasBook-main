import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityOverlap

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

theorem stackificationLiftBasedFunctorIdentity_front_raw
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
    let A := (stackificationLiftObjectGluedLocalIso X G hG F y Il).hom
    let BE := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y Il).1
      (stackificationLiftPulledObjectCoverModel (J := J) G hG (S'.p.map (𝟙 T)) y I).1
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
    let E := eqToHom (by
        simp [Il, Ic, pb, y, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
          stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
          stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base])
    A ≫ BE ≫ (stackificationLiftObjectGluedIso X G hG F y).inv.hom I.base =
      E := by
  intro y pb Ic Il A BE E
  let Mid := ((canonicalFiberPseudofunctor X.p).map (𝟙 I.Y).op.toLoc).toFunctor
  haveI : Mid.Faithful := by
    dsimp [Mid]
    let e := Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
      (LocallyDiscrete.mk (op I.Y)))
    refine ⟨?_⟩
    intro U V f g hfg
    have hf :
        f =
          e.inv.app U ≫
            (((canonicalFiberPseudofunctor X.p).map
                (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map f ≫
              e.hom.app V) := by
      symm
      rw [e.hom.naturality f]
      rw [← Category.assoc]
      rw [e.inv_hom_id_app]
      simp
    have hg :
        g =
          e.inv.app U ≫
            (((canonicalFiberPseudofunctor X.p).map
                (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map g ≫
              e.hom.app V) := by
      symm
      rw [e.hom.naturality g]
      rw [← Category.assoc]
      rw [e.inv_hom_id_app]
      simp
    rw [hf, hg, hfg]
  apply Mid.map_injective
  have hBE := stackificationLiftBasedFunctorIdentity_BE_eq_transition X G hG F T I
  dsimp only at hBE
  have hcomm := stackificationLiftObjectGluedLocalIso_comm X G hG F y I.f
    (I₁ := Il) (I₂ := I.base) (𝟙 I.Y) (𝟙 I.Y)
    (by
      dsimp [Il, Ic, pb, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
        stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
        stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
      simp)
    (by
      dsimp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
      simp)
  dsimp only [stackificationLiftObjectTransition, y, Il, pb, Ic] at hcomm
  have hD := stackificationLiftBasedFunctorIdentity_descent_id_overlap X G hG F T I
  dsimp only at hD
  let Cinv := (stackificationLiftObjectGluedIso X G hG F y).inv.hom I.base
  change Mid.map (A ≫ (BE ≫ Cinv)) = Mid.map E
  rw [Mid.map_comp A (BE ≫ Cinv)]
  rw [Mid.map_comp BE Cinv]
  rw [hBE]
  dsimp only [stackificationLiftObjectTransition, A, y, Il, pb, Ic, Mid]
  rw [← Category.assoc]
  have hcommC := congrArg
    (fun t => t ≫
      ((canonicalFiberPseudofunctor X.p).map (𝟙 I.Y).op.toLoc).toFunctor.map Cinv) hcomm
  dsimp only at hcommC
  refine hcommC.trans ?_
  refine (Category.assoc _ _ _).trans ?_
  change _ ≫
      (Mid.map (stackificationLiftObjectGluedLocalIso X G hG F y I.base).hom ≫
        Mid.map Cinv) = Mid.map E
  rw [← Mid.map_comp]
  have hbase :
      (stackificationLiftObjectGluedLocalIso X G hG F y I.base).hom ≫ Cinv =
        𝟙 _ := by
    dsimp [Cinv, stackificationLiftObjectGluedLocalIso]
    exact (stackificationLiftObjectGluedLocalIso X G hG F y I.base).hom_inv_id
  have hmapbase :=
    congrArg (fun t => Mid.map t) hbase
  dsimp only at hmapbase
  refine (congrArg (fun t => _ ≫ t) hmapbase).trans ?_
  refine (congrArg (fun t => _ ≫ t) (Mid.map_id _)).trans ?_
  exact (Category.comp_id _).trans hD

end

end CategoryTheory
