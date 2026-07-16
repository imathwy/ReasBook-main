import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityTransition

universe u v uS vS v' u'

namespace CategoryTheory

open BasedFunctor
open Opposite

section Generic

variable {C : Type u} [Category.{v} C]

theorem pseudofunctor_id_overlap_hom_eq_map_eqToHom
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {U V : C}
    (f f' : LocallyDiscrete.mk (op U) ⟶ LocallyDiscrete.mk (op V))
    (h : f = f')
    (z : F.obj (LocallyDiscrete.mk (op U))) :
    (F.mapComp' f (𝟙 (LocallyDiscrete.mk (op V))) f (by simp)).inv.toNatTrans.app z ≫
      (F.mapComp' f' (𝟙 (LocallyDiscrete.mk (op V))) f (by simpa [h])).hom.toNatTrans.app z =
        (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map
          (eqToHom (congrArg (fun k => (F.map k).toFunctor.obj z) h)) := by
  subst h
  simpa using
    (Cat.Hom.inv_hom_id_toNatTrans_app
      (F.mapComp' f (𝟙 (LocallyDiscrete.mk (op V))) f (by simp)) z)

end Generic

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

theorem stackificationLiftBasedFunctorIdentity_descent_id_overlap
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    let y : S'.p.Fiber (S'.p.obj T) :=
      Functor.Fiber.mk (p := S'.p) (a := T) rfl
    let z : X.p.Fiber (S'.p.obj T) := stackificationLiftObjectGlued X G hG F y
    let pb : S'.p.Fiber (S'.p.obj T) :=
      stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)
    let Ic := stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I
    let Il := stackificationLiftVerticalCommonCover_left (J := J) G hG y pb Ic
    let E := eqToHom (by
        simp [Il, Ic, pb, y, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
          stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
          stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base])
    let M := ((canonicalFiberPseudofunctor X.p).map (𝟙 I.Y).op.toLoc).toFunctor
    let D :=
      (((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)).obj z)
    D.hom (i₁ := Il) (i₂ := I.base) I.f (𝟙 I.Y) (𝟙 I.Y)
        (by
          dsimp [Il, Ic, pb, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
            stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
            stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
          simp)
        (by
          dsimp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]
          simp) =
      M.map E := by
  intro y z pb Ic Il E M D
  let Fp := canonicalFiberPseudofunctor X.p
  let f₁ : LocallyDiscrete.mk (op (S'.p.obj T)) ⟶ LocallyDiscrete.mk (op I.Y) :=
    I.f.op.toLoc
  let f₂ : LocallyDiscrete.mk (op (S'.p.obj T)) ⟶ LocallyDiscrete.mk (op I.Y) :=
    (S'.p.map (𝟙 T)).op.toLoc ≫ I.f.op.toLoc
  have hf : f₁ = f₂ := by
    dsimp [f₁, f₂]
    simp
  have hmain :=
    pseudofunctor_id_overlap_hom_eq_map_eqToHom Fp f₁ f₂ hf z
  dsimp [D, M, E, Fp, f₁, f₂, Il, Ic, pb, y,
    stackificationLiftBasedFunctorIdentityCommonCoverArrow,
    stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
    Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj] at hmain ⊢
  simpa using hmain

end

end CategoryTheory
