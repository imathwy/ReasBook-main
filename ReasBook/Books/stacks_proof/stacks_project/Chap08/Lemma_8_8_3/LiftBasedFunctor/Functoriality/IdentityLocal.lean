import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityCommon
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityPullback
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityTail
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityTailAfterFront
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityTransition

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Local reduction for the identity-arrow calculation.  After restricting the identity core
map to a pulled-cover branch, the vertical local formula and the pulled-object comparison reduce
the expression to the final descent-normalization tail. -/
theorem stackificationLiftBasedFunctorMapCore_id_local_reduction
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
    ∀ (cart : (S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice X.p] z ⟶ z),
    let M := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
    let Ic := stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I
    let pb : S'.p.Fiber (S'.p.obj T) :=
      stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)
    let Iz := stackificationLiftPulledToObjectCover (J := J) G hG (S'.p.map (𝟙 T)) y I
    let Il := stackificationLiftVerticalCommonCover_left (J := J) G hG y
      (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)) Ic
    let A := (stackificationLiftObjectGluedLocalIso X G hG F y Il).hom
    let BE := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y Il).1
      (stackificationLiftPulledObjectCoverModel (J := J) G hG (S'.p.map (𝟙 T)) y I).1
      (((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
        (stackificationLiftObjectModel (J := J) G hG pb Iz).2.inv) ≫
        ((stackificationLiftObjectModel (J := J) G hG pb Iz).2.hom ≫
          (stackificationLiftPulledObjectCoverModel (J := J) G hG
            (S'.p.map (𝟙 T)) y I).2.inv))
    let F0 := ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op I.Y)))).app
      ((FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftPulledObjectCoverModel (J := J) G hG
          (S'.p.map (𝟙 T)) y I).1)).symm.hom
    let Gtail := (stackificationLiftPulledGluedObjectDescentIso X G hG F
      (S'.p.map (𝟙 T)) y).inv.hom I
    let H := M.map cart
    M.map ((stackificationLiftBasedFunctorMapCore X G hG F (𝟙 T)) ≫ cart) =
      A ≫ BE ≫ F0 ≫ Gtail ≫ H := by
  intro y z cart M Ic pb Iz Il A BE F0 Gtail H
  dsimp [stackificationLiftBasedFunctorMapCore]
  have hVert := stackificationLiftVerticalMap_local X G hG F
    (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) Ic
  change ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
      (stackificationLiftVerticalMap X G hG F
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))) =
    stackificationLiftVerticalLocalMap X G hG F
      (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) Ic at hVert
  change M.map
      ((stackificationLiftVerticalMap X G hG F
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
        (stackificationLiftArrowPullbackObjectComparison X G hG F (𝟙 T)).hom) ≫
        cart) =
    A ≫ BE ≫ F0 ≫ Gtail ≫ H
  have hVertM :
      M.map
          (stackificationLiftVerticalMap X G hG F
            (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))) =
        stackificationLiftVerticalLocalMap X G hG F
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) Ic := by
    simpa [M] using hVert
  rw [M.map_comp]
  rw [M.map_comp]
  rw [hVertM]
  have hCompM :
      M.map (stackificationLiftArrowPullbackObjectComparison X G hG F (𝟙 T)).hom =
        (stackificationLiftPulledObjectDescentComparison X G hG F
            (S'.p.map (𝟙 T)) y).hom.hom I ≫
          (stackificationLiftPulledGluedObjectDescentIso X G hG F
            (S'.p.map (𝟙 T)) y).inv.hom I := by
    simpa [M, stackificationLiftArrowPullbackObjectComparison, y] using
      stackificationLiftObjectPullbackComparison_local_hom X G hG F
        (S'.p.map (𝟙 T)) y I
  rw [hCompM]
  have hVL :
      stackificationLiftVerticalLocalMap X G hG F
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) Ic =
        (stackificationLiftObjectGluedLocalIso X G hG F y Il).hom ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            (stackificationLiftObjectModel (J := J) G hG y Il).1
            (stackificationLiftObjectModel (J := J) G hG pb Iz).1
            ((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
                (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
              (stackificationLiftObjectModel (J := J) G hG pb Iz).2.inv) ≫
          (stackificationLiftObjectGluedLocalIso X G hG F pb Iz).inv := by
    simpa [y, pb, Ic, Il, Iz] using
      stackificationLiftBasedFunctorIdentity_verticalLocalMap_eq_pulled X G hG F T I
  rw [hVL]
  rw [stackificationLiftPulledObjectDescentComparison_hom_hom]
  have hPLI :
      (stackificationLiftPulledLocalIso X G hG F (S'.p.map (𝟙 T)) y I).hom =
        (stackificationLiftObjectGluedLocalIso X G hG F pb Iz).hom ≫
          (stackificationLiftPulledModelComparisonIso X G hG F
            (S'.p.map (𝟙 T)) y I).hom ≫
          ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
              (LocallyDiscrete.mk (op I.Y)))).app
            ((FibredCategoryMor.fiberFunctor F I.Y).obj
              (stackificationLiftPulledObjectCoverModel (J := J) G hG
                (S'.p.map (𝟙 T)) y I).1)).symm.hom := by
    simpa [pb, Iz] using
      stackificationLiftPulledLocalIso_hom X G hG F (S'.p.map (𝟙 T)) y I
  rw [hPLI]
  let B := stackificationLiftHomExtensionFiberMap X G hG F
    (stackificationLiftObjectModel (J := J) G hG y Il).1
    (stackificationLiftObjectModel (J := J) G hG pb Iz).1
    ((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
      ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
      (stackificationLiftObjectModel (J := J) G hG pb Iz).2.inv)
  let Ciso := (stackificationLiftObjectGluedLocalIso X G hG F pb Iz).inv
  let Diso := (stackificationLiftObjectGluedLocalIso X G hG F pb Iz).hom
  let E := (stackificationLiftPulledModelComparisonIso X G hG F
    (S'.p.map (𝟙 T)) y I).hom
  change (((A ≫ B ≫ Ciso) ≫ ((Diso ≫ E ≫ F0) ≫ Gtail)) ≫ H =
    A ≫ BE ≫ F0 ≫ Gtail ≫ H)
  have hAssoc :
      (((A ≫ B ≫ Ciso) ≫ ((Diso ≫ E ≫ F0) ≫ Gtail)) ≫ H) =
        A ≫ B ≫ (Ciso ≫ Diso) ≫ E ≫ F0 ≫ Gtail ≫ H := by
    simp only [Category.assoc]
  rw [hAssoc]
  have hCD : Ciso ≫ Diso =
      𝟙 ((FibredCategoryMor.fiberFunctor F Iz.Y).obj
        (stackificationLiftObjectModel (J := J) G hG pb Iz).1) := by
    dsimp [Ciso, Diso]
    exact (stackificationLiftObjectGluedLocalIso X G hG F pb Iz).inv_hom_id
  have hReplace :
      A ≫ B ≫ (Ciso ≫ Diso) ≫ E ≫ F0 ≫ Gtail ≫ H =
        A ≫ B ≫ 𝟙 _ ≫ E ≫ F0 ≫ Gtail ≫ H := by
    exact congrArg (fun t => A ≫ B ≫ t ≫ E ≫ F0 ≫ Gtail ≫ H) hCD
  rw [hReplace]
  simp only [Category.id_comp]
  let E' := stackificationLiftHomExtensionFiberMap X G hG F
    (stackificationLiftObjectModel (J := J) G hG pb Iz).1
    (stackificationLiftPulledObjectCoverModel (J := J) G hG (S'.p.map (𝟙 T)) y I).1
    ((stackificationLiftObjectModel (J := J) G hG pb Iz).2.hom ≫
      (stackificationLiftPulledObjectCoverModel (J := J) G hG
        (S'.p.map (𝟙 T)) y I).2.inv)
  have hE : E = E' := by
    dsimp [E, E']
    simpa [pb, Iz] using
      stackificationLiftPulledModelComparisonIso_hom X G hG F (S'.p.map (𝟙 T)) y I
  rw [hE]
  have hBE : B ≫ E' = BE := by
    dsimp [B, E', BE]
    exact (stackificationLiftHomExtensionFiberMap_comp X G hG F
      ((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
        (stackificationLiftObjectModel (J := J) G hG pb Iz).2.inv)
      ((stackificationLiftObjectModel (J := J) G hG pb Iz).2.hom ≫
        (stackificationLiftPulledObjectCoverModel (J := J) G hG
          (S'.p.map (𝟙 T)) y I).2.inv)).symm
  calc
    A ≫ B ≫ E' ≫ F0 ≫ Gtail ≫ H =
        A ≫ (B ≫ E') ≫ F0 ≫ Gtail ≫ H := by
      simp only [Category.assoc]
    _ = A ≫ BE ≫ F0 ≫ Gtail ≫ H := by
      exact congrArg (fun t => A ≫ t ≫ F0 ≫ Gtail ≫ H) hBE

/-- Local identity blocker for Chap08 Lemma 8 8 3.

This is the small file where the remaining identity calculation lives: after restricting to the
pulled cover of the identity pullback, the vertical local formula, the pulled-object comparison,
and the chosen identity pullback arrow in `X` should compose to the local identity. -/
theorem stackificationLiftBasedFunctorMapCore_id_fiber_fac
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S) :
    let y : S'.p.Fiber (S'.p.obj T) :=
      Functor.Fiber.mk (p := S'.p) (a := T) rfl
    let z : X.p.Fiber (S'.p.obj T) := stackificationLiftObjectGlued X G hG F y
    let cart :
        (S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice X.p] z ⟶ z :=
      ⟨(canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T)) z, by
        have hcart :
            X.p.IsHomLift (S'.p.map (𝟙 T))
              ((canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T)) z) :=
          ((canonicalPullbackChoice X.p).isStronglyCartesian (S'.p.map (𝟙 T)) z).toIsHomLift
        simpa using hcart⟩
    stackificationLiftBasedFunctorMapCore X G hG F (𝟙 T) ≫ cart = 𝟙 z := by
  intro y z cart
  apply stack_cover_hom_ext (J := J) X
    (stackificationLiftPulledObjectCover (J := J) G hG (S'.p.map (𝟙 T)) y)
  intro I
  have hred := stackificationLiftBasedFunctorMapCore_id_local_reduction X G hG F T I cart
  dsimp only at hred
  refine hred.trans ?_
  have htail := stackificationLiftBasedFunctorIdentity_tail_after_front X G hG F T I
  dsimp only at htail
  exact htail

end

end CategoryTheory
