import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.Identity

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

example
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (𝟙 (S'.p.obj T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    (stackificationLiftVerticalCommonCover (J := J) G hG
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)
      ((𝟙 (S'.p.obj T)) ^*[canonicalPullbackChoice S'.p]
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl))).Arrow := by
  refine ⟨I.Y, I.f, ?_⟩
  refine ⟨?_, (stackificationLiftPulledToObjectCover (J := J) G hG
    (𝟙 (S'.p.obj T))
    (Functor.Fiber.mk (p := S'.p) (a := T) rfl) I).hf⟩
  simpa using I.base.hf

noncomputable def identityPulledCommonCoverArrow
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    (stackificationLiftVerticalCommonCover (J := J) G hG
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)
      (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T))).Arrow :=
  ⟨I.Y, I.f, by
    refine ⟨?_, (stackificationLiftPulledToObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl) I).hf⟩
    simpa using I.base.hf⟩

example
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    stackificationLiftVerticalCommonCover_left (J := J) G hG
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl)
        (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T))
        (identityPulledCommonCoverArrow (J := J) G hG T I) =
      I.base := by
  ext <;> simp [identityPulledCommonCoverArrow,
    stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]

example
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    stackificationLiftVerticalCommonCover_right (J := J) G hG
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl)
        (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T))
        (identityPulledCommonCoverArrow (J := J) G hG T I) =
      stackificationLiftPulledToObjectCover (J := J) G hG
        (S'.p.map (𝟙 T))
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl) I := by
  ext <;> simp [identityPulledCommonCoverArrow,
    stackificationLiftVerticalCommonCover_right, stackificationLiftVerticalCommonCover,
    stackificationLiftPulledToObjectCover]

example
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
  rcases I with ⟨YI, fI, hfI⟩
  let I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T)) y).Arrow := ⟨YI, fI, hfI⟩
  let Ic := identityPulledCommonCoverArrow (J := J) G hG T I
  dsimp [stackificationLiftBasedFunctorMapCore]
  have hVert := stackificationLiftVerticalMap_local X G hG F
    (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) Ic
  change ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
      (stackificationLiftVerticalMap X G hG F
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))) =
    stackificationLiftVerticalLocalMap X G hG F
      (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) Ic at hVert
  let M := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
  change M.map
      ((stackificationLiftVerticalMap X G hG F
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
        (stackificationLiftArrowPullbackObjectComparison X G hG F (𝟙 T)).hom) ≫
        cart) =
    M.map (𝟙 z)
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
  let Il := stackificationLiftVerticalCommonCover_left (J := J) G hG y
    (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)) Ic
  let Ir := stackificationLiftVerticalCommonCover_right (J := J) G hG y
    (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)) Ic
  dsimp only [stackificationLiftVerticalLocalMap]
  change
    ((((stackificationLiftObjectGluedLocalIso X G hG F y Il).hom ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            (stackificationLiftObjectModel (J := J) G hG y Il).1
            (stackificationLiftObjectModel (J := J) G hG
              (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)) Ir).1
            ((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map Ic.f.op.toLoc).toFunctor.map
                (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
              (stackificationLiftObjectModel (J := J) G hG
                (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)) Ir).2.inv) ≫
          (stackificationLiftObjectGluedLocalIso X G hG F
            (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)) Ir).inv) ≫
        (stackificationLiftPulledObjectDescentComparison X G hG F
          (S'.p.map (𝟙 T)) y).hom.hom I ≫
          (stackificationLiftPulledGluedObjectDescentIso X G hG F
            (S'.p.map (𝟙 T)) y).inv.hom I) ≫
      M.map cart = M.map (𝟙 z))
  have hIr :
      Ir = stackificationLiftPulledToObjectCover (J := J) G hG
        (S'.p.map (𝟙 T)) y I := by
    simpa [Ir, Ic, identityPulledCommonCoverArrow] using
      stackificationLiftBasedFunctorIdentityCommonCoverArrow_right (J := J) G hG T I
  have hIr' :
      stackificationLiftPulledToObjectCover (J := J) G hG
        (S'.p.map (𝟙 T)) y I = Ir := hIr.symm
  clear hIr
  subst Ir
  trace_state
  sorry

end

end CategoryTheory
