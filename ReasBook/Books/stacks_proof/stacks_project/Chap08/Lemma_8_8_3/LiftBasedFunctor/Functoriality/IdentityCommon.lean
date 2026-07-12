import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.FunctorialityCore
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.Functoriality

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- For the identity-arrow calculation, a pulled-object cover branch is also a branch of the
common cover used by the vertical local formula. -/
noncomputable def stackificationLiftBasedFunctorIdentityCommonCoverArrow
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

/-- The left branch of the identity common cover is the original object-cover branch, up to the
identity base-map normalization coming from the pulled cover. -/
theorem stackificationLiftBasedFunctorIdentityCommonCoverArrow_left
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    stackificationLiftVerticalCommonCover_left (J := J) G hG
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl)
        (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T))
        (stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I) =
      I.base := by
  ext <;> simp [stackificationLiftBasedFunctorIdentityCommonCoverArrow,
    stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base]

/-- The right branch of the identity common cover is the pulled-object branch for the identity
pullback target. -/
theorem stackificationLiftBasedFunctorIdentityCommonCoverArrow_right
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    stackificationLiftVerticalCommonCover_right (J := J) G hG
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl)
        (stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T))
        (stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I) =
      stackificationLiftPulledToObjectCover (J := J) G hG
        (S'.p.map (𝟙 T))
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl) I := by
  ext <;> simp [stackificationLiftBasedFunctorIdentityCommonCoverArrow,
    stackificationLiftVerticalCommonCover_right, stackificationLiftVerticalCommonCover,
    stackificationLiftPulledToObjectCover]

theorem stackificationLiftBasedFunctorIdentity_verticalLocalMap_eq_pulled
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    let y : S'.p.Fiber (S'.p.obj T) := Functor.Fiber.mk (p := S'.p) (a := T) rfl
    let pb : S'.p.Fiber (S'.p.obj T) := stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)
    let Ic := stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I
    let Il := stackificationLiftVerticalCommonCover_left (J := J) G hG y pb Ic
    let Iz := stackificationLiftPulledToObjectCover (J := J) G hG (S'.p.map (𝟙 T)) y I
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
  intro y pb Ic Il Iz
  have hR : Iz =
      stackificationLiftVerticalCommonCover_right (J := J) G hG y pb Ic := by
    simpa [Iz, Ic, pb, y] using
      (stackificationLiftBasedFunctorIdentityCommonCoverArrow_right (J := J) G hG T I).symm
  cases hR
  dsimp [stackificationLiftVerticalLocalMap]
  rfl

end

end CategoryTheory
