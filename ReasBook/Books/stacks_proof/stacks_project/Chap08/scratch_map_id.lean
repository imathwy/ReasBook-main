import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

#check PullbackChoice.pullbackIdComponentIso
#check PullbackChoice.pullbackIdComponentIso_fac
#check stackificationLiftArrowVerticalFactor_fac
#check stackificationLiftVerticalMap_id
#check Functor.IsStronglyCartesian.ext
#check PullbackChoice.pullbackIdComponentIso_inv_eq

example (T : S'.S) :
    (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)).1 ≫
      (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T))
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl : S'.p.Fiber (S'.p.obj T)) =
    (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice S'.p)
        (S'.p.obj T)
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).hom.1 ≫
      (canonicalPullbackChoice S'.p).map (𝟙 (S'.p.obj T))
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl : S'.p.Fiber (S'.p.obj T)) := by
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  have hleft :
      (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)).1 ≫
        (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y =
      𝟙 T := by
    simpa [y] using stackificationLiftArrowVerticalFactor_fac (S' := S') (𝟙 T)
  have hright :
      (PullbackChoice.pullbackIdComponentIso (canonicalPullbackChoice S'.p)
          (S'.p.obj T) y).hom.1 ≫
        (canonicalPullbackChoice S'.p).map (𝟙 (S'.p.obj T)) y =
      𝟙 T := by
    simpa [y] using
      PullbackChoice.pullbackIdComponentIso_fac (canonicalPullbackChoice S'.p)
        (S'.p.obj T) y
  exact hleft.trans hright.symm

example (T : S'.S) :
    (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)).1 ≫
      (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T))
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl : S'.p.Fiber (S'.p.obj T)) =
      𝟙 T := by
  simpa using stackificationLiftArrowVerticalFactor_fac (S' := S') (𝟙 T)

example
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S) :
    stackificationLiftBasedFunctorMap X G hG F (𝟙 T) =
      𝟙 (stackificationLiftBasedFunctorObj X G hG F T) := by
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let z : X.p.Fiber (S'.p.obj T) := stackificationLiftObjectGlued X G hG F y
  have hMapLift : X.p.IsHomLift (𝟙 (S'.p.obj T))
      (stackificationLiftBasedFunctorMap X G hG F (𝟙 T)) := by
    simpa using stackificationLiftBasedFunctorMap_isHomLift X G hG F (𝟙 T)
  have hFiber :
      (⟨stackificationLiftBasedFunctorMap X G hG F (𝟙 T), hMapLift⟩ : z ⟶ z) =
        𝟙 z := by
    apply stack_cover_hom_ext (J := J) X
      (stackificationLiftObjectCover (J := J) G hG y)
    intro I
    apply Functor.Fiber.hom_ext
    rw [stackificationLiftBasedFunctorMap_eq_core_comp_cart]
    simp [stackificationLiftBasedFunctorMap, y, z]
  exact congrArg (fun f => f.1) hFiber

end

end CategoryTheory
