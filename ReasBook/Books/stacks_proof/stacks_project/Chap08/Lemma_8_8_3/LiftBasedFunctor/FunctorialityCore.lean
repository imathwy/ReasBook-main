import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Base

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the vertical-and-comparison part of the descended arrow
formula, before appending the chosen cartesian pullback arrow in `X`. -/
noncomputable def stackificationLiftBasedFunctorMapCore
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' : S'.S} (φ : T ⟶ T') :
    stackificationLiftObjectGlued X G hG F
        (Functor.Fiber.mk (p := S'.p) (a := T) rfl) ⟶
      S'.p.map φ ^*[canonicalPullbackChoice X.p]
        stackificationLiftObjectGlued X G hG F
          (Functor.Fiber.mk (p := S'.p) (a := T') rfl) :=
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let pb : S'.p.Fiber (S'.p.obj T) :=
    stackificationLiftArrowPullbackTarget (S' := S') φ
  let v : y ⟶ pb :=
    stackificationLiftArrowVerticalFactor (S' := S') φ
  stackificationLiftVerticalMap X G hG F v ≫
    (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom

/-- Helper for Chap08 Lemma 8 8 3: the full descended arrow is the core part followed by the
chosen cartesian pullback arrow in `X`. -/
theorem stackificationLiftBasedFunctorMap_eq_core_comp_cart
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' : S'.S} (φ : T ⟶ T') :
    stackificationLiftBasedFunctorMap X G hG F φ =
      (stackificationLiftBasedFunctorMapCore X G hG F φ).1 ≫
        (canonicalPullbackChoice X.p).map (S'.p.map φ)
          (stackificationLiftObjectGlued X G hG F
          (Functor.Fiber.mk (p := S'.p) (a := T') rfl)) := by
  dsimp [stackificationLiftBasedFunctorMap, stackificationLiftBasedFunctorMapCore]
  let a :=
    (stackificationLiftVerticalMap X G hG F
      (stackificationLiftArrowVerticalFactor (S' := S') φ)).1
  let b :=
    (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom.1
  let c :=
    (canonicalPullbackChoice X.p).map (S'.p.map φ)
      (stackificationLiftObjectGlued X G hG F
        (Functor.Fiber.mk (p := S'.p) (a := T') rfl))
  change a ≫ b ≫ c = (a ≫ b) ≫ c
  rw [Category.assoc]

end

end CategoryTheory
