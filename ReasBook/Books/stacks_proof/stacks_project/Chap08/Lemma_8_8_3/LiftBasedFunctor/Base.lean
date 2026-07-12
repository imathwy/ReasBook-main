import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Map

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the arrow formula for the lifted based functor lies over the
same base morphism as the original arrow in `S'`. -/
theorem stackificationLiftBasedFunctorMap_isHomLift
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' : S'.S} (φ : T ⟶ T') :
    X.p.IsHomLift (S'.p.map φ)
      (stackificationLiftBasedFunctorMap X G hG F φ) := by
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let y' : S'.p.Fiber (S'.p.obj T') :=
    Functor.Fiber.mk (p := S'.p) (a := T') rfl
  let pb : S'.p.Fiber (S'.p.obj T) :=
    stackificationLiftArrowPullbackTarget (S' := S') φ
  let v : y ⟶ pb :=
    stackificationLiftArrowVerticalFactor (S' := S') φ
  let a :=
    (stackificationLiftVerticalMap X G hG F v).1
  let b :=
    (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom.1
  let c :=
    (canonicalPullbackChoice X.p).map (S'.p.map φ)
      (stackificationLiftObjectGlued X G hG F y')
  have ha : X.p.IsHomLift (𝟙 (S'.p.obj T)) a := by
    dsimp [a]
    exact (stackificationLiftVerticalMap X G hG F v).2
  have hb : X.p.IsHomLift (𝟙 (S'.p.obj T)) b := by
    dsimp [b]
    exact (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom.2
  have hab : X.p.IsHomLift (𝟙 (S'.p.obj T)) (a ≫ b) := by
    exact IsHomLift.comp_of_lift_id (p := X.p) (S'.p.obj T) a b
  have hc : X.p.IsHomLift (S'.p.map φ) c := by
    dsimp [c]
    exact ((canonicalPullbackChoice X.p).isStronglyCartesian (S'.p.map φ)
      (stackificationLiftObjectGlued X G hG F y')).toIsHomLift
  dsimp [stackificationLiftBasedFunctorMap, y, y', pb, v, a, b, c]
  simpa only [Category.assoc] using
    (IsHomLift.comp_lift_id_left' (p := X.p) (S'.p.obj T) (a ≫ b)
      (S'.p.map φ) c)

end

end CategoryTheory
