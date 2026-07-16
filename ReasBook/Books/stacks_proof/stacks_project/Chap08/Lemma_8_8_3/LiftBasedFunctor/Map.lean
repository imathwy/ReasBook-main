import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the morphism formula for the eventual descended based
functor. A total arrow is factored in `S'` as a vertical arrow followed by the chosen cartesian
pullback arrow; the lift sends the vertical factor by descent gluing and the cartesian factor by
the pullback-compatibility comparison for glued objects. -/
noncomputable def stackificationLiftBasedFunctorMap
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' : S'.S} (φ : T ⟶ T') :
    stackificationLiftBasedFunctorObj X G hG F T ⟶
      stackificationLiftBasedFunctorObj X G hG F T' :=
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let y' : S'.p.Fiber (S'.p.obj T') :=
    Functor.Fiber.mk (p := S'.p) (a := T') rfl
  let pb : S'.p.Fiber (S'.p.obj T) :=
    stackificationLiftArrowPullbackTarget (S' := S') φ
  let v : y ⟶ pb :=
    stackificationLiftArrowVerticalFactor (S' := S') φ
  (stackificationLiftVerticalMap X G hG F v).1 ≫
    (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom.1 ≫
      (canonicalPullbackChoice X.p).map (S'.p.map φ)
        (stackificationLiftObjectGlued X G hG F y')

end

end CategoryTheory
