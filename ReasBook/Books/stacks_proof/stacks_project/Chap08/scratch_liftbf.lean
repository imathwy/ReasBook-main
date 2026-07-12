import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Base

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

noncomputable def scratchHbf
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    S'.toBasedCategory ⥤ᵇ X.toBasedCategory where
  toFunctor :=
    { obj := stackificationLiftBasedFunctorObj X G hG F
      map := fun φ => stackificationLiftBasedFunctorMap X G hG F φ
      map_id := by
        intro T
        dsimp [stackificationLiftBasedFunctorMap]
        set_option pp.all true in
        trace_state
        sorry
      map_comp := by
        intro A B D φ ψ
        sorry }
  w := by
    refine CategoryTheory.Functor.ext
      (fun T => stackificationLiftBasedFunctorObj_base X G hG F T) ?_
    intro T T' φ
    dsimp
    have hLift := stackificationLiftBasedFunctorMap_isHomLift X G hG F φ
    simpa using IsHomLift.fac' X.p (S'.p.map φ)
      (stackificationLiftBasedFunctorMap X G hG F φ)

end

end CategoryTheory
