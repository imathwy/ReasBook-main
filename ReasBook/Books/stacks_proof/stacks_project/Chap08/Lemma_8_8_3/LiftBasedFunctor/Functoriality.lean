import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.Identity
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.Composition

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the underlying functor of the descended based functor. -/
noncomputable def stackificationLiftBasedFunctorToFunctor
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    S'.S ⥤ X.S where
  obj := stackificationLiftBasedFunctorObj X G hG F
  map := fun φ => stackificationLiftBasedFunctorMap X G hG F φ
  map_id := stackificationLiftBasedFunctorMap_id X G hG F
  map_comp := fun φ ψ => stackificationLiftBasedFunctorMap_comp X G hG F φ ψ

/-- Helper for Chap08 Lemma 8 8 3: the descended functor commutes with the projections to the
base category. -/
theorem stackificationLiftBasedFunctorToFunctor_w
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    stackificationLiftBasedFunctorToFunctor X G hG F ⋙ X.p = S'.p := by
  -- The object part was chosen in the same fiber, and the arrow formula was already proved to
  -- lift the same base morphism as the original arrow in `S'`.
  refine CategoryTheory.Functor.ext
    (fun T => stackificationLiftBasedFunctorObj_base X G hG F T) ?_
  intro T T' φ
  dsimp [stackificationLiftBasedFunctorToFunctor]
  have hLift := stackificationLiftBasedFunctorMap_isHomLift X G hG F φ
  simpa using IsHomLift.fac' X.p (S'.p.map φ)
    (stackificationLiftBasedFunctorMap X G hG F φ)

/-- Helper for Chap08 Lemma 8 8 3: the descended object-and-arrow formula as a based functor. -/
noncomputable def stackificationLiftBasedFunctor
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    S'.toBasedCategory ⥤ᵇ X.toBasedCategory where
  toFunctor := stackificationLiftBasedFunctorToFunctor X G hG F
  w := stackificationLiftBasedFunctorToFunctor_w X G hG F

end

end CategoryTheory
