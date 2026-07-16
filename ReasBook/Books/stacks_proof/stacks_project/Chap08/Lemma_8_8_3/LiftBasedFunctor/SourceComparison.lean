import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.SourceComparisonNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.SourceComparisonHomLift

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: after precomposition by the stackification morphism, the
descended based functor is based-isomorphic to the original source morphism. -/
theorem stackificationLiftBasedFunctor_sourceIso_nonempty
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    Nonempty
      (BasedFunctor.comp G.toHom (stackificationLiftBasedFunctor X G hG F) ≅
        FibredCategoryMor.toBasedFunctor F) := by
  refine ⟨BasedNatIso.mkNatIso ?nat ?homLift⟩
  · refine NatIso.ofComponents
      (fun T => stackificationLiftBasedFunctorObj_sourceIso X G hG F T) ?_
    intro T T' φ
    exact stackificationLiftBasedFunctor_sourceIso_naturality X G hG F φ
  · intro T
    change X.p.IsHomLift (𝟙 (S.p.obj T))
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T).hom
    exact stackificationLiftBasedFunctorObj_sourceIso_isHomLift X G hG F T

end

end CategoryTheory
