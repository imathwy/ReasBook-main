import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Package

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the object-and-arrow descent construction produces an
admissible based functor on `S'` whose precomposition is based-isomorphic to the fixed source
morphism. -/
theorem stackificationLiftBasedFunctor_exists
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    ∃ Hbf : S'.toBasedCategory ⥤ᵇ X.toBasedCategory,
      ∃ _hcart : BasedFunctor.PreservesStronglyCartesian Hbf,
        Nonempty (BasedFunctor.comp G.toHom Hbf ≅ FibredCategoryMor.toBasedFunctor F) := by
  exact stackificationLiftBasedFunctor_exists_core X G hG F

end

end CategoryTheory
