import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.SourceComparison

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the remaining small package for the descended based functor.

The object, arrow, and base-lift formulas are already defined in the imported files.  The
remaining work is to prove their functoriality, cartesian preservation, and source comparison
isomorphism. -/
theorem stackificationLiftBasedFunctor_exists_core
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    ∃ Hbf : S'.toBasedCategory ⥤ᵇ X.toBasedCategory,
      ∃ _hcart : BasedFunctor.PreservesStronglyCartesian Hbf,
        Nonempty (BasedFunctor.comp G.toHom Hbf ≅ FibredCategoryMor.toBasedFunctor F) := by
  -- Once the functoriality and compatibility helpers above are available, the final owner
  -- statement is just packaging of the descended based functor.
  refine ⟨stackificationLiftBasedFunctor X G hG F, ?_⟩
  refine ⟨stackificationLiftBasedFunctor_preservesStronglyCartesian X G hG F, ?_⟩
  exact stackificationLiftBasedFunctor_sourceIso_nonempty X G hG F

end

end CategoryTheory
