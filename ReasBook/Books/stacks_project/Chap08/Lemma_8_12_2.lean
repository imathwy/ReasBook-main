import Mathlib
import stacks_project.Chap08.Definition_8_4_1
import stacks_project.Chap08.Lemma_8_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: the canonical fiber pseudofunctor of the pullback projection along
`u` inherits the stack condition from `p` over `(D, K)`. -/
theorem pullback_projection_canonicalFiber_isStack
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] :
    Pseudofunctor.IsStack (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J := by
  sorry

/-- Lemma 8.12.2: if `u : C ⥤ D` is a continuous functor of sites and `X` is a stack over
`(D, K)` with projection `p : S ⥤ D`, then the pullback category `u^p S`, modeled by the
categorical pullback `CategoricalPullback u p`, is a stack over `(C, J)`. -/
theorem continuous_pullback_isStackOnSite
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] :
    IsStackOnSite J (CategoricalPullback.π₁ u p) := by
  letI :
      Pseudofunctor.IsStack (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J :=
    pullback_projection_canonicalFiber_isStack (J := J) (K := K) u p
  infer_instance

end

end CategoryTheory
