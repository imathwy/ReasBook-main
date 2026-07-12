import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact canonical mathlib theorem
-- `AlgebraicGeometry.IsSeparated.valuativeCriterion`, with conclusion
-- `ValuativeCriterion.Uniqueness f`.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 26.22.1: if a morphism of schemes is separated, then it satisfies the uniqueness
part of the valuative criterion. -/
@[stacks 01KZ]
theorem valuativeCriterionUniqueness_of_isSeparated [IsSeparated f] :
    ValuativeCriterion.Uniqueness f := sorry

end AlgebraicGeometry
