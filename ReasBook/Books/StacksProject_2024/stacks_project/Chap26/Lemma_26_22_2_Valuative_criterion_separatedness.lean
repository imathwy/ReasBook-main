import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact canonical mathlib theorem
-- `AlgebraicGeometry.IsSeparated.of_valuativeCriterion`, with assumptions
-- `[QuasiSeparated f]` and `ValuativeCriterion.Uniqueness f`.

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 26.22.2 (Valuative criterion separatedness): if a morphism of schemes is
quasi-separated and satisfies the uniqueness part of the valuative criterion, then it is
separated. -/
@[stacks 01L0]
theorem isSeparated_of_quasiSeparated_valuativeCriterionUniqueness [QuasiSeparated f]
    (hf : ValuativeCriterion.Uniqueness f) : IsSeparated f := sorry

end

end AlgebraicGeometry
