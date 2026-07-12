import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion`,
-- `AlgebraicGeometry.ValuativeCriterion.Existence`, and the equality
-- `AlgebraicGeometry.ValuativeCriterion.Existence.eq`; Chapter 26 precedent uses these canonical
-- scheme-morphism properties for the adjacent Stacks items.

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Proposition 26.20.6 (Valuative criterion of universal closedness): a quasi-compact morphism
of schemes is universally closed if and only if it satisfies the existence part of the valuative
criterion. -/
@[stacks 01KF]
theorem universallyClosed_iff_valuativeCriterionExistence [QuasiCompact f] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f := sorry

end

end AlgebraicGeometry
