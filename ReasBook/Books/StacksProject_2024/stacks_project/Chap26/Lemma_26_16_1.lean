import Mathlib.AlgebraicGeometry.Limits

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical finite-limit owner
-- `AlgebraicGeometry.instHasFiniteLimitsScheme`; `Mathlib.AlgebraicGeometry.Limits` supplies this
-- from the terminal scheme and scheme pullbacks, matching the source's "in other words" clause.

/-- Lemma 26.16.1: the category of schemes has a final object, products and fibre products;
equivalently, it has finite limits. -/
@[stacks 01JM]
theorem scheme_hasFiniteLimits : HasFiniteLimits Scheme.{u} := sorry

end AlgebraicGeometry
