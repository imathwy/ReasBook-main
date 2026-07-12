import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.1.21: the natural numbers together with addition form an additive commutative
monoid, with identity element `0`. -/
#check (inferInstance : AddCommMonoid ℕ)
