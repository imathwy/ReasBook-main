import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.7.17: the natural strict order `<` on the set of natural numbers `ℕ` is a strict
total order. -/
#check (inferInstance : IsStrictTotalOrder ℕ (· < ·))
