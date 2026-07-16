import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.1.17: the natural order relation `<` on `ℕ` is a strict total order relation. -/
#check (inferInstance : IsStrictTotalOrder ℕ (· < ·))
