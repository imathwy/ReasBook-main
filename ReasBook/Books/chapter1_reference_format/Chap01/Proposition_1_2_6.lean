import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1.2.6: the relation `<` on `ℝ` is a strict total order relation. -/
#check (inferInstance : IsStrictTotalOrder ℝ (· < ·))
