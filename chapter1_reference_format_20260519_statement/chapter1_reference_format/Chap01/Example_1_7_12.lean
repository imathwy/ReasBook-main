import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.7.12: the natural order relation `≤` on `ℕ` is a total order relation. -/
#check (inferInstance : IsLinearOrder ℕ (· ≤ ·))
