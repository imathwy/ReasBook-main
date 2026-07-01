import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.1.12: the natural order relation `≤` on `ℕ` is a linear order relation. -/
#check (inferInstance : IsLinearOrder ℕ (· ≤ ·))
