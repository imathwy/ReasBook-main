import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.1.7: The equality relation on `ℕ` is an equivalence relation. -/
#check (eq_equivalence : Equivalence ((· = ·) : ℕ → ℕ → Prop))
