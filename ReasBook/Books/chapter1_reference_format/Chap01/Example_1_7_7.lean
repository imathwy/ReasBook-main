import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.7.7: the binary relation `=` on the natural numbers `ℕ` is an equivalence
relation. -/
#check (eq_equivalence : Equivalence ((· = ·) : ℕ → ℕ → Prop))
