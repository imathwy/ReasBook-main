import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.2.5: The field of real numbers is a field extension of the field of
rational numbers, expressed by the canonical `Algebra ℚ ℝ` instance. -/
#check (inferInstance : Algebra ℚ ℝ)
