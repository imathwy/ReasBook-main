import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.4.67: the set of algebraic numbers in the complex field is countable. In mathlib,
this is the canonical theorem `Algebraic.countable` specialized to the `ℚ`-algebra `ℂ`. -/
#check (Algebraic.countable ℚ ℂ : { z : ℂ | IsAlgebraic ℚ z }.Countable)
