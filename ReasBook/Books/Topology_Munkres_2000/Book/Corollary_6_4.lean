module

import Mathlib.Logic.Denumerable

/- Corollary 6.4. The type `ℕ+` of positive integers is not finite. -/
#check (Infinite.not_finite : ¬ Finite ℕ+)
