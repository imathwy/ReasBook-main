module

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Prod.Lex

open Prod.Lex

/- Example 10.2: The dictionary order well-orders `ℕ+ × ℕ+`. -/
#check (inferInstance : WellFoundedLT (ℕ+ ×ₗ ℕ+))
