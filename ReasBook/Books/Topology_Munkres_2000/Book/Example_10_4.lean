module

import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Prod.Lex

open Prod.Lex

/- Example 10.4 (1): The dictionary order well-orders the parenthesized triple
`ℕ+ × (ℕ+ × ℕ+)`. -/
#check (inferInstance : IsWellOrder (ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)) (· < ·))

/- Example 10.4 (2): The dictionary order well-orders the fourth power of `ℕ+`. -/
#check (inferInstance : IsWellOrder (Lex (Fin 4 → ℕ+)) (· < ·))

/- Example 10.4 (3): More generally, the dictionary order well-orders every
finite power of `ℕ+`. -/
#check fun n : ℕ ↦ (inferInstance : IsWellOrder (Lex (Fin n → ℕ+)) (· < ·))
