module

import Mathlib.Data.Prod.Lex

universe u v

public section

open Prod.Lex

variable (A : Type u) (B : Type v) [LT A] [LT B] {x y : A ×ₗ B}

/- Definition 3.13: The type `A ×ₗ B` is the product `A × B` equipped with the
dictionary order. -/
#check (A ×ₗ B)

/- The defining rule for the dictionary order. -/
#check (lt_iff :
  x < y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2)

end
