module

public import Mathlib.Data.Prod.Lex

variable (α β : Type*) [LinearOrder α] [LinearOrder β]

/- Exercise 3.9: The dictionary order on `α × β`, for linearly ordered types
`α` and `β`, is an order relation. -/
#check (inferInstance : IsStrictTotalOrder (α ×ₗ β) (· < ·))
