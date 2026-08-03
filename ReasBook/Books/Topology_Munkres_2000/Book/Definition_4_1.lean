module

import Init

universe u

variable (A : Type u)

/- Definition 4.1: A binary operation on a type `A` is a function of type
`A × A → A`. -/
#check (A × A → A)
