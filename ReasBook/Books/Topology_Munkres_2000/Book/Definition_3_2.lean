module

import Mathlib.Data.Rel

universe u

variable (A : Type u)

/- Definition 3.2: A relation on a type `A` is a subset of the cartesian product
`A × A`. -/
#check SetRel A A
