module

import Init

universe u v

variable (J : Type u) (X : Type v)

/- Definition 19.3: A `J`-tuple of elements of `X` is a function `J → X`.
For `x : J → X` and `α : J`, the value `x α` is the `α`-coordinate of `x`. -/
#check (J → X)
#check (fun (x : J → X) (α : J) ↦ x α)
