module

import Init

universe u v

variable (J : Type u) (X : Type v)

/- Definition 19.2: A `J`-tuple of elements of `X` is a function `x : J → X`.
Its `α`th coordinate is `x α`, and the type of all such tuples is `J → X`. -/
#check (J → X)
#check (fun (x : J → X) (α : J) ↦ x α)
