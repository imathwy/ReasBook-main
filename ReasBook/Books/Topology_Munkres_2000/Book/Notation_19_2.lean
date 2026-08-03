module

import Init

universe u v

variable (J : Type u) (X : Type v)

/- Notation 19.2: When every factor is `X`, the Cartesian product is the function
 type `J → X`. An element `x : J → X` may be viewed as a `J`-indexed tuple or as a
 function, with coordinate at `j : J` written `x j`. -/
#check (J → X)
#check (fun (x : J → X) (α : J) ↦ x α)
