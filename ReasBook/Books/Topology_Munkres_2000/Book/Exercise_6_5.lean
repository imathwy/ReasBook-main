module

import Mathlib.Data.Finite.Prod

/- Exercise 6.5: No in general, since an empty factor makes the product empty;
`Set.finite_prod` gives the exact criterion and implies both factors are finite
when both are nonempty. -/
#check Set.finite_prod
