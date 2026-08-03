module

import Mathlib.Data.Setoid.Basic

/- Exercise 3.4 (1): Equality of `f`-images is the kernel equivalence relation. -/
#check Setoid.ker
#check Setoid.ker_def

/- Exercise 3.4 (2): For surjective `f`, its kernel quotient is equivalent to the codomain. -/
#check Setoid.quotientKerEquivOfSurjective
#check Setoid.kerLift_mk
