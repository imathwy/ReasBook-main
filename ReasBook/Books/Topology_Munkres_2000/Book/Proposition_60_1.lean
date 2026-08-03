module

import Mathlib.Algebra.Group.Prod

/- Proposition 60.1. Given group homomorphisms `h : C →* A` and `k : C →* B`,
`h.prod k : C →* A × B` is the homomorphism sending `c` to `(h c, k c)`. -/
#check MonoidHom.prod
#check MonoidHom.prod_apply
