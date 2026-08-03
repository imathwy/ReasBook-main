module

import Mathlib.Algebra.Group.Prod

/- Definition 60.2: If `A` and `B` are groups, then `A × B` has the canonical
group structure with multiplication `(a, b) * (a', b') = (a * a', b * b')`. -/
#check Prod.instGroup
#check Prod.mk_mul_mk
