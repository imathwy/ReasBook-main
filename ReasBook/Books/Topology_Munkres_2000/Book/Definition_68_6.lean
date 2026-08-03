module

import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Defs

/- Definition 68.6: In a group, `y` is conjugate to `x` when
`y = c * x * c⁻¹` for some `c`; a subgroup is normal when it contains every
conjugate of each of its elements. -/
#check IsConj
#check isConj_iff
#check Subgroup.Normal
#check Subgroup.Normal.conj_mem
