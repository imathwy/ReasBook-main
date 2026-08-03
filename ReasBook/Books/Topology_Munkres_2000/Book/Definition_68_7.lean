module

import Mathlib.Algebra.Group.Subgroup.Basic

/- Definition 68.7: For a subset `S` of a group `G`, the intersection of all
normal subgroups containing `S` is itself normal and is the least normal
subgroup of `G` containing `S`. -/
#check Subgroup.normalClosure
#check Subgroup.normalClosure_eq_iInf
#check Subgroup.normalClosure_normal
#check Subgroup.subset_normalClosure
#check Subgroup.normalClosure_le_normal
