module

import Mathlib.Algebra.Group.Subgroup.Basic

/- Proposition 81.1: For a subgroup `H` of a group `G`, its normalizer
`H.normalizer` contains `H` as a normal subgroup and is the largest subgroup of
`G` with this property. -/
#check Subgroup.normalizer
#check Subgroup.le_normalizer
#check Subgroup.normal_in_normalizer
#check Subgroup.maximal_normal_subgroupOf_normalizer
#check Subgroup.normal_subgroupOf_iff_le_normalizer
