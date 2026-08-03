module

import Mathlib.Algebra.Group.Subgroup.Basic

/- Definition 81.2: If `H` is a subgroup of a group `G`, its normalizer is the
subgroup of elements `g` such that conjugation by `g` sends `H` to itself. -/
#check Subgroup.normalizer
#check Subgroup.mem_normalizer_iff_conj_image_eq
