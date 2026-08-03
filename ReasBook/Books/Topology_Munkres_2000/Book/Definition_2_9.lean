module

public import Mathlib.Logic.Equiv.Defs

/- Definition 2.9: A bijective function has an inverse, characterized by the
unique preimage of each codomain element, and the inverse is bijective. -/
#check Equiv.ofBijective
#check Equiv.apply_eq_iff_eq_symm_apply
#check Equiv.ofBijective_apply_symm_apply
#check Equiv.ofBijective_symm_apply_apply
#check Equiv.bijective
