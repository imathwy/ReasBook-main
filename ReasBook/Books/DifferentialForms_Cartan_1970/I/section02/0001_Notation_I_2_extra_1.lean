import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ComplexConjugate

/- Notation I.2-extra-1: mathlib's canonical complex-number API for conjugation, the norm square,
the modulus, and the real and imaginary part formulas is given by the scoped notation `conj`,
`Complex.normSq`, `Complex.norm_def`, `Complex.re_eq_add_conj`, and
`Complex.im_eq_sub_conj`. -/
#check (conj : ℂ →+* ℂ)
#check Complex.normSq
#check Complex.norm_def
#check Complex.re_eq_add_conj
#check Complex.im_eq_sub_conj
