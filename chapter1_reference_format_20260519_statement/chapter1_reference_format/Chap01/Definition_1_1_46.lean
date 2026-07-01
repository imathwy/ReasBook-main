import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section PrincipalIdeal

variable (R : Type u) [CommSemiring R] (I : Ideal R)

/- Definition 1.1.46 (1): for an ideal `I` of a commutative ring `R`, being principal is the
canonical property `I.IsPrincipal`; equivalently, there exists `x : R` with
`I = Ideal.span {x}`, traditionally written `(x)`. -/
#check I.IsPrincipal
/- The canonical expansion is the upstream theorem `Submodule.isPrincipal_iff`, specialized to
ideals. -/
#check Submodule.isPrincipal_iff I

end PrincipalIdeal

section PrincipalIdealDomain

variable (R : Type u) [CommRing R] [IsDomain R]

/- Definition 1.1.46 (2): for a commutative integral domain `R`, the textbook notion of
principal ideal domain is the canonical property `IsPrincipalIdealRing R`, meaning that every
ideal of `R` is principal. -/
recall IsPrincipalIdealRing (R : Type u) [Semiring R] : Prop

/- The canonical expansion of `IsPrincipalIdealRing R` is that every ideal of `R` is principal. -/
#check isPrincipalIdealRing_iff R

end PrincipalIdealDomain
