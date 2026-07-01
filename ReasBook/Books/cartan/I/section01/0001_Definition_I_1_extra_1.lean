import Mathlib

open scoped Polynomial

universe u

section

variable (K : Type u) [Semiring K]

/- Definition I.1-extra-1: the formal polynomials in one indeterminate over `K`
form the canonical polynomial type `K[X]`. This owner already lives at the semiring level. -/
#check K[X]

end

section

variable (K : Type u) [CommRing K]

/- The canonical commutative ring structure on the polynomial ring `K[X]`. -/
#check (inferInstance : CommRing K[X])

end

section

variable (K : Type u) [CommSemiring K]

/- The canonical unital `K`-algebra structure on the polynomial ring `K[X]`. -/
#check (inferInstance : Algebra K K[X])

end
