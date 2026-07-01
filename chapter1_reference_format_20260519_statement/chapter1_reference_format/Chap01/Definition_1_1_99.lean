import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section CoprimeIdeals

variable (R : Type u) [CommSemiring R] (I J : Ideal R)

/- Definition 1.1.99: two ideals `I` and `J` are coprime when their sum is the unit ideal; this
is the canonical predicate `IsCoprime I J`. For ideals, mathlib's owner already lives over the
weakest ambient assumption `[CommSemiring R]`, so this recall is stated at that canonical level. -/
#check (IsCoprime I J)

/- The textbook condition `I + J = A` is expressed in mathlib as `I + J = 1`, and it is exactly
the characterization `Ideal.isCoprime_iff_add`. -/
#check (Ideal.isCoprime_iff_add : IsCoprime I J ↔ I + J = 1)

end CoprimeIdeals
