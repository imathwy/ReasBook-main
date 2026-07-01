import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- Lemma 10.63.9: for a Noetherian ring `R` and an `R`-module `M`, the union of the associated
primes of `M` is exactly the set of elements of `R` that are zerodivisors on `M`. This is the
canonical mathlib theorem `biUnion_associatedPrimes_eq_zero_divisors`. -/
recall biUnion_associatedPrimes_eq_zero_divisors

end
