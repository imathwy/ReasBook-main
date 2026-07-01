import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.63.5: if `R` is a Noetherian ring and `M` is a finite `R`-module, then
`associatedPrimes R M` is finite. This is exactly the owner theorem
`associatedPrimes.finite`. -/
recall associatedPrimes.finite

end
