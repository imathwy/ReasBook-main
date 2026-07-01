import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.21.3: for a commutative ring `R`, every open and closed subset `U ⊆ Spec(R)` is of
the form `D(e)` for a unique idempotent `e ∈ R`. This is exactly the canonical theorem
`PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`. -/
recall PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen

/- Companion recall: the induced one-to-one correspondence between idempotents of `R` and clopen
subsets of `Spec(R)` is the canonical order isomorphism
`PrimeSpectrum.isIdempotentElemEquivClopens`. -/
recall PrimeSpectrum.isIdempotentElemEquivClopens

end
