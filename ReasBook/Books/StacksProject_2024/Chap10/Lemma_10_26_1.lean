import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.26.1 (1): for a prime `𝔭 ⊆ R`, the closure of the singleton `{𝔭}` in `Spec R` is the
closed subset `V(𝔭)`. This is exactly the canonical theorem
`PrimeSpectrum.closure_singleton`. -/
recall PrimeSpectrum.closure_singleton

/- Lemma 10.26.1 (2): the irreducible closed subsets of `Spec R` are exactly the subsets `V(𝔭)`
for prime ideals `𝔭 ⊆ R`. Canonically, this is the inclusion-reversing order isomorphism
`PrimeSpectrum.pointsEquivIrreducibleCloseds`. -/
recall PrimeSpectrum.pointsEquivIrreducibleCloseds

/- Lemma 10.26.1 (3): the irreducible components of `Spec R` are exactly the subsets `V(𝔭)` for
minimal prime ideals `𝔭 ⊆ R`. Canonically, this is the inclusion-reversing order isomorphism
`minimalPrimes.equivIrreducibleComponents`. -/
recall minimalPrimes.equivIrreducibleComponents
