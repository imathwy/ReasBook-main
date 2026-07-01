import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Lemma 10.41.5 (00HY): if the image of `Spec(S) → Spec(R)` is stable under specialization, then
it is closed. This is exactly the canonical prime-spectrum theorem
`PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`. -/
recall PrimeSpectrum.isClosed_range_of_stableUnderSpecialization

end
