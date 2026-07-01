import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommSemiring R]

/- Lemma 10.17.8: the Stacks Project states that for a ring `R`, the spectrum `Spec(R)` is
quasi-compact. Mathlib exposes this at the owner level as the canonical instance
`PrimeSpectrum.compactSpace` of `CompactSpace (PrimeSpectrum R)`, already for a commutative
semiring; the textbook ring statement is its special case. -/
recall PrimeSpectrum.compactSpace

end
