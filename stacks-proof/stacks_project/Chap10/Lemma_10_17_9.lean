import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.17.9: for a commutative ring `R`, the prime spectrum `Spec(R)` is a spectral space.
In particular, it is quasi-compact, it has a basis of quasi-compact opens, and intersections of
quasi-compact opens are quasi-compact. Mathlib exposes this at the owner level as the canonical
instance `PrimeSpectrum.instSpectralSpace`, already for a commutative semiring; the textbook ring
statement is its special case. -/
recall PrimeSpectrum.instSpectralSpace
