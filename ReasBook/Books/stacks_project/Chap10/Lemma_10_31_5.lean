import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommSemiring R] [IsNoetherianRing R]

/- Lemma 10.31.5: for the textbook case of a Noetherian ring, `Spec(R)` is a Noetherian
topological space in the sense of Topology, Definition 5.9.1. This is the canonical instance
`PrimeSpectrum.instNoetherianSpace`, which is available in mathlib under the weaker assumptions
`[CommSemiring R] [IsNoetherianRing R]`. -/
recall PrimeSpectrum.instNoetherianSpace

end
