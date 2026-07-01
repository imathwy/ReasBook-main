import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Lemma 10.17.4: for a ring homomorphism `φ : R →+* S`, the induced map
`PrimeSpectrum.comap φ : Spec(S) → Spec(R)` is continuous; this is the canonical theorem
`PrimeSpectrum.continuous_comap`. -/
recall PrimeSpectrum.continuous_comap

/- Lemma 10.17.4: the inverse image of a basic open `D(f)` under the induced map on spectra is
`D(φ(f))`; this is the canonical basic-open pullback theorem
`PrimeSpectrum.comap_basicOpen`. -/
recall PrimeSpectrum.comap_basicOpen

end
