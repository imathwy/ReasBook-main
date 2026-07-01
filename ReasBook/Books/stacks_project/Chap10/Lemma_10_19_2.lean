import Mathlib.RingTheory.Spectrum.Prime.RingHom

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.19.2: if the induced map `Spec S → Spec R` is surjective, then an element `x : R`
is a unit if and only if its image `φ x : S` is a unit. -/
-- Proof sketch: surjectivity of `PrimeSpectrum.comap φ` upgrades `φ` to the canonical owner
-- abstraction `IsLocalHom φ` via `IsLocalHom.of_comap_surjective`; then `isUnit_map_iff` is
-- exactly the needed equivalence, modulo the textbook order of the two sides.
theorem isUnit_iff_isUnit_map_of_comap_surjective
    (φ : R →+* S) (hφ : Function.Surjective (PrimeSpectrum.comap φ)) (x : R) :
    IsUnit x ↔ IsUnit (φ x) := by
  haveI : IsLocalHom φ := IsLocalHom.of_comap_surjective φ hφ
  exact (isUnit_map_iff φ x).symm
