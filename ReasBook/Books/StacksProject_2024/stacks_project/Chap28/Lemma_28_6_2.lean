import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

-- Semantic recall / owner choice:
-- - source-facing layer: the affine-scheme Jacobson criterion for `Spec R`;
-- - core/canonical owner: `PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`;
-- - bridge: identify the affine-scheme surface `Spec R` with the prime-spectrum Jacobson owner.

/-- Lemma 28.6.2: an affine scheme `Spec R` is Jacobson if and only if the ring `R` is Jacobson. -/
@[stacks 01P3]
theorem jacobsonSpace_spec_iff_isJacobsonRing :
    JacobsonSpace (Spec R) ↔ IsJacobsonRing R := by
  change JacobsonSpace (Spec.topObj R) ↔ IsJacobsonRing R
  simpa [Spec.topObj_forget] using
    (PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace :
      IsJacobsonRing R ↔ JacobsonSpace (PrimeSpectrum R)).symm

end AlgebraicGeometry
