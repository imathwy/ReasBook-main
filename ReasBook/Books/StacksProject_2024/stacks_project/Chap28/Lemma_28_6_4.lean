import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry PrimeSpectrum IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- - `lean_leansearch` returned the canonical local-ring punctured-spectrum owner
--   `IsLocalRing.closedPoint` together with `IsLocalRing.isClosed_singleton_closedPoint`, and the
--   affine-spectrum opens `PrimeSpectrum.zeroLocus` / `PrimeSpectrum.basicOpen`;
-- - `Chap28/Definition_28_6_1` fixes the scheme-level predicate as `JacobsonSpace`;
-- - `Chap28/Lemma_28_6_3` and `Chap15/Lemma_15_10_5` provide the expected local-Jacobson and
--   Jacobson-radical localization patterns, so the present item is formalized as three atomic
--   Jacobson open-subscheme examples.

variable {R : Type u} [CommRing R]

/-- Lemma 28.6.4 (1): if `(R, 𝔪)` is a Noetherian local ring, then the punctured spectrum
`Spec(R) \ {𝔪}` is a Jacobson scheme. -/
@[stacks 02IM]
theorem jacobsonSpace_puncturedSpectrum_of_isNoetherianRing
    [IsLocalRing R] [IsNoetherianRing R] :
    JacobsonSpace
      (Scheme.Opens.toScheme
        (⟨({closedPoint R} : Set (PrimeSpectrum R))ᶜ,
          (isClosed_singleton_closedPoint R).isOpen_compl⟩ : (Spec (.of R)).Opens)) := sorry

/-- Lemma 28.6.4 (2): if `R` is Noetherian, then `Spec(R) \ V(rad(R))` is a Jacobson scheme,
written canonically using the Jacobson radical `Ring.jacobson R`. -/
@[stacks 02IM]
theorem jacobsonSpace_spec_compl_zeroLocus_ringJacobson
    [IsNoetherianRing R] :
    JacobsonSpace
      (Scheme.Opens.toScheme
        (⟨(PrimeSpectrum.zeroLocus ((Ring.jacobson R : Ideal R) : Set R))ᶜ,
          (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (.of R)).Opens)) := sorry

/-- Lemma 28.6.4 (3): if `R` is Noetherian and `I ≤ Ring.jacobson R`, then
`Spec(R) \ V(I)` is a Jacobson scheme. This is the canonical Zariski-pair form. -/
@[stacks 02IM]
theorem jacobsonSpace_spec_compl_zeroLocus_of_le_ringJacobson
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    JacobsonSpace
      (Scheme.Opens.toScheme
        (⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
          (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (.of R)).Opens)) := sorry

end AlgebraicGeometry
