import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.30.6: for a ring map `f : R →+* S`, the following are equivalent: the kernel of `f`
consists of nilpotent elements, every minimal prime ideal of `R` (equivalently every minimal point
of `Spec R`) lies in the image of `Spec(S) → Spec(R)`, and the image of `Spec(S) → Spec(R)` is
dense in `Spec(R)`. -/
-- Proof sketch: the owner abstraction is `DenseRange (comap f)`. Mathlib identifies this both with
-- `RingHom.ker f ≤ nilradical R` via `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical` and
-- with the minimal-prime condition via `PrimeSpectrum.denseRange_comap_iff_minimalPrimes`;
-- `PrimeSpectrum.isMin_iff` rewrites that owner theorem into the intrinsic minimal-point form.
@[stacks 00FL]
theorem denseRange_comap_tfae_ker_le_nilradical_minimalPrimes (f : R →+* S) :
    List.TFAE
      [ RingHom.ker f ≤ nilradical R,
        ∀ p : PrimeSpectrum R, IsMin p → p ∈ Set.range (comap f),
        DenseRange (comap f) ] := by
  tfae_have 1 ↔ 3 := (denseRange_comap_iff_ker_le_nilRadical f).symm
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h
      rw [denseRange_comap_iff_minimalPrimes]
      intro I hI
      exact h ⟨I, Ideal.minimalPrimes_isPrime hI⟩ (isMin_iff.mpr hI)
    · intro h p hp
      simpa using ((denseRange_comap_iff_minimalPrimes f).mp h) p.asIdeal (isMin_iff.mp hp)
  tfae_finish

end
