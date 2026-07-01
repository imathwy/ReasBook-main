import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing

/-- Example 10.35.16: under the localization map `ℤ → ℚ`, identifying `ℚ` with the localization
of `ℤ` at all nonzero integers, the closed point of `Spec(ℚ)` maps to the generic point of
`Spec(ℤ)`. -/
theorem int_to_rat_comap_closedPoint_eq_genericPoint :
    comap (algebraMap ℤ ℚ) (closedPoint ℚ) = (⊥ : PrimeSpectrum ℤ) := by
  rw [show closedPoint ℚ = (⊥ : PrimeSpectrum ℚ) by
    exact Subsingleton.elim _ _]
  simpa [PrimeSpectrum.ext_iff] using
    (Ideal.comap_bot_of_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ) :
      Ideal.comap (algebraMap ℤ ℚ) ⊥ = (⊥ : Ideal ℤ))
