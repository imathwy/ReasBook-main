import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (p : Ideal R) [p.IsPrime]

/-- Example 10.18.2: if `R` is a local ring and `p` is a prime ideal different from the maximal
ideal, then the canonical map `R → Localization.AtPrime p` is not a local ring homomorphism. -/
-- Proof sketch: if the localization map were local, then the maximal ideal of
-- `Localization.AtPrime p` would comap to the maximal ideal of `R`. But for localization at a
-- prime, that same comap is exactly `p`, so `p = maximalIdeal R`, contradicting the hypothesis.
theorem localization_atPrime_not_isLocalHom_of_ne_maximalIdeal
    (hp : p ≠ maximalIdeal R) :
    ¬ IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
  intro h
  letI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := h
  exact hp <| by
    simpa [Localization.AtPrime.comap_maximalIdeal] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R (Localization.AtPrime p)))

end
