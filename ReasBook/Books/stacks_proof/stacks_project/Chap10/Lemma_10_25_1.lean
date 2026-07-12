import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommSemiring R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-!
Domain-style sampling for zero-dimensional localizations at minimal primes:
- source-facing items:
  the nilpotence statement for elements of the maximal ideal of `Localization.AtPrime p.1`,
  and under `[IsReduced R]` the field corollary for the same localization.
- core/canonical owners inspected:
  `Ring.KrullDimLE.of_isLocalization`,
  `Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`,
  `Ring.KrullDimLE.isField_of_isReduced`,
  `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`.
- owner abstraction: the chapter already treats `minimalPrimes R` as the canonical minimal-prime
  owner, so the theorem should use that owner directly rather than a parallel `PrimeSpectrum`
  point plus a separate minimality proof.
- bridge/view layer here: the file remains a thin source-facing specialization that derives the
  local `Ring.KrullDimLE 0` instance from minimality of `p` and then reuses the canonical
  nilpotence and reduced-field criteria. No additional wrapper API is needed.
-/

/-- Lemma 10.25.1: if `p` is a minimal prime of `R`, then every element of the maximal ideal of
`Localization.AtPrime p.1` is nilpotent. -/
@[stacks 00EU]
theorem isNilpotent_of_mem_maximalIdeal_localizationAtPrime_of_minimalPrime
    (p : minimalPrimes R) {x : Localization.AtPrime p.1}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.1)) :
    IsNilpotent x := by
  letI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) :=
    Ring.KrullDimLE.of_isLocalization p.1 p.2 (Localization.AtPrime p.1)
  simpa using
    Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.2 hx

end

section

variable {R : Type u} [CommRing R] [IsReduced R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Lemma 10.25.1 companion: if `R` is reduced and `p` is a minimal prime of `R`, then
`Localization.AtPrime p.1` is a field. -/
@[stacks 00EU]
theorem isField_localizationAtPrime_of_minimalPrime (p : minimalPrimes R) :
    IsField (Localization.AtPrime p.1) := by
  letI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) :=
    Ring.KrullDimLE.of_isLocalization p.1 p.2 (Localization.AtPrime p.1)
  exact Ring.KrullDimLE.isField_of_isReduced

end
