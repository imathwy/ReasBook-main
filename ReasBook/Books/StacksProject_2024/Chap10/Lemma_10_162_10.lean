import Mathlib
import stacks_project.Chap10.Definition_10_161_1
import stacks_project.Chap10.Definition_10_162_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: analytically unramified Noetherian local rings, their minimal-prime quotients,
  and the finite normalization (`N-1`) consequence;
- sampled owner declarations:
  `IsAnalyticallyUnramified`,
  `PrimeSpectrum.IsAnalyticallyUnramified`,
  `IsN1Ring`,
  and the canonical minimal-prime index type `minimalPrimes R`;
- best owner abstraction: the ambient owner is `IsAnalyticallyUnramified R`, while minimal-prime
  inputs should use the canonical `minimalPrimes R` owner rather than a separate prime-spectrum
  point together with a membership proof;
- primitive data vs. derived API: the primitive source data are the ring `R`, the owner
  hypothesis `[IsAnalyticallyUnramified R]`, and the minimal-prime family. Reducedness of `R`,
  analytic unramifiedness of each minimal-prime quotient, and the `N-1` finiteness statement are
  derived theorem-level API and should not be repackaged as extra structures.
-/

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

local instance (p : minimalPrimes R) : IsLocalRing (R ⧸ p.1) :=
  primeSpectrum_quotient_isLocalRing ⟨p.1, inferInstance⟩

-- Proof sketch: the completion map `R → AdicCompletion (maximalIdeal R) R` is faithfully flat, so
-- it is injective. If the completion is reduced, then a nilpotent element of `R` maps to `0`, hence
-- already vanishes in `R`.
/-- Lemma 10.162.10 (1): an analytically unramified Noetherian local ring is reduced. -/
theorem isReduced_of_isAnalyticallyUnramified [IsAnalyticallyUnramified R] :
    IsReduced R := sorry

-- Proof sketch: for a minimal prime `p`, use exactness of completion on the quotient `R ⧸ p.asIdeal`
-- to identify its completion with the quotient of the completion of `R`. Reducedness of the latter
-- modulo the extended minimal prime shows the quotient ring is analytically unramified.
/-- Lemma 10.162.10 (2): if `R` is analytically unramified, then every minimal prime quotient of
`R` is analytically unramified. -/
theorem minimalPrime_isAnalyticallyUnramified_of_isAnalyticallyUnramified
    [IsAnalyticallyUnramified R] (p : minimalPrimes R) :
    IsAnalyticallyUnramified (R ⧸ p.1) := sorry

-- Proof sketch: embed `R` into the product of the quotient rings by its minimal primes. Exactness
-- of completion gives an embedding of the completion of `R` into the product of the completions of
-- those quotients, and each factor is reduced by the analytic unramifiedness hypothesis.
/-- Lemma 10.162.10 (3): if `R` is reduced and each minimal prime quotient of `R` is analytically
unramified, then `R` is analytically unramified. -/
theorem isAnalyticallyUnramified_of_isReduced_of_minimalPrimes
    [IsReduced R]
    (hmin : ∀ p : minimalPrimes R, IsAnalyticallyUnramified (R ⧸ p.1)) :
    IsAnalyticallyUnramified R := sorry

-- Proof sketch: the completion of `R` is reduced, so its minimal-prime decomposition identifies
-- its total quotient ring with a finite product of fields. The integral closure over the completion
-- is finite by the domain case on each factor, and faithful flatness of completion descends a
-- finite generating set to the integral closure of `R` in `Q(R)`.
/-- Lemma 10.162.10 (4): if `R` is analytically unramified, then the integral closure of `R` in
its total ring of fractions is finite over `R`. -/
theorem integralClosure_fractionRing_finite_of_isAnalyticallyUnramified
    [IsAnalyticallyUnramified R] :
    Module.Finite R (integralClosure R (FractionRing R)) := sorry

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

-- Proof sketch: apply part (4) to obtain finiteness of the integral closure of `R` in
-- `FractionRing R`; this is exactly the defining field of `IsN1Ring R`.
/-- Lemma 10.162.10 (5): an analytically unramified Noetherian local domain is `N-1`. -/
theorem isN1Ring_of_isAnalyticallyUnramified [IsAnalyticallyUnramified R] :
    IsN1Ring R := sorry

end
