import Mathlib
import StacksProject_2024.Chap10.Definition_10_67_1
import StacksProject_2024.Chap10.Definition_10_162_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
variable {x : R}

local notation "A" => R ⧸ Ideal.span (Set.singleton x)

/- Domain-style sampling:
- primary domain: analytically unramified Noetherian local domains, associated primes of
  principal quotients, and the no-embedded-primes condition on that quotient;
- sampled owner declarations:
  `IsAnalyticallyUnramified`,
  `PrimeSpectrum.IsAnalyticallyUnramified`,
  `embeddedAssociatedPrimes`,
  and `IsAssociatedPrime`;
- best owner abstraction: the theorem itself remains `source-facing`, but the quotient hypotheses
  should be expressed via the existing owner predicates `embeddedAssociatedPrimes R A = ∅` and
  `IsAssociatedPrime p.asIdeal A` rather than a parallel minimality condition and raw membership
  tests;
- primitive data vs. derived API: the primitive source data are the nonzero element `x` in the
  maximal ideal and the owner-level hypotheses on the quotient `A = R / xR`; the old “every
  associated prime is minimal” clause is derived bridge API for `embeddedAssociatedPrimes R A = ∅`.
-/

-- Proof sketch: let `R^∧` be the maximal-ideal completion of `R`. To prove it is reduced, take
-- `y : R^∧` with `y ^ 2 = 0`. Since `R / xR` has no embedded primes, the associated primes of
-- `R^∧ / xR^∧` are exactly the associated primes lying over the associated primes of `R / xR`.
-- For each such prime `q`, the corresponding localization `(R^∧)_q` is regular by Lemma
-- `10.162.11`, hence a domain by Lemma `10.106.2`, so `y` vanishes in every such localization.
-- Lemma `10.63.19` then shows `y = x y'`. Because `x` is a nonzerodivisor on the completion,
-- `y'` is again nilpotent; iterating and applying Krull intersection gives `y = 0`.
/-- Lemma 10.162.12: if `(R, 𝔪)` is a Noetherian local domain, `x ∈ 𝔪` is nonzero, `R / xR` has
no embedded primes, and every associated prime of `R / xR` is regular and analytically
unramified, then `R` is analytically unramified. -/
theorem isAnalyticallyUnramified_of_nonzero_in_maximalIdeal_of_associatedPrimes_quotient_regular
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p) :
    IsAnalyticallyUnramified R := sorry

end
