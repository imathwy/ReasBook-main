import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Reduced

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R]

/-
Definition 10.37.11 is `source-facing`: the chapter needs a ring-level owner predicate saying
that every prime localization is a normal domain. For each localization, the `core/canonical`
owner abstractions are mathlib's `IsDomain` and `IsIntegrallyClosed`; this file packages those
local conditions over all primes. The prime-spectrum and prime-ideal consequences below are
derived `bridge/view` API.
-/
/-- Definition 10.37.11: a commutative ring is normal if for every prime ideal `p`, the
localization `Localization.AtPrime p` is a normal domain. -/
class IsNormalRing (R : Type u) [CommRing R] : Prop where
  isNormalLocalizationAtPrime :
    ∀ p : PrimeSpectrum R,
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

/-- An integrally closed domain is a normal ring. -/
instance [IsDomain R] [IsIntegrallyClosed R] : IsNormalRing R where
  isNormalLocalizationAtPrime := fun p ↦ by
    refine ⟨?_, ?_⟩
    · exact IsLocalization.isDomain_of_atPrime (Localization.AtPrime p.asIdeal) p.asIdeal
    · letI : IsDomain (Localization.AtPrime p.asIdeal) :=
        IsLocalization.isDomain_of_atPrime (Localization.AtPrime p.asIdeal) p.asIdeal
      exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
        p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

/-- A normal ring has domain localizations at all points of `PrimeSpectrum R`. -/
theorem isDomain_localizationAtPrime (p : PrimeSpectrum R) [IsNormalRing R] :
    IsDomain (Localization.AtPrime p.asIdeal) :=
  (IsNormalRing.isNormalLocalizationAtPrime p).1

/-- A normal ring has integrally closed localizations at all points of `PrimeSpectrum R`. -/
theorem isIntegrallyClosed_localizationAtPrime (p : PrimeSpectrum R) [IsNormalRing R] :
    IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
  (IsNormalRing.isNormalLocalizationAtPrime p).2

instance [IsNormalRing R] : IsReduced R := by
  refine isReduced_ofLocalizationMaximal R fun p _ ↦ ?_
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  letI : IsDomain (Localization.AtPrime p) := by
    simpa using isDomain_localizationAtPrime q
  infer_instance

attribute [instance] isDomain_localizationAtPrime isIntegrallyClosed_localizationAtPrime

/-- A normal ring has normal localizations at all prime ideals. -/
instance (p : Ideal R) [p.IsPrime] [IsNormalRing R] :
    IsDomain (Localization.AtPrime p) := by
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  simpa using isDomain_localizationAtPrime q

/-- A normal ring has integrally closed localizations at all prime ideals. -/
instance (p : Ideal R) [p.IsPrime] [IsNormalRing R] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  simpa using isIntegrallyClosed_localizationAtPrime q
