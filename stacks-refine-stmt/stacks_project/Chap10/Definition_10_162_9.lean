import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The quotient of a local ring by a prime ideal is again a local ring. -/
instance primeSpectrum_quotient_isLocalRing (p : PrimeSpectrum R) : IsLocalRing (R ⧸ p.asIdeal) :=
  sorry

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Definition 10.162.9: a local ring is analytically unramified when its completion with
respect to the maximal ideal is reduced. -/
@[mk_iff isAnalyticallyUnramified_iff]
class IsAnalyticallyUnramified : Prop where
  completion_isReduced : IsReduced (AdicCompletion (maximalIdeal R) R)

attribute [instance] IsAnalyticallyUnramified.completion_isReduced

end

section

variable (K : Type u) [Field K]

/-- Fields are analytically unramified. -/
instance : IsAnalyticallyUnramified K := sorry

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace PrimeSpectrum

/-- A prime ideal of a local ring is analytically unramified when the quotient ring by
that prime ideal is analytically unramified. -/
def IsAnalyticallyUnramified (p : PrimeSpectrum R) : Prop :=
  _root_.IsAnalyticallyUnramified (R ⧸ p.asIdeal)

end PrimeSpectrum

end
