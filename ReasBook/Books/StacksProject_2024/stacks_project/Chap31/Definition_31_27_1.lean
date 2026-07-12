import StacksProject_2024.Chap31.Definition_31_23_3
import StacksProject_2024.Chap31.Definition_31_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪

-- Semantic recall: `lean_leansearch` surfaced the canonical valuation owner `Ring.ordFrac` and
-- the generic-point API `PrimeDivisor.genericPoint`. Chapter 31 already owns scheme-side prime
-- divisors as `AlgebraicGeometry.PrimeDivisor X`, so the source-facing owner here is the order of
-- vanishing along a prime divisor, with local presentation data kept as the bridge to
-- `Ring.ordFrac`.

/-- A local presentation of a regular meromorphic section of `\mathcal L` along the prime divisor
`Z`, recorded by the quotient `s / s_\xi` in the fraction field of the local ring at the generic
point `\xi` coming from a chosen generator `s_\xi` of `\mathcal L_\xi`. -/
structure PrimeDivisorOrderPresentation
    (ℒ : ModX) (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (Z : PrimeDivisor X) where
  /-- The generic-point stalk of `Z` has Krull dimension at most `1`, so `Ring.ordFrac` applies
  to fractions in this stalk. -/
  krullDimLE : Ring.KrullDimLE 1 Z.genericPointStalk
  /-- The quotient `s / s_\xi` in the fraction field of the local ring `\mathcal O_{X, \xi}`. -/
  quotient : FractionRing Z.genericPointStalk

/-- The order of vanishing attached to a quotient in the fraction field of the generic-point
stalk of a prime divisor. This is the canonical `Ring.ordFrac` owner used by
`primeDivisorOrderOfVanishing`. -/
def primeDivisorOrderOfVanishingInGenericPointStalk
    (Z : PrimeDivisor X) (quotient : FractionRing Z.genericPointStalk)
    (krullDimLE : Ring.KrullDimLE 1 Z.genericPointStalk) : ℤ :=
  letI := krullDimLE
  WithZero.log (Ring.ordFrac Z.genericPointStalk quotient)

/-- Unfolding form of `primeDivisorOrderOfVanishingInGenericPointStalk`. -/
theorem primeDivisorOrderOfVanishingInGenericPointStalk_def
    (Z : PrimeDivisor X) (quotient : FractionRing Z.genericPointStalk)
    (krullDimLE : Ring.KrullDimLE 1 Z.genericPointStalk) :
    primeDivisorOrderOfVanishingInGenericPointStalk Z quotient krullDimLE =
      letI := krullDimLE
      WithZero.log (Ring.ordFrac Z.genericPointStalk quotient) := by
  rfl

/-- Definition 31.27.1: for a locally Noetherian integral scheme `X`, an invertible
`\mathcal O_X`-module `\mathcal L`, a regular meromorphic section `s` of `\mathcal L`, and a
prime divisor `Z \subset X`, the order of vanishing along `Z` is the order of vanishing in the
local ring at the generic point `\xi` of `Z` of the quotient `s / s_\xi`, computed from any
chosen local presentation data `s_\xi` and `s / s_\xi`. -/
def primeDivisorOrderOfVanishing
    {ℒ : ModX} (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (Z : PrimeDivisor X) (data : PrimeDivisorOrderPresentation ℒ s Z) : ℤ :=
  primeDivisorOrderOfVanishingInGenericPointStalk Z data.quotient data.krullDimLE

/- Unfolding form of `primeDivisorOrderOfVanishing`. -/
theorem primeDivisorOrderOfVanishing_def
    {ℒ : ModX} {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    (data : PrimeDivisorOrderPresentation ℒ s Z) :
    primeDivisorOrderOfVanishing s Z data =
      primeDivisorOrderOfVanishingInGenericPointStalk Z data.quotient data.krullDimLE := by
  rfl

/-- A local presentation computes the order of vanishing through its quotient in the
generic-point stalk. -/
theorem PrimeDivisorOrderPresentation.orderOfVanishing_eq
    {ℒ : ModX} {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    (data : PrimeDivisorOrderPresentation ℒ s Z) :
    primeDivisorOrderOfVanishing s Z data =
      primeDivisorOrderOfVanishingInGenericPointStalk Z data.quotient data.krullDimLE :=
  primeDivisorOrderOfVanishing_def data

end AlgebraicGeometry.Scheme
