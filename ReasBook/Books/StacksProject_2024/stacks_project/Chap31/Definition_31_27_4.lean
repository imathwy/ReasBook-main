import Mathlib
import StacksProject_2024.Chap29.Definition_29_49_6
import StacksProject_2024.Chap31.Definition_31_23_3
import StacksProject_2024.Chap31.Definition_31_26_2
import StacksProject_2024.Chap31.Definition_31_26_5
import StacksProject_2024.Chap31.Definition_31_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]
variable [PrimeDivisorDiscreteValuationRings X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

-- Semantic recall:
-- * `lean_leansearch` surfaced only analytic meromorphic-divisor owners such as
--   `MeromorphicOn.divisor`, not the scheme-side Stacks interface needed here.
-- * Local Chapter 31 inspection found the concrete coefficient owner
--   `primeDivisorOrderOfVanishing` together with prime-divisor local-presentation data, but no
--   scheme-side bridge yet from those coefficients to the abstract divisor-class quotient `Cl(X)`.
-- * The source definition is therefore recorded here by its concrete coefficient function on prime
--   divisors, together with the coefficientwise well-definedness statement that is the exact input
--   needed to recover the divisor class once that bridge is available. The current owner for
--   meromorphic sections also does not expose a distinguished zero section, so the source's
--   nonzero side condition remains external to this coefficientwise interface.

/-- Definition 31.27.4 (1): let `X` be a locally Noetherian integral scheme, let `\mathcal L` be
an invertible `\mathcal O_X`-module, and let `s` be a meromorphic section of `\mathcal L`
equipped with prime-divisor local-presentation data. The Weil divisor
`\operatorname{div}_{\mathcal L}(s)` is recorded here by its coefficient function on prime
divisors, sending `Z` to `\operatorname{ord}_{Z,\mathcal L}(s)`. -/
@[stacks 0BE6]
def meromorphicSectionWeilDivisorCoeff
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (Z : PrimeDivisor X) : ℤ :=
  primeDivisorOrderOfVanishing s Z (data Z)

/-- Unfolding form of `meromorphicSectionWeilDivisorCoeff`. -/
theorem meromorphicSectionWeilDivisorCoeff_def
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (Z : PrimeDivisor X) :
    meromorphicSectionWeilDivisorCoeff ℒ s data Z =
      primeDivisorOrderOfVanishing s Z (data Z) := sorry

/-- The coefficient function attached to a meromorphic section has locally finite nonzero support
on `X`, so it determines a Weil divisor once the current coefficientwise surface is packed into the
Chapter 31 `Div(X)` owner. -/
theorem locallyFinite_meromorphicSectionWeilDivisorCoeff_ne_zero
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if meromorphicSectionWeilDivisorCoeff ℒ s data Z = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

/-- Definition 31.27.4 (2): the Weil divisor class associated to an invertible
`\mathcal O_X`-module is well defined because for any two meromorphic sections equipped with
prime-divisor local-presentation data, the associated coefficient functions differ by the
principal-divisor coefficients of a function-field unit. This is the coefficientwise form of the
source's `Cl(X)`-valued statement. -/
@[stacks 0BE6]
theorem exists_functionFieldUnit_sub_of_meromorphicSectionWeilDivisorCoeff
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s s' : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (data' : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s' Z) :
    ∃ f : X.functionFieldˣ,
      ∀ Z : PrimeDivisor X,
        meromorphicSectionWeilDivisorCoeff ℒ s data Z =
          meromorphicSectionWeilDivisorCoeff ℒ s' data' Z +
            principalWeilDivisorCoeff X (primeDivisorDiscreteValuationRing X) f Z :=
  sorry

end AlgebraicGeometry.Scheme
