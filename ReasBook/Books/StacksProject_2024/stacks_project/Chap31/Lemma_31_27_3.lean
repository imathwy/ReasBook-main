import Mathlib
import StacksProject_2024.Chap29.Definition_29_49_6
import StacksProject_2024.Chap31.Definition_31_23_7
import StacksProject_2024.Chap31.Definition_31_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

-- Semantic recall:
-- * `lean_leansearch` surfaced only analytic meromorphic-divisor owners such as
--   `MeromorphicOn.divisor`.
-- * Local Chapter 31 inspection found no common scheme-side owner simultaneously packaging the
--   order-of-vanishing surface from `Definition_31_27_1` and the Weil-divisor surface from
--   `Definition_31_26_2`.
-- * The source statement is therefore recorded here in coefficientwise form on the current
--   Chapter 31 prime-divisor owner.

/-- Lemma 31.27.3: let `X` be a locally Noetherian integral scheme, let `\mathcal L` be an
invertible `\mathcal O_X`-module, and let `s, s' ∈ \mathcal K_X(\mathcal L)` be nonzero
meromorphic sections. Then there exists a unit `f ∈ R(X)ˣ`, representing the quotient `s / s'`,
such that for every prime divisor `Z` and every chosen local presentations of `s` and `s'` along
`Z`, the difference of the orders of vanishing is the order of vanishing of `f` at `Z`. This is
the coefficientwise form of the Weil-divisor identity
`\sum \operatorname{ord}_{Z,\mathcal L}(s)[Z] = \sum \operatorname{ord}_{Z,\mathcal L}(s')[Z] +
\operatorname{div}(f)`. -/
@[stacks 02SH]
theorem exists_functionFieldUnit_sub_of_primeDivisorOrderOfVanishing
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s s' : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (hs' : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s')
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (data' : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s' Z) :
    (∀ Z : PrimeDivisor X, (data Z).quotient ≠ 0) →
      (∀ Z : PrimeDivisor X, (data' Z).quotient ≠ 0) →
    ∃ f : X.functionFieldˣ,
      ∀ Z : PrimeDivisor X,
        primeDivisorOrderOfVanishing s Z (data Z) =
          primeDivisorOrderOfVanishing s' Z (data' Z) +
            WithZero.log (Ring.ordFrac (X.presheaf.stalk Z.genericPoint) (f : X.functionField)) :=
  sorry

end AlgebraicGeometry.Scheme
