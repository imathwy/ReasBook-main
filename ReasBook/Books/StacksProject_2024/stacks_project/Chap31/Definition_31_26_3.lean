import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.OrderOfVanishing
import StacksProject_2024.Chap31.Definition_31_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The generic local ring `𝒪_{X, ξ}` attached to a prime divisor `Z`, where `ξ` is the generic
point of the support of `Z`. -/
noncomputable abbrev PrimeDivisor.genericPointStalk (Z : PrimeDivisor X) :=
  X.presheaf.stalk Z.genericPoint

-- Semantic recall: `lean_leansearch` surfaced the canonical owner `Ring.ordFrac`; Chapter 31
-- already owns prime divisors as `PrimeDivisor X`, with a generic-point API on prime divisors
-- themselves. Definition 31.26.3 therefore stays source-facing on `PrimeDivisor X` and only
-- bridges to `Ring.ordFrac`.

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/-- Definition 31.26.3: let `X` be a locally Noetherian integral scheme. For a prime divisor
`Z ⊆ X` whose stalk at its generic point is a discrete valuation ring, and for `f ∈ R(X)ˣ`, the
order of vanishing of `f` along `Z` is the order of vanishing of `f` in the generic local ring
`𝒪_{X, ξ}`. This is the source-faithful scheme-side bridge to `Ring.ordFrac`. -/
noncomputable abbrev primeDivisorOrder
    (Z : PrimeDivisor X)
    [IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)]
    (f : X.functionFieldˣ) : ℤ :=
  WithZero.log (Ring.ordFrac (X.presheaf.stalk Z.genericPoint) (f : X.functionField))

end AlgebraicGeometry.Scheme
