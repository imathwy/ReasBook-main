import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical DVR owner
-- `IsDiscreteValuationRing`, and nearby Chapter 31 files formalize effective Cartier divisors on
-- schemes through `D : X.IdealSheafData` and the closed subscheme inclusion `D.subschemeι`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The local ring of `X` at the image of the generic point of an integral effective Cartier
divisor is a domain. -/
instance instIsDomainStalk_genericPointImage_subscheme_of_isEffectiveCartierDivisor
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsIntegral D.subscheme] :
    IsDomain (X.presheaf.stalk (D.subschemeι (genericPoint D.subscheme))) := sorry

/-- Lemma 31.15.4: if `X` is a Noetherian scheme and `D ⊆ X` is an integral closed subscheme
which is also an effective Cartier divisor, then the local ring of `X` at the generic point of
`D` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_genericPointImage_subscheme_of_isEffectiveCartierDivisor
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsIntegral D.subscheme] :
    @IsDiscreteValuationRing
      (X.presheaf.stalk (D.subschemeι (genericPoint D.subscheme))) inferInstance
      (instIsDomainStalk_genericPointImage_subscheme_of_isEffectiveCartierDivisor D) := sorry

end AlgebraicGeometry.Scheme
