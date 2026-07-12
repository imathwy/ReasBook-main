import Mathlib
import StacksProject_2024.Chap31.Lemma_31_13_3
import StacksProject_2024.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `IsAffineHom` and affine open-subscheme owners.
-- Local Chapter 31 precedent provides `closedImmersionComplement` for the open complement of a
-- closed immersion, while Chapter 29 owns `schemeTheoreticallyDense` for open subschemes.
-- The Stacks tag evidence is consistent: item tag `07ZU` matches the source URL `/tag/07ZU`.

variable {S D : Scheme.{u}} (i : D ⟶ S)
variable [MonoidalCategory (RingedSpace.Modules S.toRingedSpace)]
variable [IsEffectiveCartierDivisor i]

/-- Lemma 31.13.4 (1): if `D ⊆ S` is an effective Cartier divisor and
`U = S \ D`, then the open immersion `U ⟶ S` is an affine morphism. -/
@[stacks 07ZU]
theorem isAffineHom_closedImmersionComplement_ι_of_isEffectiveCartierDivisor :
    IsAffineHom (closedImmersionComplement i).ι := sorry

/-- Lemma 31.13.4 (2): if `D ⊆ S` is an effective Cartier divisor and
`U = S \ D`, then `U` is scheme theoretically dense in `S`. -/
@[stacks 07ZU]
theorem schemeTheoreticallyDense_closedImmersionComplement_of_isEffectiveCartierDivisor :
    schemeTheoreticallyDense (closedImmersionComplement i) := sorry

end AlgebraicGeometry
