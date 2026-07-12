import Mathlib
import StacksProject_2024.Chap32.Lemma_32_3_1

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} (S : Scheme.{u})
variable (T : I → Over S)
variable [∀ i, IsIntegralHom (T i).hom]

-- Semantic recall: `lean_leansearch` identified `AlgebraicGeometry.IsIntegralHom` as the
-- canonical owner for integral scheme morphisms, and the nearby slice-product precedent
-- `Lemma_32_3_1` / `Lemma_32_3_2` uses `piObj T` for the product object in `Over S`.

/-- Lemma 32.3.3: if each morphism `T_i ⟶ S` is integral, then the product of the family in
`Over S` is integral over `S`. -/
@[stacks 0CNK]
theorem isIntegralHom_piObj_hom_of_isIntegralHom :
    IsIntegralHom (piObj T).hom := sorry

end

end AlgebraicGeometry
