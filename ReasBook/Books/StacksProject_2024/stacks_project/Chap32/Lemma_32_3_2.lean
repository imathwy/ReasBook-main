import Mathlib
import StacksProject_2024.Chap32.Lemma_32_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} (S : Scheme.{u})
variable (T : I → Over S)
variable [∀ i, IsAffineHom (T i).hom]
variable [∀ i, Surjective (T i).hom]

-- Semantic recall: `lean_leansearch` identified `AlgebraicGeometry.Surjective` as the canonical
-- owner for scheme-level surjectivity, and local scratch checking verified `piObj T` as the slice
-- product object in `Over S`.

/-- Lemma 32.3.2: if each affine morphism `T_i ⟶ S` is surjective, then the product of the family
in `Over S` maps surjectively to `S`. -/
@[stacks 0CNJ]
theorem surjective_piObj_hom_of_isAffineHom :
    Surjective (piObj T).hom := sorry

end

end AlgebraicGeometry
