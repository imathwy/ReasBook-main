import Mathlib

open CategoryTheory Limits AlgebraicGeometry
open CategoryTheory.Limits.ProductsFromFiniteCofiltered

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical finite-stage product API
-- `ProductsFromFiniteCofiltered.finiteSubproductsCone` and `isLimitFiniteSubproductsCone`; the
-- source-facing statements below specialize that slice-category product presentation to affine
-- families over a fixed base scheme.

section

variable {I : Type u} (S : Scheme.{u})
variable (T : I → Over S)
variable [∀ i, IsAffineHom (T i).hom]

/-- Lemma 32.3.1 (1): an indexed family of affine morphisms into `S` admits a product in the slice
category `Over S`. -/
@[stacks 0CNI, instance]
theorem hasProduct_over_of_isAffineHom :
    HasProduct T := sorry

/-- Lemma 32.3.1 (2): the product of an affine family over `S` is the limit of the cofiltered
diagram of its finite fibre products over `S`. -/
@[stacks 0CNI]
noncomputable def isLimit_finiteSubproductsCone_of_isAffineHom :
    IsLimit (finiteSubproductsCone T) := sorry

/-- Companion normal-form theorem for the source-facing finite-subproducts limit construction. -/
theorem isLimit_finiteSubproductsCone_of_isAffineHom_def :
    isLimit_finiteSubproductsCone_of_isAffineHom S T =
      (show IsLimit (finiteSubproductsCone T) from
        isLimit_finiteSubproductsCone_of_isAffineHom S T) := sorry

/-- Lemma 32.3.1 (3): the canonical projection from the product over `S` to each finite fibre
product stage is an affine morphism of schemes. -/
@[stacks 0CNI]
theorem isAffineHom_finiteSubproductsCone_π_app_of_isAffineHom
    (s : (Finset (Discrete I))ᵒᵖ) :
    IsAffineHom ((finiteSubproductsCone T).π.app s).left := sorry

end

end AlgebraicGeometry
