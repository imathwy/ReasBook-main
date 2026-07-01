import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/- Lemma 10.12.3 (1): the bilinear map `(x, y) ↦ y ⊗ x` induces the canonical tensor-product
symmetry isomorphism `M ⊗[R] N ≃ₗ[R] N ⊗[R] M`, namely `TensorProduct.comm`. -/
recall TensorProduct.comm

variable {P : Type x} [AddCommMonoid P] [Module R P]

/- Lemma 10.12.3 (2): the bilinear map `((x, y), z) ↦ (x ⊗ z, y ⊗ z)` induces the canonical
distribution isomorphism from the binary direct sum tensor product to the product of tensor
products. In Lean, the binary direct sum of `R`-modules is canonically modeled by the product
module `M × N`, and the corresponding equivalence is the specialization of `prodLeft` to
`S = R`. -/
recall TensorProduct.prodLeft

end

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 10.12.3 (3): the bilinear map `(r, x) ↦ r • x` induces the canonical left-unit
isomorphism `R ⊗[R] M ≃ₗ[R] M`, namely `TensorProduct.lid`. -/
recall TensorProduct.lid

end
