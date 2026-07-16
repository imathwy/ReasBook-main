import stacks_proof.stacks_project.Chap10.Lemma_10_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]
variable (K L M : CochainComplex (ModuleCat R) ℤ) (q s r : ℤ)

/- Domain-style sampling for 15.72.1.1:
- primary domain: tensor-Hom currying for `R`-modules, specialized degreewise to cochain
  complexes;
- sampled owner declarations:
  `TensorProduct.lift.equiv`,
  `TensorProduct.curry`,
  the Chapter 10 recall file `Lemma_10_12_8`;
- best owner abstraction: the only primitive data here are the three degree terms
  `K.X (-q)`, `L.X (-s)`, and `M.X r`; the currying equivalence itself is already the canonical
  owner `TensorProduct.lift.equiv`, already recalled upstream in Chapter 10, while
  `TensorProduct.curry` is derived API;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `Hom_R(K^{-q}, Hom_R(L^{-s}, M^r)) ≃ Hom_R(K^{-q} ⊗_R L^{-s}, M^r)`;
  `core/canonical`: `TensorProduct.lift.equiv`;
  `bridge/view`: the specialization of that owner to the indicated degree terms.

This file targets the `bridge/view` layer. Since Chapter 10 already recalls the tensor-Hom owner,
introducing a new local degreewise wrapper here would only duplicate that project-level API. -/

/- 15.72.1.1: this is the degreewise specialization of the Chapter 10 tensor-Hom currying recall,
written in the source orientation
`Hom_R(K^{-q}, Hom_R(L^{-s}, M^r)) ≃ Hom_R(K^{-q} ⊗_R L^{-s}, M^r)`. -/
#check
  (TensorProduct.lift.equiv (.id R) (K.X (-q)) (L.X (-s)) (M.X r) :
    ((K.X (-q)) →ₗ[R] (L.X (-s) →ₗ[R] M.X r)) ≃ₗ[R]
      (((K.X (-q)) ⊗[R] (L.X (-s))) →ₗ[R] M.X r))
