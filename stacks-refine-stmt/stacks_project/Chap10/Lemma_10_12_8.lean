import Mathlib
-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/- Lemma 10.12.8 is `source-facing` but recall-shaped: the owner abstraction is the canonical
linear equivalence `TensorProduct.lift.equiv`, and the textbook bijection
`Hom_R(M ⊗[R] N, P) ≃ Hom_R(M, Hom_R(N, P))` is its specialization along `RingHom.id R` followed by
inversion. -/
#check
  ((TensorProduct.lift.equiv (.id R) M N P).symm :
    (M ⊗[R] N →ₗ[R] P) ≃ₗ[R] (M →ₗ[R] N →ₗ[R] P))

/- Companion check: the forward map of this inverse specialization is the canonical curried map
`TensorProduct.curry`, sending `f : M ⊗[R] N →ₗ[R] P` to `m ↦ fun n ↦ f (m ⊗ₜ n)`. -/
#check (TensorProduct.curry : (M ⊗[R] N →ₗ[R] P) → M →ₗ[R] N →ₗ[R] P)
