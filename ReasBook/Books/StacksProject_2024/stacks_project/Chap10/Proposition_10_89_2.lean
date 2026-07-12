import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Domain triage: this proposition is about the tensor-product comparison map from a tensor with
an arbitrary product to the product of the tensors.
- `source-facing`: the TFAE identifying finite generation of `M` with surjectivity of those
  comparison maps.
- `core/canonical`: the owner maps `TensorProduct.piRightHom` and `TensorProduct.piScalarRightHom`
  from mathlib.
- `bridge/view`: the constant-family and scalar-family clauses are just specializations of those
  owner maps, not separate primitive data.
Primitive data are only the semiring, the module, and the chosen family `Q`. -/

-- Proof sketch: `(1) → (2)` is proved by choosing a surjection from a finite free module onto `M`
-- and comparing the induced commutative square with `TensorProduct.piRight` for the finite free
-- source. The implications `(2) → (3) → (4)` are obtained by specialization. For `(4) → (1)`,
-- apply surjectivity for the index set `M` to the diagonal element `fun x ↦ x : M → M`; a
-- preimage is a finite sum of pure tensors, whose left tensor factors then generate `M`.
/-- Proposition 10.89.2: for an `R`-module `M`, the following are equivalent: `M` is finitely
generated; for every family `(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is surjective; for every `R`-module `Q` and every set
`A`, the canonical map `M ⊗[R] (A → Q) → A → (M ⊗[R] Q)` is surjective; and for every set `A`,
the canonical map `M ⊗[R] (A → R) → A → M` is surjective. -/
theorem module_finite_tfae_tensorProduct_pi_surjective :
    List.TFAE
      [ Module.Finite R M,
        ∀ (A : Type w) (Q : A → Type x) [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)],
          Function.Surjective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type w) (Q : Type x) [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ (A : Type w),
          Function.Surjective (TensorProduct.piScalarRightHom R R M A) ] := sorry

end
