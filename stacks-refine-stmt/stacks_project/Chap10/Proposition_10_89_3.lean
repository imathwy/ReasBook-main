import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this proposition is about the tensor-product comparison map from a tensor with
an arbitrary product to the product of the tensors.
- `source-facing`: the TFAE identifying finite presentation of `M` with bijectivity of those
  comparison maps.
- `core/canonical`: the owner maps `TensorProduct.piRightHom` and `TensorProduct.piScalarRightHom`
  from mathlib.
- `bridge/view`: the constant-family and scalar-family clauses are just specializations of those
  owner maps, not separate primitive data.
Primitive data are only the ring, the module, and the chosen family `Q`. -/

-- Proof sketch: `(1) → (2)` follows from a finite presentation of `M` and exactness of tensor
-- product, using that finite products commute with tensoring by finite free modules. The
-- implications `(2) → (3) → (4)` are immediate specializations. For `(4) → (1)`, combine
-- Proposition `10.89.2` to obtain finite generation of `M`, choose a surjection from a finite free
-- module onto `M`, and compare kernels after tensoring with `R^A`; surjectivity of the induced map
-- on the kernel then yields finite generation of that kernel, hence finite presentation of `M`.
/-- Proposition 10.89.3: for an `R`-module `M`, the following are equivalent: `M` is finitely
presented; for every family `(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is bijective; for every `R`-module `Q` and every set `A`,
the canonical map `M ⊗[R] (A → Q) → A → (M ⊗[R] Q)` is bijective; and for every set `A`, the
canonical map `M ⊗[R] (A → R) → A → M` is bijective. -/
theorem module_finitePresentation_tfae_tensorProduct_pi_bijective :
    List.TFAE
      [ Module.FinitePresentation R M,
        ∀ (A : Type w) (Q : A → Type x) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Bijective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type w) (Q : Type x) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ (A : Type w),
          Function.Bijective (TensorProduct.piScalarRightHom R R M A) ] := sorry

end
