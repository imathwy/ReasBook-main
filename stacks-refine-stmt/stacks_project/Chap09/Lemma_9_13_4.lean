import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/- Domain-style sampling:
- primary domain: tensor products of field extensions and comparison maps to products indexed by
  algebra embeddings;
- sampled owner declarations: `Algebra.TensorProduct.commRight`,
  `Algebra.TensorProduct.productLeftAlgHom`, `Pi.algHom`, `Algebra.TensorProduct.piRight`,
  `Field.finSepDegree_eq_of_isAlgClosed`;
- best owner abstraction here: the single `L`-algebra homomorphism into the function-space
  product, assembled canonically from the pointwise `productLeftAlgHom`s via `Pi.algHom`. -/

/-- The `L`-algebra homomorphism induced by the comparison map
`α ⊗ β ↦ (σ(α)β)_σ`. -/
noncomputable def tensorProductToPiAlgHom : K ⊗[F] L →ₐ[L] ((K →ₐ[F] L) → L) :=
  Pi.algHom L (fun _ : K →ₐ[F] L ↦ L) fun σ ↦
    (Algebra.TensorProduct.productLeftAlgHom (AlgHom.id L L) σ).comp
      (Algebra.TensorProduct.commRight F L K).symm.toAlgHom

/-- The comparison algebra homomorphism sends `α ⊗ β` to the family `σ ↦ σ(α)β`. -/
-- Proof sketch: evaluate the canonical `Pi.algHom` at `σ`, unfold the swapped tensor-product
-- factor order, and compute `productLeftAlgHom` on a pure tensor.
theorem tensorProductToPiAlgHom_apply_tmul
    (α : K) (β : L) (σ : K →ₐ[F] L) :
    tensorProductToPiAlgHom (α ⊗ₜ[F] β) σ = σ α * β := by
  simp [tensorProductToPiAlgHom, mul_comm]

variable [FiniteDimensional F K] [Algebra.IsSeparable F K] [IsAlgClosed L]

/-- Lemma 9.13.4: for a finite separable extension `K/F` and an algebraically closed extension
field `L/F`, the comparison `L`-algebra homomorphism
`K ⊗[F] L → ((K →ₐ[F] L) → L)` given by `α ⊗ β ↦ (σ(α)β)_σ` is bijective. -/
-- Proof sketch: compare the `L`-dimensions of source and target using finiteness of `K/F` and the
-- cardinality formula for `F`-embeddings into an algebraically closed field, then use Dedekind
-- linear independence of embeddings to show that the kernel is trivial.
theorem tensorProductToPiAlgHom_bijective :
    Function.Bijective (tensorProductToPiAlgHom : K ⊗[F] L → (K →ₐ[F] L) → L) := sorry

/-- The comparison map of Lemma 9.13.4 as an explicit `L`-algebra equivalence. -/
noncomputable def tensorProductToPiAlgEquiv : K ⊗[F] L ≃ₐ[L] ((K →ₐ[F] L) → L) :=
  AlgEquiv.ofBijective
    tensorProductToPiAlgHom
    tensorProductToPiAlgHom_bijective
