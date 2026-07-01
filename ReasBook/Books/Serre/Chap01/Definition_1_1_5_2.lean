import Mathlib.Tactic.Recall
import Mathlib.RepresentationTheory.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w'

open scoped TensorProduct

section

variable {𝕜 : Type u} [CommSemiring 𝕜]
variable {G : Type v} [Monoid G]
variable {V₁ : Type w} {V₂ : Type w'}
variable [AddCommMonoid V₁] [Module 𝕜 V₁]
variable [AddCommMonoid V₂] [Module 𝕜 V₂]
variable (ρ₁ : Representation 𝕜 G V₁) (ρ₂ : Representation 𝕜 G V₂)

/- Definition 1-1.5-2: the tensor product of two linear representations is the canonical
mathlib construction `Representation.tprod`, yielding the representation `ρ₁.tprod ρ₂` on
`V₁ ⊗[𝕜] V₂`. -/
recall Representation.tprod

/-- The tensor-product representation acts on pure tensors by applying each representation to its
own factor. -/
-- Proof sketch: use `Representation.tprod_apply` to rewrite the action as `TensorProduct.map`,
-- then apply `TensorProduct.map_tmul`.
theorem tprod_apply_tmul (g : G) (x₁ : V₁) (x₂ : V₂) :
    (ρ₁.tprod ρ₂ g) (x₁ ⊗ₜ[𝕜] x₂) = ρ₁ g x₁ ⊗ₜ[𝕜] ρ₂ g x₂ := by
  rw [Representation.tprod_apply, TensorProduct.map_tmul]

end
