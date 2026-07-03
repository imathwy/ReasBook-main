import Mathlib.Tactic.Recall
import Mathlib.LinearAlgebra.TensorProduct.Basis

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w u₁ u₂

open scoped TensorProduct

section

variable (K : Type u) [Field K]
variable (V₁ : Type v) (V₂ : Type w)
variable [AddCommGroup V₁] [AddCommGroup V₂] [Module K V₁] [Module K V₂]

/- Definition 1-1.5-1: for vector spaces `V₁` and `V₂` over `K`, the tensor product is the
canonical vector space `V₁ ⊗[K] V₂`, with pure-tensor map linear in each variable and whose
pure tensors of basis vectors form a basis. -/
#check (V₁ ⊗[K] V₂)

/- The canonical map `(x₁, x₂) ↦ x₁ ⊗ₜ[K] x₂` is the owner declaration `TensorProduct.mk`. -/
recall TensorProduct.mk

section BasisClause

variable {ι₁ : Type u₁} {ι₂ : Type u₂}
variable (b₁ : Module.Basis ι₁ K V₁) (b₂ : Module.Basis ι₂ K V₂)

/- If `b₁` and `b₂` are bases of `V₁` and `V₂`, then the family of pure tensors
`b₁ i₁ ⊗ₜ[K] b₂ i₂` is the basis constructed by `Module.Basis.tensorProduct`. -/
recall Module.Basis.tensorProduct

end BasisClause
end
