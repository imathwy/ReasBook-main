import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

variable {R : Type u} {R₂ : Type v} {M : Type w} {M₂ : Type x}
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} [RingHomSurjective σ₁₂]

/- Proposition 1.4.14: A linear map sends a subspace to a subspace. The canonical owner
construction is `Submodule.map`; the set-theoretic image description is the companion theorem
`Submodule.map_coe`. -/
#check (Submodule.map : (M →ₛₗ[σ₁₂] M₂) → Submodule R M → Submodule R₂ M₂)

/- Concretely, the carrier of the image submodule is the set-theoretic image. -/
#check (Submodule.map_coe : (f : M →ₛₗ[σ₁₂] M₂) → (p : Submodule R M) →
  (↑(Submodule.map f p) : Set M₂) = f '' p)
