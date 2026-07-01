import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable (K : Type u) [Semiring K] (V₁ : Type v) (V₂ : Type w)
  [AddCommMonoid V₁] [Module K V₁] [AddCommMonoid V₂] [Module K V₂]

/- Definition 1.4.12: a map `f : V₁ → V₂` between `K`-vector spaces is linear exactly when it
satisfies the canonical source-facing predicate `IsLinearMap K f`. The core bundled owner is the
type `V₁ →ₗ[K] V₂`. -/
recall IsLinearMap (R : Type u) {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M → M₂) : Prop

/- Bundled linear maps between `K`-modules form the canonical type `V₁ →ₗ[K] V₂`. -/
#check (V₁ →ₗ[K] V₂)

/- A function satisfying the source-facing linearity predicate canonically packages into a bundled
linear map. -/
recall IsLinearMap.mk' {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M → M₂) (lin : IsLinearMap R f) :
    M →ₗ[R] M₂

/- Every bundled linear map satisfies the source-facing linearity predicate on its underlying
function. -/
recall LinearMap.isLinear {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R]
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] (fₗ : M →ₗ[R] M₂) :
    IsLinearMap R fₗ
