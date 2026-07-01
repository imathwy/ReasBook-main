import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u w z

section AddCommMonoid

variable {R : Type u} {M : Type w} {M₂ : Type z}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/- Definition 1.4.15: for an `R`-linear map, the kernel is the canonical subspace `LinearMap.ker`
consisting of vectors sent to `0`. -/
#check (LinearMap.ker : (M →ₗ[R] M₂) → Submodule R M)

/- For an `R`-linear map, the image is the canonical subspace `LinearMap.range`, i.e. the
set-theoretic image of the source under the map. -/
#check (LinearMap.range : (M →ₗ[R] M₂) → Submodule R M₂)

end AddCommMonoid

section Ring

variable {R : Type u} {M : Type w} {M₂ : Type z}
variable [Ring R] [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R M₂]

/- An `R`-linear map is injective exactly when its kernel is trivial, i.e. equal to `⊥`, the
submodule whose only element is `0`. -/
#check (LinearMap.ker_eq_bot : ∀ {f : M →ₗ[R] M₂}, f.ker = ⊥ ↔ Function.Injective f)

end Ring
