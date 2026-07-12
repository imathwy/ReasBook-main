import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (K : Type u) [Semiring K] (V : Type v) [AddCommMonoid V] [Module K V]

/- Remark 1.4.13: for a `K`-vector space `V`, a linear form is an element of the canonical dual
module `Module.Dual K V`. Mathlib's owner already lives at the weaker module level, so we recall
it there. -/
recall Module.Dual (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :
  Type (max u v)

/- Concretely, the dual module is realized as the type of `K`-linear maps from `V` to `K`. -/
#check (V →ₗ[K] K)
