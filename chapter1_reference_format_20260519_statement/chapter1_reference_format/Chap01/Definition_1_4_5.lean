import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable (K : Type u) [Semiring K] {ι : Type v} {V : Type w} [AddCommMonoid V] [Module K V]
  (x : ι → V)

/- Definition 1.4.5: for a family `x : ι → V`, the canonical map
`Finsupp.linearCombination K x` sends a finitely supported coefficient family to the
corresponding linear combination of the vectors `x i`. -/
#check (Finsupp.linearCombination K x : (ι →₀ K) →ₗ[K] V)

/- Evaluating the canonical linear-combination map gives the corresponding finite sum of
coefficients times vectors. -/
recall Finsupp.linearCombination_apply {α : Type v} {M : Type w} {R : Type u} [Semiring R]
  [AddCommMonoid M] [Module R M] (v : α → M) (l : α →₀ R) :
    Finsupp.linearCombination R v l = l.sum fun i a ↦ a • v i
