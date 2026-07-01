import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 7.17: Minkowski's inequality for real-valued `ℒ^p(μ)` functions is the canonical
seminorm estimate `MeasureTheory.lpNorm_add_le`. Mathlib states it in the more general form for
functions into any normed additive commutative group, and only the first `MemLp` hypothesis is
needed because the right-hand side is allowed to take the value `∞`. -/
recall MeasureTheory.lpNorm_add_le
