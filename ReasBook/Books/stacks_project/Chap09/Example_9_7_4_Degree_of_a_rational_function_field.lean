import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped RatFunc

/-- Example 9.7.4 (Degree of a rational function field): the rational function field `k(t)` is not
a finite extension of `k`, equivalently it is not finite-dimensional as a `k`-vector space. -/
theorem ratFunc_not_finiteDimensional
    (k : Type u) [Field k] :
    ¬ FiniteDimensional k k⟮X⟯ := by
  intro h
  letI := h
  exact (Algebra.transcendental_iff_not_isAlgebraic.mp RatFunc.transcendental)
    (Algebra.IsAlgebraic.of_finite k k⟮X⟯)
