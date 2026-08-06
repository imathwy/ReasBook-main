import Mathlib.Analysis.Convex.StdSimplex

-- The source-facing owner here is the topological standard simplex `Δ^n`; the canonical mathlib
-- owner is `stdSimplex ℝ (Fin (n + 1))`.

/-- Definition 16.1.1. The standard `n`-simplex `Δ^n`, viewed as the subset of
`Fin (n + 1) → ℝ` consisting of functions with nonnegative coordinates summing to `1`. -/
abbrev standardSimplex (n : ℕ) :=
  stdSimplex ℝ (Fin (n + 1))

prefix:max "Δ^" => standardSimplex

/-- `Δ^n` is the canonical mathlib standard simplex `stdSimplex ℝ (Fin (n + 1))`. -/
theorem standardSimplex_def (n : ℕ) :
    Δ^n = stdSimplex ℝ (Fin (n + 1)) :=
  rfl

/-- A point of `Δ^n` is exactly a function `Fin (n + 1) → ℝ` with nonnegative coordinates whose
coordinate sum is `1`. -/
theorem mem_standardSimplex_iff {n : ℕ} {x : Fin (n + 1) → ℝ} :
    x ∈ Δ^n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
  Iff.rfl

/-- `Δ^n` is the intersection of the coordinate half-spaces `0 ≤ x i` with the
affine hyperplane cut out by `∑ i, x i = 1`. -/
theorem standardSimplex_eq_inter (n : ℕ) :
    Δ^n = (⋂ i, {x | 0 ≤ x i}) ∩ {x | ∑ i, x i = 1} := by
  simpa [standardSimplex] using (stdSimplex_eq_inter ℝ (Fin (n + 1)))
