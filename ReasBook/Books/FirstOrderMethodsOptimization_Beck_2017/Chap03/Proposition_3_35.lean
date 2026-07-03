import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Corollary_3_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

/- Proposition 3.35 is `source-facing`: its primitive data are the entropy-linear objective and
the resulting softmax point. The `core/canonical` owner declarations remain the simplex
`stdSimplex ℝ (Fin n)`, the multiplier condition `IsStdSimplexMultiplier`, and the
optimality criterion `isMinOn_stdSimplex_iff_exists_subgradient_vector_and_multiplier` from
Corollary 3.33. This file therefore keeps only the concrete source objective and its canonical
optimizer, without introducing a parallel wrapper for simplex optimality. -/

section

variable {n : ℕ}

/-- The softmax point attached to `y`, with coordinates `exp (y i)` normalized to sum to `1`. -/
def softmax_point (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ Real.exp (y i) / ∑ j, Real.exp (y j)

/-- The entropy-linear objective
`x ↦ ∑ i, x i * log (x i) - ∑ i, y i * x i` on `ℝ^n`, modeled as `Fin n → ℝ`. -/
def entropy_linear_objective (y x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * Real.log (x i) - ∑ i, y i * x i

-- Proof sketch: apply the chapter owner criterion
-- `isMinOn_stdSimplex_iff_exists_subgradient_vector_and_multiplier` to the entropy-linear
-- objective, use the entropy singularity at the boundary to rule out zero coordinates of `xstar`,
-- and then collapse the multiplier condition to the stationarity equations
-- `log (xstar i) + 1 - y i = μ`. Exponentiating yields
-- `xstar i = α * exp (y i)` for a constant `α`, and the simplex constraint `∑ i, xstar i = 1`
-- determines `α = (∑ j, exp (y j))⁻¹`.
/-- Proposition 3.35: if `xstar` minimizes
`entropy_linear_objective y`, equivalently `x ↦ ∑ i, x i * log (x i) - ∑ i, y i * x i`, on the
unit simplex `Δ_n = stdSimplex ℝ (Fin n)`, then `xstar` is the softmax point
`softmax_point y`. -/
theorem eq_softmax_of_isMinOn_stdSimplex_entropyLinearObjective
    (y xstar : Fin n → ℝ)
    (hx_mem : xstar ∈ stdSimplex ℝ (Fin n))
    (hmin : IsMinOn (entropy_linear_objective y) (stdSimplex ℝ (Fin n)) xstar) :
    xstar = softmax_point y := sorry

end
