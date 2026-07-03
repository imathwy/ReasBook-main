import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped RealInnerProductSpace Gradient

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Theorem 5.10 is a `bridge/view` item: the source-facing Euclidean second-order expansion is
obtained by pulling back `f` along `AffineMap.lineMap x y` and applying the scalar owner theorem
`taylor_mean_remainder_lagrange_iteratedDeriv`. The canonical second-order data is the bilinear
Hessian `bilinearIteratedFDerivTwo`.
-/

-- Proof sketch: compose `f` with the affine line map `t ↦ AffineMap.lineMap x y t` on `[0, 1]`
-- and apply the one-variable Taylor theorem with Lagrange remainder. The first derivative of the
-- pullback at `0` is `⟪∇ f x, y - x⟫`, and the second derivative at an intermediate point is the
-- Hessian quadratic form `bilinearIteratedFDerivTwo ℝ f ξ (y - x) (y - x)`.
/-- Theorem 5.10: if `f : ℝ^n → ℝ` is twice continuously differentiable on an open set `U`
containing the ball `Metric.ball x r`, then every `y` in that ball admits a point `ξ` on the
segment from `x` to `y` such that the second-order Taylor expansion of `f` at `x` with Lagrange
remainder holds. The Hessian term is expressed by the canonical bilinear second derivative
`bilinearIteratedFDerivTwo`. -/
theorem linear_approximation_with_lagrange_remainder
    {U : Set E} {f : E → ℝ} {x y : E} {r : ℝ}
    (hU_open : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hball : Metric.ball x r ⊆ U)
    (hy : y ∈ Metric.ball x r) :
    ∃ ξ ∈ segment ℝ x y,
      f y = f x + inner ℝ (∇ f x) (y - x)
        + (1 / 2 : ℝ) * bilinearIteratedFDerivTwo ℝ f ξ (y - x) (y - x) := sorry

end
