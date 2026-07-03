import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_10 (from Chap05) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The effective domain of an extended-real-valued function is the set of points where the
function takes a finite value. -/
def effective_domain (f : E → EReal) : Set E := {x | f x < ⊤}

/-- An extended-real-valued function is strongly convex when it has no `-∞` values, its effective
domain is convex, and it satisfies the quadratic Jensen inequality there for a positive modulus. -/
class is_strongly_convex_function (f : E → EReal) (σ : ℝ) : Prop where
  /-- A strongly convex extended-real-valued function never takes the value `-∞`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- The effective domain of a strongly convex function is convex. -/
  convex_effective_domain : Convex ℝ (effective_domain f)
  /-- The defining quadratic Jensen inequality holds along every segment in the effective domain. -/
  segment_ineq :
    ∀ ⦃x⦄, x ∈ effective_domain f → ∀ ⦃y⦄, y ∈ effective_domain f → ∀ ⦃t : ℝ⦄,
      t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤
          (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
            (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  /-- The strong-convexity modulus is strictly positive. -/
  sigma_pos : 0 < σ

-- Proof sketch: translate the source predicate to the canonical owner statement
-- `StrongConvexOn (effective_domain f) σ₁ (fun x ↦ (f x).toReal)` on the finite-valued
-- restriction, apply `StrongConvexOn.mono hσ₂σ₁.le` to lower the modulus from `σ₁` to `σ₂`, and
-- then translate back while keeping the inherited no-`⊥` and convex-domain data from `hf` and the
-- new positivity hypothesis `hσ₂`.
/-- Proposition 5.10: if an extended-real-valued function is `σ₁`-strongly convex, then it is
also `σ₂`-strongly convex for every smaller positive modulus `σ₂ < σ₁`. -/
theorem is_strongly_convex_function.mono
    {f : E → EReal} {σ₁ σ₂ : ℝ} (hf : is_strongly_convex_function f σ₁)
    (hσ₂ : 0 < σ₂) (hσ₂σ₁ : σ₂ < σ₁) :
    is_strongly_convex_function f σ₂ := sorry

end

/-! ### Theorem_5_10 (from Chap05) -/
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
