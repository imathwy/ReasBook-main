import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.10 lies in the cubic-Newton linear-rate domain on a real Hilbert space.

Sampled owner-style declarations:
* `conditionNumberOfDegree` in `Definition_4_2_11`
* `uniformConvexityParameterOfDegree` in `Definition_4_2_11`
* `iteratedFDerivLipschitzConstantOfDegree` in `Definition_4_2_11`
* `cubicNewtonQuadraticDecreaseRegion` in `Text_4_2_11`, where the source threshold is rewritten
  in multiplication form to avoid division-by-zero artifacts
* `acceleratedCubicNewtonQuadraticConvergenceRegion` in `Text_4_2_22`, which uses the same
  multiplication-form threshold discipline for the local cubic region
* the positive-parameter owner style in `Lemma_4_4_8`, where `NNRealˣ` carries positivity in the
  public API instead of separate proof binders

Best owner abstraction:
* source-facing: the cubic-Newton rate bounds driven by arbitrary positive parameters `σ₃` and
  `L₃` satisfying the textbook gap and descent inequalities
* core/canonical: the chapter owner `γ[3](f)` for the degree-`3` condition number of a function
* bridge/view: the contraction factor `2 √L₃ / (2 √L₃ + √σ₃)`, equivalent to
  `(1 + (1 / 2) * sqrt (σ₃ / L₃))⁻¹`

Primitive data:
* a function `f`, a reference point `xStar`, and an iterate sequence `x`
* positive scalars `σ₃`, `L₃`, now owned canonically as `NNRealˣ`
* the two source hypotheses bounding the gap by `‖∇ f‖^(3/2)` and the one-step decrease by
  `‖∇ f‖^(3/2)`, stated in multiplication form rather than through `1 / sqrt σ₃` and
  `1 / sqrt L₃`

Derived API:
* the contraction factor `2 √L₃ / (2 √L₃ + √σ₃)` and its exponential companion
  `√σ₃ / (2 √L₃ + √σ₃)`

Semantic-priority note:
* the file remains source-facing over arbitrary `σ₃` and `L₃`; replacing them by the canonical
  owner `γ[3](f)` would change the theorem interface from textbook assumptions to a stronger
  function-level conditioning API.
* the refined statements keep those source parameters, but encode their positivity by `NNRealˣ`
  and rewrite the public inequalities in multiplication form, following the nearby chapter style
  that avoids division-by-zero and `Real.sqrt` artifacts in theorem surfaces.
-/

section CubicNewtonConditionNumberRate

variable {f : E → ℝ} {x : ℕ → E} {xStar : E} {σ₃ L₃ : NNRealˣ}

local notation "Δ" => fun k : ℕ ↦ f (x k) - f xStar
local notation "ρ" =>
  ((2 : ℝ) * Real.sqrt (L₃ : ℝ)) / ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))

-- Proof sketch: apply the global gap estimate at `x_{k+1}` to bound
-- `Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2)` from below, then substitute that lower bound into the
-- assumed one-step descent inequality. Writing the source bounds in multiplication form yields
-- `√σ₃ * Δ_{k+1} ≤ 2 √L₃ * (f(x_k) - f(x_{k+1}))`, which is equivalent to the textbook factor
-- `(1 / 2) * sqrt (σ₃ / L₃)` because `σ₃, L₃ > 0` are owned by `NNRealˣ`.
/-- Text 4.2.10 (1): if
`3 √σ₃ (f x - f xStar) ≤ 2 ‖∇ f x‖^(3/2)` for every `x`, and if the sequence `x`
satisfies
`‖∇ f(x_{k+1})‖^(3/2) ≤ 3 √L₃ (f(x_k) - f(x_{k+1}))`,
then each one-step decrease controls the next gap by
`√σ₃ (f(x_{k+1}) - f(xStar)) ≤ 2 √L₃ (f(x_k) - f(x_{k+1}))`, equivalently by the textbook
factor `(1 / 2) * sqrt (σ₃ / L₃)`. -/
theorem cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (k : ℕ) :
    Real.sqrt (σ₃ : ℝ) * Δ (k + 1) ≤
      (2 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))) := sorry

-- Proof sketch: apply the one-step estimate from
-- `cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap` to the gaps
-- `Δ_k = f (x k) - f xStar`, rewrite it as
-- `Δ_{k+1} ≤ ρ * Δ_k` with `ρ = 2 √L₃ / (2 √L₃ + √σ₃)`, and iterate this scalar recurrence from
-- `1` to `k - 1`.
/-- Text 4.2.10 (2): under the same assumptions, the objective gaps along `x` decay at the linear
rate
`ρ^(k-1)` with `ρ = 2 √L₃ / (2 √L₃ + √σ₃) =
(1 + (1 / 2) * sqrt (σ₃ / L₃))⁻¹` for every `k ≥ 1`. -/
theorem cubic_newton_gap_le_linear_rate
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    {k : ℕ} (hk : 1 ≤ k) :
    Δ k ≤ ρ ^ (k - 1) * Δ 1 := sorry

-- Proof sketch: combine `cubic_newton_gap_le_linear_rate` with the initial cubic upper bound on
-- `f (x 1) - f xStar`, then use
-- `ρ ≤ exp (-√σ₃ / (2 √L₃ + √σ₃))` to bound the geometric factor by the displayed exponential
-- term.
/-- Text 4.2.10 (3): if in addition the first gap satisfies
`3 (f(x₁) - f(xStar)) ≤ L₃ ‖x₀ - xStar‖³`, then for every `k ≥ 1` the gap is bounded by the
displayed exponential expression, written with the equivalent rate coefficient
`√σ₃ / (2 √L₃ + √σ₃)`. -/
theorem cubic_newton_gap_le_exponential_rate
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (hinit :
      (3 : ℝ) * (f (x 1) - f xStar) ≤ (L₃ : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ))
    {k : ℕ} (hk : 1 ≤ k) :
    Δ k ≤
      Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
        (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := sorry

-- Proof sketch: start from `cubic_newton_gap_le_exponential_rate`, replace `‖x 0 - xStar‖` by
-- the bound `D`, and solve the resulting exponential inequality for `k` in terms of `ε` by
-- taking logarithms. The lower bound on `k` is written in multiplication form to avoid the
-- surface factor `(2 √L₃ + √σ₃) / √σ₃`.
/-- Text 4.2.10 (4): if `‖x₀ - xStar‖ ≤ D`, then the target accuracy `f(x_k) - f(xStar) ≤ ε` is
guaranteed once `k` satisfies the explicit logarithmic lower bound corresponding to the textbook
`O((√L₃ / √σ₃) * log (L₃ D^3 / ε))` estimate, stated in multiplication form. -/
theorem cubic_newton_gap_le_of_iteration_count_bound
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (hinit :
      (3 : ℝ) * (f (x 1) - f xStar) ≤ (L₃ : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ))
    {D ε : ℝ}
    (hD : ‖x 0 - xStar‖ ≤ D)
    (hε : 0 < ε)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hk_bound :
      (((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) *
          Real.log ((((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) / ε) ≤
        (k - 1 : ℝ) * Real.sqrt (σ₃ : ℝ))) :
    Δ k ≤ ε := sorry

end CubicNewtonConditionNumberRate
