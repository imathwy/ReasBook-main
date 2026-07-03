import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_54
import LecturesConvexOptimization_Nesterov_2018.Chap06.Algorithm_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.12 lies in the Chapter 6 conditional-gradient / weighted upper-bound domain.

Sampled owner-style declarations:
- `initialLinearizationGap` in `Definition_6_54`, the source-facing owner of the initial quantity
  `V₀`;
- `linearOptimizationOracleErrorBound` in `Definition_6_54`, the Chapter 6 owner of the
  cumulative error term `B_{ν,t}`;
- `LinearOracleCompositeMethod` in `Algorithm_6_4`, the chapter owner of the iterate and
  oracle-point data for method `(6.4.12)`;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the ambient
  extended-valued bridge/view owner that `Definition_6_54` specializes away from on this theorem
  surface.

Best owner abstraction:
- source-facing: the weighted composite upper bound with
  `initialLinearizationGap Q f Ψ (method 0)` as the initial quantity;
- core/canonical: `LinearOracleCompositeMethod` together with
  `linearOptimizationOracleErrorBound`;
- bridge/view: the ambient extended-regularizer gap value, which should not appear in the theorem
  statement.

Primitive data:
- the feasible set `Q`, objective `f`, subtype regularizer `Ψ`, and method data;
- convexity of the canonical ambient extension `Function.extend Subtype.val Ψ 0` on `Q`, the
  owner abstraction that expresses convexity of the subtype regularizer along feasible segments;
- the weight sequence `a`, Hölder data `ν`, `Gν`, `D`, and the Chapter 6 hypotheses on `a`,
  `τ_t`, and the `(6.4.3)`-style error term.

Derived API:
- the weighted affine-linearization upper bound at time `t`;
- the canonical Chapter 6 error term
  `linearOptimizationOracleErrorBound (initialLinearizationGap Q f Ψ (method 0)) a Gν D ν t`.

Source/core/bridge triage:
- source-facing: this weighted estimate for the composite conditional-gradient method;
- core/canonical: the Chapter 6 owners `initialLinearizationGap` and
  `linearOptimizationOracleErrorBound`;
- bridge/view: `ConditionalGradientContraction.linearizedCompositeGap`, used upstream only to
  justify `initialLinearizationGap` and intentionally absent from the theorem surface.
-/

-- Proof sketch: argue by induction on `t`. For the induction step, combine convexity of `f`
-- on `Q` and convexity of the ambient extension `Function.extend Subtype.val Ψ 0` on `Q` with
-- the update
-- `x_{t+1} = (1 - τ_t) x_t + τ_t v_t`, use the oracle minimization property at `v_t`, and then
-- insert the assumed `(6.4.3)`-style Hölder error bound to absorb the residual term into the
-- Chapter 6 owner `linearOptimizationOracleErrorBound`, initialized by the source-facing
-- constrained linearization-gap owner `initialLinearizationGap` at the primitive starting point
-- `x₀ = method.x0`.
/-- Theorem 6.12: along method `(6.4.12)`, if `f` is convex on `Q`, the canonical ambient
extension of the regularizer `Ψ` is convex on `Q`, the coefficients satisfy
`A_t = ∑_{k=0}^t a_k` and `τ_t = a_{t+1} / A_{t+1}`, and the `(6.4.3)` Hölder-gradient error term
is bounded by `G_ν D^(1 + ν)`, then for every iteration `t` and feasible point `x` the weighted
composite objective at `x_t` is bounded by the sum of the affine linearizations at `x` plus the
Chapter 6 error term `linearOptimizationOracleErrorBound V₀ a G_ν D ν t`, where
`V₀ = initialLinearizationGap Q f Ψ x₀` and `x₀ = method.x0`. -/
theorem weighted_objective_upper_bound_of_linear_oracle_composite_method
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (hΨ_convex : ConvexOn ℝ Q (Function.extend Subtype.val Ψ 0))
    (method : LinearOracleCompositeMethod Q f Ψ)
    (a : ℕ → ℝ) (ν Gν D : ℝ)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ, ∀ x : Q,
        inner ℝ
            (gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t))
            ((x : E) - method.oraclePoint t) ≥
          -((Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)))
    (t : ℕ) (x : Q) :
    A[a](t) * (f (method t) + Ψ (method t)) ≤
      (Finset.sum (Finset.range (t + 1)) fun k ↦
        a k *
          (f (method k) +
            inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
            Ψ x)) +
        linearOptimizationOracleErrorBound
          (initialLinearizationGap Q f Ψ method.x0) a Gν D ν t := sorry
