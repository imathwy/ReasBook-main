import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_53
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_54
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_65
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_66
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Algorithm_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators StrongConvex WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.15 lies in the Chapter 6 strong-convex conditional-gradient domain.

Mandatory domain-style sampling:
- `initialLinearizationGap` in `Definition_6_54`, the chapter source-facing owner of the initial
  quantity `V₀`;
- `Ψ ∈ 𝒮^0_σΨ(Q)` / `mem_S0On_iff` in `Definition_6_65`, the chapter owner for positive
  fixed-parameter strong convexity on the feasible set;
- `stronglyConvexCompositeErrorBound` in `Definition_6_66`, the chapter owner for the textbook
  error term `\hat B_{v,t}`;
- `LinearOracleCompositeMethod` in `Algorithm_6_4`, the chapter owner of the iterate/oracle data
  for method `(6.4.12)`.

Best owner abstraction:
- source-facing: the weighted upper bound for method `(6.4.12)` under the chapter strong-convexity
  owner, with initial quantity
  `initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0` and textbook error term
  `\hat B_{v,t}`;
- core/canonical: `LinearOracleCompositeMethod`, `Ψ ∈ 𝒮^0_σΨ(Q)`,
  `initialLinearizationGap`, and `stronglyConvexCompositeErrorBound`;
- bridge/view: `mem_S0On_iff`, used only to recover `0 < σΨ` and `StrongConvexOn Q σΨ Ψ`
  internally.

Primitive data:
- the feasible set `Q`, objective `f`, ambient regularizer `Ψ`, and method data;
- the weight sequence `a` and the Hölder-style parameters `v`, `Gv`, `D`.

Derived API:
- the weighted affine-linearization upper bound at time `t`;
- the specialized Chapter 6 error term initialized by the canonical starting gap
  `initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0`.
-/

-- Proof sketch: argue by induction on `t`. For the induction step, combine the one-step estimate
-- from method `(6.4.12)` with the strong convexity lower bound for `Ψ` at the oracle point
-- `v_t`, then apply the quadratic inequality
-- `⟪s, u⟫ + (σΨ / 2) ‖u‖² ≥ -(1 / (2 σΨ)) ‖s‖²` to
-- `s = ∇f(x_{t+1}) - ∇f(x_t)` and `u = x - v_t`. Finally insert the bound `(6.4.3)` and absorb
-- the resulting term into the Chapter 6 owner
-- `stronglyConvexCompositeErrorBound
--   (initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0) a v Gv D σΨ`.
/-- Theorem 6.15: if `Ψ` is `σ_Ψ`-strongly convex on the convex feasible set `Q`, method
`(6.4.12)` is run with positive weights `a_t > 0` and coefficients
`τ_t = a_{t+1} / A_{t+1}`, and the gradient differences satisfy the bound `(6.4.3)`, then for
every `t ≥ 0` and every feasible comparison point `x ∈ Q` the weighted composite objective at
`x_t` is bounded by the weighted affine linearizations at `x` plus the recursive error term
`\hat B_{v,t}` initialized by
`V₀ = initialLinearizationGap Q f (fun x : Q ↦ Ψ x) x₀`, where `x₀ = method.x0`. -/
theorem weighted_objective_upper_bound_of_strongly_convex_linear_oracle_composite_method
    {Q : Set E} {f Ψ : E → ℝ} {σΨ : ℝ}
    (hΨ : Ψ ∈ 𝒮^0_σΨ(Q))
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ,
        ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ≤
          (Real.rpow (a (t + 1)) v /
              Real.rpow (A[a](t.succ)) v) *
            Gv * Real.rpow D v)
    (t : ℕ) (x : Q) :
    A[a](t) * (f (method t) + Ψ (method t)) ≤
      (Finset.sum (Finset.range (t + 1)) fun k ↦
        a k *
          (f (method k) +
            inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
            Ψ x)) +
        stronglyConvexCompositeErrorBound
          (initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0) a v Gv D σΨ t := sorry

end
