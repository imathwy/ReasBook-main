import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_17
import LecturesConvexOptimization_Nesterov_2018.Chap02.Lemma_2_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex optimal-method objective-gap rates on a real Hilbert space.

Owner declarations sampled before refining this file:
* `GeneralOptimalMethodScheme` in `Algorithm_2_2` owns the optimal-method trajectory together
  with the canonical scalar sequences `αₖ`, `γₖ`, and `λₖ`;
* `OptimalMethodRecurrence.weight_bounds` in `Lemma_2_10` owns the hyperbolic and quadratic
  bounds on the canonical weight `λₖ` for `γ₀ ∈ (μ, 3L + μ]`;
* `OptimalMethodRecurrence.hyperbolic_bound_le_quadratic_bound` in `Lemma_2_10` owns the scalar
  hyperbolic-versus-quadratic factor comparison on the recurrence side;
* `estimating_sequence_suboptimality_le` in `Theorem_2_19` owns the estimating-sequence
  objective-gap estimate;
* the owner-style summary in `Definition_2_20` identifies whole-space strong convexity,
  `C¹` regularity, and gradient Lipschitzness as the primitive objective data in Chapter 2.

Best owner abstraction: the public object here is the owner method
`method : GeneralOptimalMethodScheme ... (3 * L + μ)`. The explicit hyperbolic and quadratic
right-hand sides are derived by combining the owner suboptimality theorem with the owner weight
bound, so this file states those rates directly rather than keeping parallel local bound
definitions.

Primitive data:
* the objective and its whole-space strong-convexity / smoothness hypotheses;
* a minimizer `xStar`;
* the owner method with `γ₀ = 3L + μ`.

Derived API:
* the explicit quadratic objective-gap estimate;
* the explicit hyperbolic objective-gap estimate;
* the comparison of the two displayed right-hand sides. -/

section OptimalMethodRates

variable {μ L gamma0 : ℝ} {f : E → ℝ}
variable {xStar : E}
variable {x0 : E}

/-- For any optimal-method scheme with `μ > 0` and initial curvature `γ₀ ∈ (μ, 3L + μ]`, the
objective gap is bounded above by the corresponding hyperbolic estimate with the canonical initial
energy `f(x₀) - f(x*) + (γ₀ / 2) ‖x₀ - x*‖²`. -/
theorem optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * μ *
        (f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) /
        ((gamma0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
            (2 : ℕ)) := by
  sorry

/-- For any optimal-method scheme with `μ > 0` and initial curvature `γ₀ ∈ (μ, 3L + μ]`, the
hyperbolic estimate yields the quadratic `O((k + 1)⁻²)` objective-gap upper bound with the same
canonical initial energy. -/
theorem optimal_method_quadratic_suboptimality_le_of_mem_Ioc
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
        (f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  sorry

/-- Helper for Theorem 2.20: the hyperbolic factor is bounded above by the quadratic factor after
rewriting the denominator through `sinh`.

This is the scalar comparison underlying
`OptimalMethodRecurrence.hyperbolic_bound_le_quadratic_bound`, but without the recurrence-side
restriction `q_f ∈ (0, 1)`. -/
-- Proof sketch: write `exp t - exp (-t) = 2 sinh t` with
-- `t = ((k + 1) / 2) * sqrt q_f`, use `t ≤ sinh t` for `t ≥ 0`, square both sides, and then
-- rewrite `q_f = μ / L`.
lemma optimal_method_hyperbolic_factor_le_quadratic_factor
    (hμ : 0 < μ) (hL : 0 < L) (k : ℕ) :
    μ /
        (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
          Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ) ≤
      L / (k + 1 : ℝ) ^ (2 : ℕ) := by
  let qμL : ℝ := μ / L
  let t : ℝ := ((k + 1 : ℝ) / 2) * Real.sqrt qμL
  let d : ℝ := Real.exp t - Real.exp (-t)
  have hq_nonneg : 0 ≤ qμL := div_nonneg hμ.le hL.le
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have htsinh : t ≤ Real.sinh t := (Real.self_le_sinh_iff).2 ht_nonneg
  have hsinh_sq :
      t ^ (2 : ℕ) ≤ Real.sinh t ^ (2 : ℕ) := by
    have hsinh_nonneg : 0 ≤ Real.sinh t := (Real.sinh_nonneg_iff).2 ht_nonneg
    nlinarith
  have hqf_sq :
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) = 4 * t ^ (2 : ℕ) := by
    dsimp [t]
    nlinarith [Real.sq_sqrt hq_nonneg]
  have hd_sq :
      d ^ (2 : ℕ) = 4 * Real.sinh t ^ (2 : ℕ) := by
    dsimp [d]
    rw [Real.sinh_eq]
    ring
  have hfactor :
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
    calc
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) = 4 * t ^ (2 : ℕ) := hqf_sq
      _ ≤ 4 * Real.sinh t ^ (2 : ℕ) := by
            gcongr
      _ = d ^ (2 : ℕ) := hd_sq.symm
  have hmul :
      μ * (k + 1 : ℝ) ^ (2 : ℕ) ≤ L * d ^ (2 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hfactor hL.le
    calc
      μ * (k + 1 : ℝ) ^ (2 : ℕ) = L * (qμL * (k + 1 : ℝ) ^ (2 : ℕ)) := by
        dsimp [qμL]
        field_simp [hL.ne']
      _ ≤ L * d ^ (2 : ℕ) := hscaled
  have hd_pos : 0 < d := by
    dsimp [d]
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    refine sub_pos.mpr ?_
    exact Real.exp_lt_exp.mpr (by linarith)
  have hk_sq_pos : 0 < (k + 1 : ℝ) ^ (2 : ℕ) := by
    positivity
  refine (div_le_div_iff₀ (by positivity) hk_sq_pos).2 ?_
  simpa [d, t, qμL, mul_assoc, mul_left_comm, mul_comm] using hmul

variable {x0 : E}

/-- Theorem 2.20 (1): for a smooth strongly convex minimization problem with `γ₀ = 3L + μ`, the
iterate sequence of the optimal method satisfies the `O((k + 1)⁻²)` function-value bound. -/
-- Proof sketch: apply `estimating_sequence_suboptimality_le` to the owner estimating sequence
-- attached to `method`. Then use `OptimalMethodRecurrence.weight_bounds` specialized to
-- `γ₀ = 3L + μ` to bound the canonical weight `λₖ`, and bound the initial energy by the smooth
-- upper quadratic estimate at the minimizer `xStar`.
theorem optimal_method_quadratic_suboptimality_le
    (method : GeneralOptimalMethodScheme f L μ x0 (3 * L + μ))
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (2 * (4 + q[μ, L]) * L * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  sorry

/-- Theorem 2.20 (2): if `μ > 0`, then the iterate sequence of the optimal method satisfies the
sharper hyperbolic function-value estimate. -/
-- Proof sketch: combine `estimating_sequence_suboptimality_le` with the positive-`μ` upper bound
-- on the owner weight `λₖ` from `OptimalMethodRecurrence.weight_bounds` specialized to
-- `γ₀ = 3L + μ`, and rewrite the resulting factor using `q[μ, L] = μ / L`.
theorem optimal_method_hyperbolic_suboptimality_le
    (method : GeneralOptimalMethodScheme f L μ x0 (3 * L + μ))
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (2 * (4 + q[μ, L]) * μ * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ)) := by
  sorry

end OptimalMethodRates

section ExplicitBoundComparison

variable {F : Type u} [NormedAddCommGroup F]
variable {μ L : ℝ}

/-- Theorem 2.20 (3): for `μ > 0`, the hyperbolic upper bound from the optimal-method estimate is
itself bounded above by the quadratic `O((k + 1)⁻²)` bound. -/
-- Proof sketch: compare the hyperbolic denominator with its quadratic lower bound from the scalar
-- recurrence analysis for the owner weights, equivalently the second inequality in
-- `OptimalMethodRecurrence.weight_bounds` specialized to `γ₀ = 3L + μ`.
theorem optimal_method_hyperbolic_bound_le_quadratic_bound
    (hμ : 0 < μ) (hL : 0 < L)
    (x0 xStar : F)
    (k : ℕ) :
    (2 * (4 + q[μ, L]) * μ * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ)) ≤
      (2 * (4 + q[μ, L]) * L * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  let c : ℝ := (2 * (4 + q[μ, L]) * ‖x0 - xStar‖ ^ (2 : ℕ)) / 3
  have hbase :=
    optimal_method_hyperbolic_factor_le_quadratic_factor hμ hL k
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hc_nonneg
  simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

end ExplicitBoundComparison

end
