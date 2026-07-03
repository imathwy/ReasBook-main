import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_13 (from Chap06) -/
open scoped BigOperators
open scoped StandardSimplex

noncomputable section

/- Definition 6.13 lies in the finite simplex / Euclidean prox-function domain.

Sampled owner declarations:
* mathlib `stdSimplex`, the canonical owner of the standard simplex;
* mathlib `stdSimplex_eq_inter`, the canonical set-level expansion of simplex membership;
* mathlib `stdSimplex.barycenter` and `stdSimplex.barycenter_apply`, the canonical simplex center;
* project `quadraticDistanceTo`, the chapter owner of the Euclidean prox term.

Best owner abstraction:
* source-facing: the Euclidean prox function on `Δ_n` centered at the canonical simplex
  barycenter;
* core/canonical: `stdSimplex.barycenter` and `quadraticDistanceTo` on
  `EuclideanSpace ℝ (Fin n)`, together with the canonical simplex owner `stdSimplex`;
* bridge/view: the Euclidean-coordinate realization `stdSimplexBarycenterEuclidean n`, and
  restriction of the Euclidean prox owner along the coordinate equivalence
  `EuclideanSpace.equiv (Fin n) ℝ`.

Primitive data:
* the positive dimension `n : ℕ+`.

Derived API:
* the upstream Euclidean bridge `stdSimplexBarycenterEuclidean n`;
* the coordinate formula for the Euclidean prox function.

Source/core/bridge triage:
* core/canonical: `stdSimplex.barycenter`;
* bridge/view: `stdSimplexBarycenterEuclidean` from `Lemma_6_3`;
* the prox function is then the restriction of the Euclidean owner
  `quadraticDistanceTo (stdSimplexBarycenterEuclidean n)` along
  `(EuclideanSpace.equiv (Fin n) ℝ).symm`.

The duplicate public owner `simplexUniformPoint` has been deleted. Its only content was the earlier
Euclidean realization of the canonical simplex barycenter, so keeping it violated the project’s
owner/bridge discipline. The prior `simplexEuclideanProxFunction` body also applied
`quadraticDistanceTo` directly on the subtype carrier `Fin n → ℝ`, which silently switched the
ambient norm to the product sup norm; the corrected bridge keeps the Euclidean owner on
`EuclideanSpace ℝ (Fin n)` via `stdSimplexBarycenterEuclidean`. -/

/-- Definition 6.13: on `Δ_n`, the Euclidean prox choice is the restriction of the ambient
Euclidean prox owner centered at the canonical simplex barycenter `(1 / n, ..., 1 / n)`. The
simplex subtype is viewed in Euclidean coordinates through `(EuclideanSpace.equiv (Fin n) ℝ).symm`.
-/
abbrev simplexEuclideanProxFunction (n : ℕ+) : Δ[n] → ℝ :=
  fun x ↦
    quadraticDistanceTo (stdSimplexBarycenterEuclidean n) ((EuclideanSpace.equiv (Fin n) ℝ).symm x)

-- Proof sketch: unfold `simplexEuclideanProxFunction`; then expand `quadraticDistanceTo` at the
-- Euclidean center `stdSimplexBarycenterEuclidean n`, rewrite the squared Euclidean norm by
-- `EuclideanSpace.real_norm_sq_eq`, evaluate the transported simplex point coordinatewise through
-- `EuclideanSpace.equiv`, and use `stdSimplex.barycenter_apply`.
/-- Expanding `simplexEuclideanProxFunction n` gives the textbook formula
`(1 / 2) * Σ_i (x_i - 1 / n)^2`. -/
theorem simplexEuclideanProxFunction_apply (n : ℕ+) (x : Δ[n]) :
    simplexEuclideanProxFunction n x =
      (1 / 2 : ℝ) * ∑ i : Fin n, (x i - (1 : ℝ) / n) ^ (2 : ℕ) := sorry

/-! ### Lemma_6_13 (from Chap06) -/
noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-
Lemma 6.13 lies in Chapter 6's excessive-gap / smoothed-primal-objective domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjective` and `smoothedPrimalObjective_apply` in `Chap06/Definition_6_30`, the
  chapter owner of the smoothed primal value `f_{μ₂}`;
- `smoothed_primal_objective_at_x0_le_dual_value_at_V` in `Chap06/Lemma_6_2_8`, the existing
  chapter theorem already stated on the owner surface `smoothedPrimalObjective`;
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the later Chapter 6 owner for the
  direction `f_{μ₂}(\bar x) ≤ φ(\bar u)`.

Best owner abstraction:
- source-facing: the textbook inequality at `\bar x = x₀(u₀)` and `\bar u = V(u₀)`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: this recall surface, which reuses the earlier owner theorem directly.

Primitive data:
- the primal-dual data `A`, `Q₂`, `hatf`, `hatφ`, `d₂`;
- the selections `x₀`, `V`, the base point `u₀`, and the smoothing constant `μ₂`;
- the Lipschitz and penalty-corrected model assumptions already used in `Lemma_6_2_8`.

Derived API:
- the owner theorem in `Lemma_6_2_8`;
- later reformulations such as `satisfiesExcessiveGapCondition`.

The previous version duplicated the owner theorem under a second local name. This file now keeps
Lemma 6.13 as a direct recall of the canonical Chapter 6 declaration instead of a parallel theorem
shell.
-/

/-
Lemma 6.13 recalls the Chapter 6 owner theorem for the one-point excessive-gap inequality at
`barx = x₀(u₀)` and `baru = V(u₀)`.
-/
recall smoothed_primal_objective_at_x0_le_dual_value_at_V
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₂ : Set E₂}
    {φ hatφ : E₂ → ℝ} {hatf : E₁ → ℝ} {d₂ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {V : E₂ → E₂} {u₀ : E₂} {μ₂ : NNReal}
    (hQ₂_convex : Convex ℝ Q₂)
    (hu₀ : u₀ ∈ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    (hφ_gradient_lipschitz :
      LipschitzOnWith μ₂ (fun u ↦ gradientWithin φ Q₂ u) Q₂)
    (hV_max :
      IsMaxOn
        (fun u ↦
          φ u₀ +
            inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
              ((μ₂ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ))
        Q₂
        (V u₀))
    (hφ_eq :
      φ u₀ = -hatφ u₀ + A (x₀ u₀) u₀ + hatf (x₀ u₀))
    (hgradφ_eq :
      gradientWithin φ Q₂ u₀ =
        (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀)) - gradientWithin hatφ Q₂ u₀)
    (hhatφ_model :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        -hatφ u ≤
          -hatφ u₀ - inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) +
            (μ₂ : ℝ) * d₂ u -
            ((μ₂ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ)) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ (μ₂ : ℝ) (x₀ u₀) ≤ φ (V u₀)

end

/-! ### Proposition_6_13 (from Chap06) -/
open Matrix

noncomputable section

open scoped Matrix.Norms.L2Operator

/- Proposition 6.13 lies in the Euclidean matrix operator-norm / Gram-spectrum domain.

Primary domain:
- real matrices equipped with the Euclidean induced operator norm.

Sampled owner-style declarations:
- `Matrix.greatestEigenvalue` and the notation `λ_max(H)` in `Chap04/Definition_4_1_6`, the
  project owner for the largest real spectral value;
- mathlib's scoped `Matrix.Norms.L2Operator` norm `‖A‖`, the canonical Euclidean operator norm on
  matrices;
- the Gram matrix expression `Aᵀ * A`, whose largest eigenvalue controls the Euclidean operator
  norm.

Best owner abstraction:
- source-facing: the Euclidean operator norm of a real matrix;
- core/canonical: the ambient `Matrix.Norms.L2Operator` norm together with `λ_max`;
- bridge/view: the equivalent `sSup (spectrum ℝ (Aᵀ * A))` formulation used downstream.
-/

-- Proof sketch: square the Euclidean operator norm, rewrite `‖A x‖^2` as the Rayleigh quotient
-- `xᵀ (Aᵀ * A) x`, identify its maximum over the unit sphere with `λ_max(Aᵀ * A)`, and then take
-- square roots.
/-- Proposition 6.13: for a real matrix `A`, the operator norm induced by the Euclidean norms on
`ℝ^n` and `ℝ^m` is the square root of the largest eigenvalue of the Gram matrix `Aᵀ * A`. -/
theorem l2OperatorNorm_eq_sqrt_greatestEigenvalue_transpose_mul_self
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Real.sqrt (λ_max((Aᵀ * A : Matrix (Fin n) (Fin n) ℝ))) := sorry

-- Proof sketch: unfold `λ_max` in the main theorem as the supremum of the real spectrum of the
-- Gram matrix `Aᵀ * A`.
/-- Rewriting the Euclidean operator norm formula through the definition
`λ_max(H) = sSup (spectrum ℝ H)` recovers the spectrum-supremum form used elsewhere in the
chapter. -/
theorem l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Real.sqrt (sSup (spectrum ℝ (Aᵀ * A))) := sorry

end

/-! ### Theorem_6_13 (from Chap06) -/
open scoped WeightSequenceNotation

universe u

section

variable {X : Type u}

/- Theorem 6.13 lies in Chapter 6's accumulated-weight / oracle-error normalization domain.

Sampled owner-style declarations:
- `accumulatedWeights` with notation `A[a](t)` in `Definition_6_53`, the chapter owner for the
  accumulated weights `A_t`;
- `linearOptimizationOracleErrorBound` in `Definition_6_54`, the chapter owner for the error term
  `B_{ν,t}`;
- `weighted_objective_upper_bound_of_linear_oracle_composite_method` in `Theorem_6_12`, the
  upstream weighted estimate that Theorem 6.13 normalizes;
- `le_div_iff₀`, the arithmetic theorem used internally to divide by a positive scalar.

Best owner abstraction:
- source-facing owners `A[a](t)` and `linearOptimizationOracleErrorBound V₀ a G_ν D ν t`.

Primitive data:
- the positivity hypothesis `hAt : 0 < A[a](t)`;
- the weighted inequality
  `A[a](t) * (fbar xt - fbar xs) ≤ linearOptimizationOracleErrorBound V₀ a G_ν D ν t`.

Derived API:
- the normalized objective-gap bound obtained by dividing by `A[a](t)`.

Source/core/bridge triage:
- source-facing: the Chapter 6 step from the weighted bound to the normalized gap estimate;
- core/canonical: the chapter owners `accumulatedWeights` and
  `linearOptimizationOracleErrorBound`;
- bridge/view: this theorem, whose proof internally reuses `le_div_iff₀`.

The interval condition `ν ∈ (0, 1]` belongs to the upstream construction of
`linearOptimizationOracleErrorBound`; it is not primitive data for this normalization step.
-/
-- Proof sketch: apply `le_div_iff₀` to divide the Chapter 6 weighted objective-gap inequality by
-- the positive scalar `A[a](t)`.
/-- Theorem 6.13: if `A_t > 0` and the weighted objective gap satisfies
`A_t (\bar f(x_t) - \bar f(x_s)) ≤ B_{ν,t}` with
`B_{ν,t} = linearOptimizationOracleErrorBound V₀ a G_ν D ν t`, then
`\bar f(x_t) - \bar f(x_s) ≤ B_{ν,t} / A_t`. Here `t : ℕ` encodes the hypothesis `t ≥ 0`. -/
theorem objective_gap_le_error_bound_div_accumulated_weight
    (fbar : X → ℝ) (xt xs : X) (a : ℕ → ℝ) (V0 Gν D : ℝ)
    {ν : ℝ} {t : ℕ}
    (hAt : 0 < A[a](t))
    (hweighted :
      A[a](t) * (fbar xt - fbar xs) ≤
        linearOptimizationOracleErrorBound V0 a Gν D ν t) :
    fbar xt - fbar xs ≤
      linearOptimizationOracleErrorBound V0 a Gν D ν t / A[a](t) := by
  exact (le_div_iff₀ hAt).2 (by simpa [mul_comm] using hweighted)

end
