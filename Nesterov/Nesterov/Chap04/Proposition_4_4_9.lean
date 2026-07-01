import Mathlib
import Nesterov.Chap04.Algorithm_4_4_1
import Nesterov.Chap04.Assumption_4_4_3
import Nesterov.Chap04.Definition_4_4_15
import Nesterov.Chap04.Proposition_4_4_8
import Nesterov.Chap04.Theorem_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open SmoothNonlinearEquationProblem
open scoped Manifold

variable {E₁ : Type u} {E₂ : Type v}

/- Proposition 4.4.9 lies in the modified Gauss--Newton / merit-threshold / attained
distance-to-solution-set domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics;
* `modifiedGaussNewtonQuadraticMeritThreshold` and
  `modifiedGaussNewton_large_value_oneStep_decrease` in `Theorem_4_4_3`, the source-facing
  threshold and uniform decrease owner that control the pre-entry phase;
* mathlib `LipschitzOnWith L (fderiv ℝ problem) Set.univ`, the canonical whole-space
  Jacobian-Lipschitz owner used by `Theorem_4_4_3`;
* `solutionSet` in `Definition_4_4_8`, the chapter owner for exact solutions of the nonlinear
  system;
* `solutionSublevelDistanceSet` and `infDist_eq_of_isLeast_solutionSublevelDistanceSet` in
  `Definition_4_4_15`, the source-facing attained-distance owner and the canonical bridge from
  that attained minimum to `Metric.infDist x₀ (solutionSet problem)`;
* `ModifiedGaussNewtonMethod.first_merit_le_three_halves_mul_L_mul_infDist_sq` in
  `Proposition_4_4_8`, the canonical first-step merit bound in terms of
  `Metric.infDist x₀ (solutionSet problem)` once the attained-distance owner is supplied;

Best owner abstraction:
* source-facing: the threshold regime
  `f(x_k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L`, the first iterate index that
  enters it, and the resulting complexity bounds together with the exact-solution distance from
  `x₀`;
* core/canonical: a modified Gauss--Newton method together with the whole-space Jacobian-Lipschitz
  owner on `problem` and the dual nondegeneracy owner already used in `Theorem_4_4_3`;
* bridge/view: the comparison that replaces the first post-initial merit term by the
  exact-solution `Metric.infDist` expression from Proposition 4.4.8.

Primitive data:
* the smooth nonlinear equation problem `problem`;
* the sharp merit scalarizer `φ`;
* the modified Gauss--Newton orbit `method`;
* the threshold parameters `σ` and `γφ`;
* the whole-space Jacobian-Lipschitz hypothesis on `problem`;
* for the distance comparison, the source-facing attained-distance datum
  `IsLeast (solutionSublevelDistanceSet problem f x₀) D` together with the first-step
  exact-solution quadratic upper-model hypothesis on `solutionSet problem`.

Derived API:
* the canonical least-entry statement cut out directly by the threshold inequality
  `IsLeast {k | ...} N`;
* the source-facing first-step entry-index bound
  `N ≤ 1 + (4L / (σ² γ_φ²)) f (method 1)` from Proposition 4.4.9 `(1)`;
* the exact-solution-distance consequence from Proposition 4.4.9 `(2)`;
* the auxiliary strengthening obtained by replacing the first post-initial merit value
  `f (method 1)` by the larger initial value `f x₀`;
* the `Metric.infDist` simplification of the first-step merit term from Proposition 4.4.8 using
  the same owner-level exact-solution quadratic upper-model input together with the attained
  distance owner from Definition 4.4.15.

This refinement keeps the source-facing first-entry problem, but removes the file-local quadratic
region wrapper in favor of the upstream threshold owner
`modifiedGaussNewtonQuadraticMeritThreshold` and the canonical least-entry-set formulation
`IsLeast {k | ...} N`. It also keeps the numbered proposition centered on the first post-initial
merit term `f (method 1)` supplied by the validated upstream owner in Proposition 4.4.8, together
with the canonical exact-solution distance consequence on `Metric.infDist x₀ (solutionSet
problem)` only after reinstating the attained-distance owner already required upstream in
Proposition 4.4.8. The stronger initial-merit estimate using `f x₀` is retained only as an
auxiliary companion. Since this is the whole-space case, Assumption 4.4.2 is discharged by
`IsSufficientlyLargeFeasibleSetAt.univ`, so the public smoothness input is exactly the canonical
Jacobian-Lipschitz owner from `Theorem_4_4_3`.
-/

section

open scoped ModifiedGaussNewtonLocalModelNotation

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

variable
    (problem : C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯)
    (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    {L0 : ℝ} (L : NNReal) (x0 : E₁)
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)

local notation "f" => meritFunctionReformulation problem φ
local notation "localModel" => ψ[problem; φ; fun x ↦ fderiv ℝ problem x]
local notation "𝓢" => solutionSet problem

-- Proof sketch: if `N = 0`, the bound is immediate. Otherwise every iterate `x_k` with
-- `1 ≤ k < N` still lies in the large-value regime, so the one-step decrease from
-- Theorem 4.4.3 applies for `k = 1, ..., N - 1`. Summing those decreases from the first
-- post-initial iterate yields the bound by `f(x₁)` instead of `f(x₀)`.
/-- Proposition 4.4.9 (1): if `N` is the first iterate index satisfying the threshold inequality
`f(x_N) < (σ² / (2L)) γ_φ²`, then
`N ≤ 1 + (4L / (σ² γ_φ²)) f(x₁)`, where `x₁ = method 1` and
`f = meritFunctionReformulation problem φ`. -/
theorem modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_one_add_scaled_firstMerit
    {σ γφ : ℝ}
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ | f (method k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L}
        N) :
    (N : ℝ) ≤
      1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) := sorry

-- Proof sketch: apply
-- `ModifiedGaussNewtonMethod.first_merit_le_three_halves_mul_L_mul_infDist_sq` with the same
-- owner-level exact-solution quadratic upper-model hypothesis on `𝓢 = solutionSet problem`
-- together with an attained minimum `hD` on `solutionSublevelDistanceSet problem f x₀`, then
-- multiply the resulting bound by `4 / (σ² γ_φ²)` and simplify the scalar expression.
/-- The first-step scalar bound `1 + (4L / (σ² γ_φ²)) f(x₁)` is at most
`1 + 6 ((L * Metric.infDist x₀ (solutionSet problem)) / (σ γ_φ))²`, where
`f = meritFunctionReformulation problem φ` and `x₁ = method 1`, provided the first local model
at `x₀` satisfies the same quadratic upper estimate on exact solutions in
`𝓢 = solutionSet problem` as in Proposition 4.4.8 and the attained distance from Definition
4.4.15 is realized by some `D`. This is the bridge used in
Proposition 4.4.9 (2). -/
theorem modifiedGaussNewton_firstMeritBound_le_distanceBound
    (σ γφ : ℝ)
    {D : ℝ}
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D)
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓢 →
        localModel x0 y ≤ (L / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) :
    1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) ≤
      1 + 6 * ((((L : ℝ) * Metric.infDist x0 𝓢) / (σ * γφ)) ^ (2 : ℕ)) := sorry

-- Proof sketch: combine the companion first-step entry-index bound with
-- `modifiedGaussNewton_firstMeritBound_le_distanceBound`, which replaces the first-step merit
-- expression by the exact-solution-distance bound from Proposition 4.4.8 under the same
-- first-step exact-solution quadratic upper-model hypothesis on `𝓢`, using the attained-distance
-- owner from Definition 4.4.15.
/-- Proposition 4.4.9 (2): if `N` is the first iterate index satisfying the threshold inequality
`f(x_N) < (σ² / (2L)) γ_φ²`, then
`N ≤ 1 + 6 ((L * Metric.infDist x₀ (solutionSet problem)) / (σ γ_φ))²`, where
`f = meritFunctionReformulation problem φ`, provided the first local model at `x₀` satisfies the
same quadratic upper estimate on exact solutions in `𝓢 = solutionSet problem` as in
Proposition 4.4.8 and the attained distance from Definition 4.4.15 is realized by some `D`. -/
theorem modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_distanceBound
    {σ γφ : ℝ}
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ | f (method k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L}
        N)
    {D : ℝ}
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D)
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓢 →
        localModel x0 y ≤ (L / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) :
    (N : ℝ) ≤ 1 + 6 * ((((L : ℝ) * Metric.infDist x0 𝓢) / (σ * γφ)) ^ (2 : ℕ)) := sorry

-- Proof sketch: `f (method 1) ≤ f x₀` by monotonicity of the merit values along the modified
-- Gauss--Newton orbit, so the source-facing estimate from Proposition 4.4.9 (1) strengthens to
-- the same coefficient applied to the initial merit value.
/-- Auxiliary strengthening: the first-entry bound from Proposition 4.4.9 (1) remains valid after
replacing the first post-initial merit value `f(x₁)` by the larger initial merit value `f(x₀)`. -/
theorem modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_initialMerit
    {σ γφ : ℝ}
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ | f (method k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L}
        N) :
    (N : ℝ) ≤
      1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f x0 := sorry

end
