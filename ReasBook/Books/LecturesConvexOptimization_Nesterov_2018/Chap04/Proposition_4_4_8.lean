import Mathlib.Tactic.Recall
import Nesterov.Chap04.Algorithm_4_4_1
import Nesterov.Chap04.Definition_4_4_15
import Nesterov.Chap04.Proposition_4_4_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

/- Proposition 4.4.8 lies in the merit-reformulation / modified Gauss--Newton / attained
distance-to-solution-set domain.

Sampled owner-style declarations:
* `solutionSet` in `Definition_4_4_8`, the chapter owner for exact solutions of the nonlinear
  system;
* `solutionSublevelDistanceSet` and
  `solutionSublevelDistanceSet_eq_image_solutionSet_of_meritFunctionReformulation` in
  `Definition_4_4_15`, the source-facing attained-distance owner and its merit-reformulation
  bridge back to the full exact solution set;
* `meritFunctionReformulation` in `Definition_4_4_10`, the source-facing owner
  `x ↦ φ (F x)` for scalarized residual problems;
* `exact_solution_isMinOn_meritFunctionReformulation` in `Proposition_4_4_4`, the canonical
  bridge from an exact solution to a global minimizer of the merit reformulation;
* `Metric.infDist` and `Metric.isGLB_infDist`, the canonical metric owners for distance to the
  exact solution set.

Best owner abstraction:
* source-facing: the first-step merit-value estimate for Algorithm 4.4.1 relative to the exact
  solution distance minimum through `x₀`;
* core/canonical: `solutionSet problem`, `meritFunctionReformulation problem φ`, `IsMinOn`, and
  `Metric.infDist x₀ (solutionSet problem)`;
* bridge/view: the source-facing attained minimum on
  `((fun y ↦ ‖y - x₀‖) '' solutionSet problem)`.

Primitive data:
* a residual map `problem` with distinguished zero in the codomain;
* a merit scalarizer `φ`;
* in the algorithmic theorem, a modified Gauss--Newton method, an attained minimum
  `IsLeast (solutionSublevelDistanceSet problem f x₀) D`, and the exact-solution quadratic
  local-model estimate on `solutionSet problem`.

Derived API:
* exact solutions as global minimizers of `meritFunctionReformulation problem φ`;
* the owner-level bridge identifying `solutionSublevelDistanceSet problem f x₀` with the direct
  distance image of `solutionSet problem`;
* the metric reformulation over `Metric.infDist x₀ (solutionSet problem)`.

Source/core/bridge triage:
* `exact_solution_isMinOn_meritFunctionReformulation`: core/canonical;
* the attained-distance form of Proposition 4.4.8 as an owner theorem of
  `ModifiedGaussNewtonMethod`: source-facing;
* `ModifiedGaussNewtonMethod.first_merit_le_three_halves_mul_L_mul_infDist_sq`: bridge/view.

This refinement reuses the upstream exact-solution minimizer bridge from `Proposition_4_4_4` on
the intrinsic owner layer `meritFunctionReformulation problem φ`, restores the chapter owner
`solutionSublevelDistanceSet problem f x₀` for the source-facing minimum quantity `D`, and keeps
the metric `Metric.infDist` formulation on the exact solution set only as a companion bridge via
the owner-level identification from `Definition_4_4_15`.
-/

/- The exact-solution minimizer bridge is the upstream theorem
`exact_solution_isMinOn_meritFunctionReformulation`. -/
recall exact_solution_isMinOn_meritFunctionReformulation

section

open SmoothNonlinearEquationProblem
open scoped Manifold
open scoped ModifiedGaussNewtonLocalModelNotation

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {x0 : E₁}

local notation "f" => meritFunctionReformulation problem φ
local notation "localModel" => ψ[problem; φ; fun x ↦ fderiv ℝ problem x]
local notation "𝓢" => solutionSet problem

namespace ModifiedGaussNewtonMethod

-- Proof sketch: use the owner-level bridge from `Definition_4_4_15` to rewrite `hD` as an
-- attained minimum on the direct distance image of `𝓢 = solutionSet problem`, then choose an
-- exact solution `y ∈ 𝓢` with `‖y - x₀‖ = D`. Since `problem y = 0`, Proposition 4.4.4 gives
-- `f y = 0`. The hypothesis `hupper` is therefore exactly the needed quadratic estimate at `y`,
-- and Corollary 4.4.1 applied at `x₀ = method 0` gives `f(x₁) ≤ ((L + M₀) / 2) D²`. Finally use
-- `method.regularization_mem_Icc 0` to bound `M₀ ≤ 2L` and conclude `f(x₁) ≤ (3 / 2) L D²`.
/-- Proposition 4.4.8: if `D` is the attained minimum distance from `x₀` to the exact solution
sublevel-distance set `solutionSublevelDistanceSet problem f x₀` from Definition 4.4.15,
equivalently the direct distance image of `𝓢 = solutionSet problem` for the merit reformulation
`f = meritFunctionReformulation problem φ`, and the first modified Gauss--Newton local model at
`x₀` satisfies the exact-solution quadratic upper estimate on `𝓢`, then the first iterate of
Algorithm 4.4.1 obeys `f(x₁) ≤ (3 / 2) L D²`. -/
theorem first_merit_le_three_halves_mul_L_mul_sq_of_isLeastSolutionDistance
    {L0 L D : ℝ}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D)
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓢 →
        localModel x0 y ≤ (L / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) :
    f (method 1) ≤ (3 / 2 : ℝ) * L * D ^ (2 : ℕ) := sorry

-- Proof sketch: first rewrite the owner-level attained minimum `hD` as an attained minimum on
-- the direct distance image of `solutionSet problem` via
-- `solutionSublevelDistanceSet_eq_image_solutionSet_of_meritFunctionReformulation`, then apply
-- the canonical `Metric.infDist` bridge.
/-- Companion bridge: the source-facing attained-distance estimate from Proposition 4.4.8 may be
rephrased using the canonical metric quantity `Metric.infDist x₀ (solutionSet problem)` whenever
that infimum is attained by `D`; it uses the same exact-solution quadratic upper estimate on
`solutionSet problem`. -/
theorem first_merit_le_three_halves_mul_L_mul_infDist_sq
    {L0 L D : ℝ}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D)
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓢 →
        localModel x0 y ≤ (L / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) :
    f (method 1) ≤
      (3 / 2 : ℝ) * L * Metric.infDist x0 𝓢 ^ (2 : ℕ) := sorry

end ModifiedGaussNewtonMethod

end
