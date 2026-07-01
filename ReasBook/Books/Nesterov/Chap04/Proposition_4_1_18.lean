import Mathlib
import Nesterov.Chap04.Definition_4_1_3
import Nesterov.Chap04.Definition_4_1_2
import Nesterov.Chap04.Definition_4_1_10
import Nesterov.Chap04.Algorithm_4_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Proposition 4.1.18 lies in the Chapter 4 strong-convex cubic-regularization complexity domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the chapter owner for a cubic-regularization
  trajectory, regularization schedule, and accepted-step inequality;
* `HasLipschitzContinuousHessian` in `Definition_4_2_7` and `HessianLipschitzOn` in
  `Definition_4_1_2`, the canonical Chapter 4 Hessian-Lipschitz owners;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Theorem_4_2_2`, which keeps
  the initial level-set radius control in the canonical weak form
  `∀ x, f x ≤ f x₀ → ‖x - xStar‖ ≤ D` instead of an attainment witness;
* `NonlinearConvexTransformation` in `Definition_4_1_10`, the source-facing owner for the
  transformed problem data;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, which packages
  a “first index” statement canonically via `IsLeast`.

Source/core/bridge triage:
* source-facing: the two global first-accuracy-index complexity bounds in Proposition 4.1.18;
* core/canonical: `CubicRegularizationMethod`, `HasLipschitzContinuousHessian`,
  `HessianLipschitzOn`, `NonlinearConvexTransformation`, and `IsLeast`;
* bridge/view: the scalar threshold / bound expressions below.

Primitive data:
* the objective, strong-convexity, and Hessian-Lipschitz hypotheses;
* the cubic-regularization method owner;
* the chosen minimizer and bounded-initial-sublevel radius data;
* in the transformed theorem, the nonlinear-convex-transformation owner.

Derived API:
* the first accuracy index, expressed canonically as an `IsLeast` witness;
* the displayed scalar thresholds and iteration bounds, kept as theorem-local textbook notation
  rather than one-off public wrapper definitions.

This file keeps the proposition source-facing, but refines its public API to the existing chapter
owners for cubic regularization and Hessian-Lipschitz control, uses the canonical least-index
predicate `IsLeast`, and demotes the scalar helper expressions to local notation because they do
not form a reusable owner API elsewhere in the chapter.
-/

section StrongConvexCubicRegularization

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal} {x0 : E}
variable {μ D ε : ℝ} {N : ℕ}

local notation "χ" => ((L : ℝ) * D) / μ
local notation "ω₀" => μ ^ (3 : ℕ) / (18 * (L : ℝ) ^ (2 : ℕ))
local notation "B" =>
  (25 / 4 : ℝ) * Real.sqrt χ +
    Real.logb 3
      (Real.logb 4 (1 / ε) +
        Real.logb 4 (2 * μ ^ (3 : ℕ) / (9 * (L : ℝ) ^ (2 : ℕ))))

-- Proof sketch: use strong convexity to identify `xStar` as the minimizer and `hlevel` as the
-- radius control on the initial sublevel set `f ⁻¹' Set.Iic (f x0)`. The cubic acceptance data is
-- part of the owner `CubicRegularizationMethod`, and the global Hessian-Lipschitz assumption is
-- recorded by the canonical owner hypothesis `f ∈ C22[L]`. Apply the first-phase and
-- second-phase strong-convex cubic bounds, split at
-- `ω₀ = μ^3 / (18 L^2)`, and conclude from the least-index hypothesis
-- `IsLeast {k | f (x_k) - f(x*) ≤ ε} N`.
/-- Proposition 4.1.18: if a cubic-regularization method for `f` starts at `x₀`, `f` is
`μ`-strongly convex with minimizer `xStar`, its Hessian is globally `L`-Lipschitz, the sublevel
set `{x | f x ≤ f x₀}` is contained in the closed ball of radius `D` around `xStar`, and `N` is
the first iterate
whose objective gap is at most `ε ∈ (0, μ^3 / (18 L^2)]`, then
`N ≤ 6.25 √(L D / μ) + log_3 (log_4 (1 / ε) + log_4 (2 μ^3 / (9 L^2)))`. -/
theorem strongConvex_cubicRegularization_firstAccuracyIndex_le_globalIterationBound
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 (L : ℝ) x0)
    (xStar : E)
    (hμ : 0 < μ)
    (hf_hessian : f ∈ C22[L])
    (hf_strong : StrongConvexOn Set.univ μ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (hlevel : ∀ ⦃x : E⦄, f x ≤ f x0 → ‖x - xStar‖ ≤ D)
    (hε : ε ∈ Set.Ioc 0 ω₀)
    (hN : IsLeast {k : ℕ | f (method k) - f xStar ≤ ε} N) :
    (N : ℝ) ≤ B := sorry

end StrongConvexCubicRegularization

section NonlinearTransformationStrongConvexCubicRegularization

variable (problem : NonlinearConvexTransformation E)
variable {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal} {𝓕 : Set E}
variable {μ ε : ℝ} {N : ℕ}

local notation "ω₀" =>
  μ ^ (3 : ℕ) / (18 * problem.sigma ^ (6 : ℕ) * (L : ℝ) ^ (2 : ℕ))
local notation "B" =>
  (25 / 4 : ℝ) * Real.sqrt ((problem.sigma / μ) * (L : ℝ) * problem.D) +
    Real.logb 3
      (Real.logb 4 (1 / ε) +
        Real.logb 4
          (2 * μ ^ (3 : ℕ) / (9 * problem.sigma ^ (6 : ℕ) * (L : ℝ) ^ (2 : ℕ))))

-- Proof sketch: apply the strong-convex nonlinear-transformation phase analysis to the canonical
-- transformed minimizer `problem.xStar`. The cubic acceptance data is built into the owner
-- `CubicRegularizationMethod`, while the transformed Hessian-Lipschitz hypothesis is carried by
-- the owner `HessianLipschitzOn L 𝓕 problem` together with the sublevel containment
-- `hlevel_subset`. The constants `problem.sigma` and `problem.D` provide the distortion and radius
-- terms, and the same three-phase counting argument yields the displayed least-index bound.
/-- The nonlinear-transformation companion bound: for a nonlinear change of variables with convex
potential `φ`, if `φ` is `μ`-strongly convex, the transformed objective has
`L`-Lipschitz Hessian on a comparison set containing its initial sublevel set, and `N` is the
first iterate whose objective gap drops below `ε ∈ (0, μ^3 / (18 σ^6 L^2)]`, then
`N ≤ 6.25 √((σ / μ) L D) + log_3 (log_4 (1 / ε) + log_4 (2 μ^3 / (9 σ^6 L^2)))`. -/
theorem nonlinearTransformation_strongConvex_firstAccuracyIndex_le_globalIterationBound
    (hproblem : HessianLipschitzOn L 𝓕 problem)
    (method :
      CubicRegularizationMethod
        problem
        stepMap
        L0 (L : ℝ) problem.x0)
    (hlevel_subset :
      problem ⁻¹' Set.Iic (problem problem.x0) ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (hε : ε ∈ Set.Ioc 0 ω₀)
    (hN :
      IsLeast
        {k : ℕ | problem (method k) - problem problem.xStar ≤ ε}
        N) :
    (N : ℝ) ≤ B := sorry

end NonlinearTransformationStrongConvexCubicRegularization
