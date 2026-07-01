import Mathlib
import Nesterov.Chap04.Definition_4_1_3
import Nesterov.Chap04.Definition_4_1_2
import Nesterov.Chap04.Definition_4_1_10
import Nesterov.Chap04.Algorithm_4_1_5
import Nesterov.Chap04.Lemma_4_1_6
import Nesterov.Chap04.Theorem_4_1_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.1.9 lies in the nonlinear-transformation / strong-convex cubic-regularization rate
domain.

Sampled owner declarations:
* `NonlinearConvexTransformation` in `Definition_4_1_10`, the source-facing owner for the
  transformed objective, transported minimizer, and level-set constants `σ` and `D`;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the chapter owner for the iterate sequence
  and regularization schedule;
* `HessianLipschitzOn` in `Definition_4_1_2`, the canonical chapter owner for local convex
  Hessian-Lipschitz control on a comparison set;
* `CubicRegularizationMethod.objective_succ_le_feasibleComparison` in `Theorem_4_1_8`, the
  owner-level one-step feasible comparison estimate used by the transformed cubic-rate bounds.

Source/core/bridge triage:
* source-facing: the first-phase decay, termination, and second-phase superlinear estimates for a
  strongly convex transformed objective;
* core/canonical: `NonlinearConvexTransformation`, `CubicRegularizationMethod`, and
  `StrongConvexOn Set.univ μ problem.φ`;
* bridge/view: the scalar threshold `\tilde ω`.

Primitive data:
* the transformed problem `problem`;
* the comparison set `𝓕` together with the sublevel containment hypothesis from Theorem 4.1.8;
* the canonical smoothness owner `HessianLipschitzOn L 𝓕 problem.objective`;
* the cubic-regularization method `method`;
* the strong-convexity parameter `μ > 0`.

Derived API:
* the threshold `\tilde ω = 2 L σ^3 / μ^(3/2)`;
* the objective gaps `f(x_k) - f(x*)`;
* the owner-level one-step feasible comparison estimate from
  `CubicRegularizationMethod.objective_succ_le_feasibleComparison`;
* the phase-wise gap estimates below.

The monotonicity needed to keep the trajectory inside the initial sublevel set is already derived
from the chapter owner `CubicRegularizationMethod`, and Theorem 4.1.8 already upgrades the
one-step feasible comparison estimate to the owner theorem
`CubicRegularizationMethod.objective_succ_le_feasibleComparison`. This refinement therefore keeps
the Theorem 4.1.8 comparison-set hypotheses explicit, preserves the source-facing theorem family
semantics, and derives the one-step feasible comparison bound from the method owner rather than
keeping it as parallel public data. -/

/-- The threshold `\tilde ω = 2 L σ^3 / μ^(3/2)` governing the two-phase convergence estimate for
cubic regularization after a nonlinear transformation of a strongly convex function. -/
abbrev nonlinearTransformationStrongConvexCubicThreshold
    (L σ μ : ℝ) : ℝ :=
  (2 * L * σ ^ (3 : ℕ)) / Real.rpow μ (3 / 2 : ℝ)

/-- Expanding `nonlinearTransformationStrongConvexCubicThreshold L σ μ` recovers the textbook
formula `\tilde ω = 2 L σ^3 / μ^(3/2)`. -/
@[simp]
theorem nonlinearTransformationStrongConvexCubicThreshold_def
    (L σ μ : ℝ) :
    nonlinearTransformationStrongConvexCubicThreshold L σ μ =
      (2 * L * σ ^ (3 : ℕ)) / Real.rpow μ (3 / 2 : ℝ) :=
  rfl

section NonlinearTransformationStrongConvexCubicRate

variable (problem : NonlinearConvexTransformation E)
variable (𝓕 : Set E) (μ : ℝ) {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal}
variable
  (method :
    CubicRegularizationMethod
      problem
      stepMap
      L0 (L : ℝ) problem.x0)

local notation "f" => problem
local notation "𝓛₀" => f ⁻¹' Set.Iic (f problem.x0)
local notation "ω̃" =>
  nonlinearTransformationStrongConvexCubicThreshold (L : ℝ) problem.sigma μ
local notation "Δ" => fun k : ℕ ↦ f (method k) - f problem.xStar

variable
  (hlevel_subset : 𝓛₀ ⊆ 𝓕)
  [HessianLipschitzOn L 𝓕 problem]
  (hμ : 0 < μ)
  (hphi_strong : StrongConvexOn Set.univ μ problem.φ)

-- Proof sketch: apply
-- `method.objective_succ_le_feasibleComparison hlevel_subset`
-- from Theorem 4.1.8 at the comparison point `v (α • u* + (1 - α) • u (x_k))`, then use
-- convexity of `φ` and strong convexity at `u*` to bound the objective and distance terms.
-- Rewrite the resulting scalar recursion in terms of
-- `\tilde ω = nonlinearTransformationStrongConvexCubicThreshold L σ μ`, and iterate the same
-- first-phase argument as in the star-convex model case.
/-- Theorem 4.1.9 (1): under the nonlinear-transformation assumptions from Theorem 4.1.8, if
`φ` is `μ`-strongly convex and the initial gap is at least `(4 / 9) * \tilde ω`, then every
iterate whose gap is still above that threshold satisfies the fourth-root decay bound. -/
theorem nonlinearTransformation_cubicRegularization_firstPhase_gap_bound
    (hgap0 :
      Δ 0 ≥ (4 / 9 : ℝ) * ω̃)
    (k : ℕ)
    (hk : Δ k ≥ (4 / 9 : ℝ) * ω̃) :
    Δ k ≤
      (Real.rpow (Δ 0) (1 / 4 : ℝ) -
        ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ)) ^
        (4 : ℕ) := sorry

-- Proof sketch: apply the first-phase scalar recursion from the previous theorem to the
-- normalized gaps `Δ_k = (f(x_k) - f(x*)) / \tilde ω`. The same argument as in the first phase
-- shows that this recursion cannot remain forever in the regime `Δ_k > 4 / 9`, so some iterate
-- must cross the threshold.
/-- Theorem 4.1.9 (2): under the same assumptions, the first phase ends at some index `k₀` where
`f(x_{k₀}) - f(x^*) ≤ (4 / 9) * \tilde ω`. -/
theorem nonlinearTransformation_cubicRegularization_firstPhase_terminates
    (hgap0 :
      Δ 0 ≥ (4 / 9 : ℝ) * ω̃) :
    ∃ k0 : ℕ,
      Δ k0 ≤ (4 / 9 : ℝ) * ω̃ := sorry

-- Proof sketch: once `f(x_k) - f(x*) ≤ (4 / 9) * \tilde ω`, the scalar upper bound obtained from
-- the comparison points
-- `v (α • u* + (1 - α) • u (x_k))` is minimized at `α = 1`, giving
-- `Δ_{k+1} ≤ (1 / 2) Δ_k^(3/2)` for `Δ_k = (f(x_k) - f(x*)) / \tilde ω`. Rewriting this bound
-- in terms of the original objective values yields the displayed superlinear recurrence.
/-- Theorem 4.1.9 (3): once an iterate reaches the threshold `(4 / 9) * \tilde ω`, every later
iterate satisfies the superlinear estimate
`f(x_{k+1}) - f(x^*) ≤ (1 / 2) (f(x_k) - f(x^*)) * sqrt ((f(x_k) - f(x^*)) / \tilde ω)`. -/
theorem nonlinearTransformation_cubicRegularization_secondPhase_gap_le_superlinear
    (k0 : ℕ)
    (hk0 : Δ k0 ≤ (4 / 9 : ℝ) * ω̃)
    (k : ℕ)
    (hk : k0 ≤ k) :
    Δ (k + 1) ≤
      (1 / 2 : ℝ) * Δ k * Real.sqrt (Δ k / ω̃) := sorry

end NonlinearTransformationStrongConvexCubicRate
