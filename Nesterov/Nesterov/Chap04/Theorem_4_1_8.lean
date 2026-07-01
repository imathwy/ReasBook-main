import Nesterov.Chap04.Definition_4_1_2
import Nesterov.Chap04.Definition_4_1_3
import Nesterov.Chap04.Definition_4_1_10
import Nesterov.Chap04.Algorithm_4_1_5
import Nesterov.Chap04.Lemma_4_1_5
import Nesterov.Chap04.Theorem_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient LevelSetNotation CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.1.8 lies in the nonlinear change-of-variables / cubic-regularization rate domain.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for local `C²`
  Hessian-Lipschitz control on a comparison set;
* `NonlinearConvexTransformation` in `Definition_4_1_10`, the source-facing owner for the change
  of variables `u`, the convex potential `φ`, the chosen minimizer `uStar`, and the constants
  `sigma` and `D`;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the chapter owner for the iterate sequence,
  regularization schedule, and accepted-step relation;
* `norm_sub_le_sigma_mul_norm_image_sub` in `Lemma_4_1_9`, the owner-level distortion theorem
  showing that the x-space distance bound is derived from the controlling image-side level set;
* `starConvex_cubicSegment_first_gap_le_half_LD_cube` and
  `starConvex_cubicSegment_gap_le_inverse_square_rate` in `Theorem_4_1_4`, the adjacent cubic
  rate owners whose scalar recursion is transported here to the nonlinear-transformation setting.

Source/core/bridge triage:
* source-facing: the transformed cubic-regularization rate statements for a nonlinear convex
  transformation;
* core/canonical: `HessianLipschitzOn L 𝓕 problem`,
  `NonlinearConvexTransformation E`, and `CubicRegularizationMethod`;
* bridge/view: the scalar rate bounds expressed with the transported radius `problem.sigma *
  problem.D`.

Primitive data:
* the nonlinear-convex-transformation owner `problem`;
* the comparison set `𝓕`;
* the cubic-regularization method `method`;
* the sublevel containment hypothesis `𝓛₀ ⊆ 𝓕`;
* the canonical smoothness owner `HessianLipschitzOn L 𝓕 problem`.

Derived API:
* the transformed objective function, used through the owner coercion `problem : E → ℝ`;
* the transported minimizer `problem.xStar`;
* the constants `problem.sigma` and `problem.D` together with the distortion/radius bounds they
  induce on the initial sublevel set;
* the one-step feasible comparison estimate along `method`, derived from the method owner and the
  chapter cubic Taylor comparison machinery.

The previous theorem surface kept that last derived estimate as a primitive hypothesis
`hcomparison`. This refinement keeps the same mathematical semantics, but moves the comparison
bound to an owner-level theorem on `CubicRegularizationMethod` and removes the duplicate public
input from the target statements. -/

namespace CubicRegularizationMethod

section NonlinearTransformation

variable {problem : NonlinearConvexTransformation E} {𝓕 : Set E}
variable {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal}
variable [HessianLipschitzOn L 𝓕 problem]

local notation "f" => problem
local notation "𝓛₀" => f ⁻¹' Set.Iic (f problem.x0)

/-- Helper for Theorem 4.1.8: one cubic-regularization step cannot increase the transformed
objective, because the current iterate is itself a feasible comparison point for the cubic
subproblem. -/
theorem objective_succ_le_objective
    (method :
      CubicRegularizationMethod
        problem
        stepMap
        L0 (L : ℝ) problem.x0)
    (k : ℕ) :
    f (method (k + 1)) ≤ f (method k) := by
  let M := method.regularization k
  have hmodel :
      EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) ≤
        cubicRegularizationQuadraticApproximation f M (method k) (method k) := by
    have hM_pos : 0 < M := method.regularization_pos k
    -- Evaluate the cubic model at the current iterate to compare the accepted value with `f x_k`.
    simpa [M] using
      (@cubicRegularizationProblem_optimalValue_toReal_le_quadraticApproximation
        E _ _ _ f M (method k) (method k) hM_pos)
  have hstep :
      f (method (k + 1)) ≤
        EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) := by
    -- Rewrite the accepted step as the next iterate.
    simpa [M, method.x_succ k] using method.objective_step_le_value k
  -- The model value at `y = x_k` is exactly `f x_k`.
  calc
    f (method (k + 1)) ≤
        EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) := hstep
    _ ≤ cubicRegularizationQuadraticApproximation f M (method k) (method k) := hmodel
    _ = f (method k) := by simp [M, cubicRegularizationQuadraticApproximation_apply]

/-- Helper for Theorem 4.1.8: every iterate stays in the initial transformed sublevel set
`𝓛₀`. -/
theorem mem_initial_sublevel
    (method :
      CubicRegularizationMethod
        problem
        stepMap
        L0 (L : ℝ) problem.x0)
    (k : ℕ) :
    method k ∈ 𝓛₀ := by
  induction k with
  | zero =>
      -- The initial iterate is exactly `x₀`.
      change f (method 0) ≤ f problem.x0
      simp [method.x_zero]
  | succ k hk =>
      -- Monotonicity propagates the initial sublevel bound along the trajectory.
      change f (method (k + 1)) ≤ f problem.x0
      exact (method.objective_succ_le_objective k).trans hk

-- Proof sketch: first derive monotonicity of the transformed objective values from the method
-- owner by comparing the cubic model at the current iterate. Hence every iterate stays in the
-- initial sublevel set `𝓛₀`, so `hlevel_subset` puts `method k` inside `𝓕`. Apply the local
-- second-order Taylor upper bound on the feasible pair `(method k, y)` and combine it with the
-- accepted-step inequality `method.objective_step_le_value k`. Finally use
-- `method.regularization k ≤ 2L` to simplify `((L + M_k) / 6)` to `L / 2`.
/-- Along a cubic-regularization method for the transformed objective, the feasible comparison
estimate from method `(4.1.16)` is derived from the method owner together with the local
Hessian-Lipschitz comparison data on `𝓕`; it is not extra primitive method data. -/
theorem objective_succ_le_feasibleComparison
    (method :
      CubicRegularizationMethod
        problem
        stepMap
        L0 (L : ℝ) problem.x0)
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (k : ℕ) {y : E} (hy : y ∈ 𝓕) :
    f (method (k + 1)) ≤
      f y + ((L : ℝ) / 2) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
  let M := method.regularization k
  have hxF : method k ∈ 𝓕 := hlevel_subset (method.mem_initial_sublevel k)
  have hcomparison :
      EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) ≤
        f y + (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    -- Compare the cubic model value with the feasible point `y`.
    simpa [M] using
      cubicRegularizationValue_le_feasibleComparison_of_mem
        (hf := inferInstance)
        (hstep := method.step_isMinOn k)
        (x := method k)
        (y := y)
        hxF
        hy
  have hstep :
      f (method (k + 1)) ≤
        f y + (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    -- Insert the owner-level feasible comparison after the accepted-step inequality.
    have haccept :
        f (method (k + 1)) ≤
          EReal.toReal
            (SetConstrainedMinimizationProblem.optimalValue
              (cubicRegularizationProblem f M (method k))) := by
      simpa [M, method.x_succ k] using method.objective_step_le_value k
    exact haccept.trans hcomparison
  have hcoef :
      (((L : ℝ) + M) / 6 : ℝ) ≤ (L : ℝ) / 2 := by
    have hM : M ≤ 2 * (L : ℝ) := by
      simpa [M] using method.regularization_le_two_mul_L k
    nlinarith
  have hpow_nonneg : 0 ≤ ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    positivity
  have hterm :
      (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) ≤
        ((L : ℝ) / 2) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    exact mul_le_mul_of_nonneg_right hcoef hpow_nonneg
  -- Replace the cubic coefficient by the larger but simpler bound `L / 2`.
  calc
    f (method (k + 1))
        ≤ f y + (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) := hstep
    _ ≤ f y + ((L : ℝ) / 2) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
      gcongr

end NonlinearTransformation

end CubicRegularizationMethod

section NonlinearTransformationCubicRate

variable (problem : NonlinearConvexTransformation E)
variable (𝓕 : Set E) {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal}
variable
  (method :
    CubicRegularizationMethod
      problem
      stepMap
      L0 (L : ℝ) problem.x0)

local notation "f" => problem
local notation "𝓛₀" => f ⁻¹' Set.Iic (f problem.x0)
local notation "Δ" => fun k : ℕ ↦ f (method k) - f problem.xStar
local notation "σD" => problem.sigma * problem.D

variable
  (hlevel_subset : 𝓛₀ ⊆ 𝓕)
  [HessianLipschitzOn L 𝓕 problem]

/-- Helper for Theorem 4.1.8: transporting the cubic comparison point through the nonlinear
change of variables yields the same one-step scalar recurrence as in Theorem 4.1.4, with `D`
replaced by `σD`. -/
lemma nonlinear_transformation_cubic_gap_succ_le_alpha_step
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (k : ℕ) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Δ k.succ ≤
      (1 - α) * Δ k + ((L : ℝ) / 2) * α ^ (3 : ℕ) * σD ^ (3 : ℕ) := by
  let uk : E := problem.u (method k)
  let zα : E := AffineMap.lineMap uk problem.uStar α
  let yα : E := problem.u.symm zα
  let S : Set E := (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)
  have hσ_nonneg : 0 ≤ problem.sigma := by
    rcases problem.sigma_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hD_nonneg : 0 ≤ problem.D := by
    rcases problem.D_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hσD_nonneg : 0 ≤ σD := mul_nonneg hσ_nonneg hD_nonneg
  have hk_sublevel : method k ∈ 𝓛₀ := method.mem_initial_sublevel k
  have hk_level :
      f (method k) ≤ f problem.x0 := hk_sublevel
  have huk : uk ∈ S := by
    -- Rewrite the sublevel statement in image coordinates.
    change problem.φ (problem.u (method k)) ≤ problem.φ (problem.u problem.x0)
    simpa [uk] using hk_level
  have huStar_level :
      problem.φ problem.uStar ≤ problem.φ (problem.u problem.x0) := by
    -- The chosen image-space minimizer lies in the same controlling level set.
    have hu_mem_univ : problem.u problem.x0 ∈ (Set.univ : Set E) := by
      simp
    exact (isMinOn_iff.mp problem.isMinOn_uStar) (problem.u problem.x0) hu_mem_univ
  have hzα_level :
      problem.φ zα ≤ problem.φ (problem.u problem.x0) := by
    have hkφ_level : problem.φ uk ≤ problem.φ (problem.u problem.x0) := by
      simpa [uk] using hk_level
    have hconv :
        problem.φ zα ≤
          (1 - α) * problem.φ uk + α * problem.φ problem.uStar := by
      -- Convexity controls the potential along the image-space segment from `u x_k` to `u*`.
      simpa [uk, zα, AffineMap.lineMap_apply_module, mul_comm, mul_left_comm, mul_assoc] using
        problem.φ_convex.2
          (by simp)
          (by simp)
          (sub_nonneg.mpr hα.2)
          hα.1
          (by ring)
    nlinarith [hconv, hkφ_level, huStar_level, hα.1, hα.2]
  have hyα_sublevel : yα ∈ 𝓛₀ := by
    -- Pull the image-space segment point back through `u⁻¹`.
    change problem (yα) ≤ problem problem.x0
    simpa [yα, zα] using hzα_level
  have hyαF : yα ∈ 𝓕 := hlevel_subset hyα_sublevel
  have hcomparison :
      f (method (k + 1)) ≤
        f yα + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) := by
    -- Route correction: use the owner-level feasible comparison from this file, not an ad hoc
    -- public comparison hypothesis.
    simpa [yα] using
      method.objective_succ_le_feasibleComparison hlevel_subset k hyαF
  have hobjective :
      f yα - f problem.xStar ≤ (1 - α) * Δ k := by
    have hconv :
        problem.φ zα ≤
          (1 - α) * problem.φ uk + α * problem.φ problem.uStar := by
      -- The transformed objective at `yα` is bounded by the convex combination of the endpoint
      -- potentials on the image segment.
      simpa [uk, zα, AffineMap.lineMap_apply_module, mul_comm, mul_left_comm, mul_assoc] using
        problem.φ_convex.2
          (by simp)
          (by simp)
          (sub_nonneg.mpr hα.2)
          hα.1
          (by ring)
    have hyα_eq : f yα = problem.φ zα := by
      simp [yα, zα]
    have hxStar_eq : f problem.xStar = problem.φ problem.uStar := by
      simp [NonlinearConvexTransformation.xStar]
    have hk_eq : f (method k) = problem.φ uk := by
      simp [uk]
    calc
      f yα - f problem.xStar = problem.φ zα - problem.φ problem.uStar := by
        rw [hyα_eq, hxStar_eq]
      _ ≤ (1 - α) * (problem.φ uk - problem.φ problem.uStar) := by
        nlinarith [hconv]
      _ = (1 - α) * (f (method k) - f problem.xStar) := by
        rw [hk_eq, hxStar_eq]
      _ = (1 - α) * Δ k := by
        rfl
  have hs : Convex ℝ S := by
    change Convex ℝ (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)
    simpa [Function.comp, Set.preimage, Set.mem_Iic, Set.sep_univ] using
      problem.φ_convex.convex_le (problem.φ (problem.u problem.x0))
  have hdist :
      ‖(yα - method k : E)‖ ≤ problem.sigma * ‖(zα - uk : E)‖ := by
    -- Apply the mean-value estimate to `u⁻¹` along the image-space segment.
    simpa [uk, yα] using
      hs.norm_image_sub_le_of_norm_fderiv_le
        (fun z hz ↦ problem.u_symm_differentiableAt_controllingLevelSet hz)
        (fun z hz ↦ problem.norm_fderiv_u_symm_le_sigma hz)
        huk
        (by
          change zα ∈ S
          exact hzα_level)
  have hzα_eq :
      zα = α • (problem.uStar - uk) + uk := by
    -- `lineMap` exposes the image displacement from `u x_k` toward `u*`.
    simpa [uk, zα] using AffineMap.lineMap_apply uk problem.uStar α
  have hzα_norm_eq :
      ‖(zα - uk : E)‖ = α * ‖(problem.uStar - uk : E)‖ := by
    rw [hzα_eq]
    simp [norm_smul_of_nonneg, hα.1]
  have huk_radius :
      ‖(problem.uStar - uk : E)‖ ≤ problem.D := by
    -- The current image iterate belongs to the controlling level set, so its distance to `u*`
    -- is bounded by `D`.
    simpa [uk, norm_sub_rev] using problem.norm_sub_uStar_le_D huk
  have hzα_norm_le :
      ‖(zα - uk : E)‖ ≤ α * problem.D := by
    rw [hzα_norm_eq]
    exact mul_le_mul_of_nonneg_left huk_radius hα.1
  have hnorm_le :
      ‖(yα - method k : E)‖ ≤ α * σD := by
    calc
      ‖(yα - method k : E)‖ ≤ problem.sigma * ‖(zα - uk : E)‖ := hdist
      _ ≤ problem.sigma * (α * problem.D) := by
        exact mul_le_mul_of_nonneg_left hzα_norm_le hσ_nonneg
      _ = α * σD := by ring
  have hcube :
      ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
        ((L : ℝ) / 2) * α ^ (3 : ℕ) * σD ^ (3 : ℕ) := by
    -- Cubing the distance bound gives the transported cubic penalty.
    have hpow :
        ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤ (α * σD) ^ (3 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm_le 3
    have hcoef_nonneg : 0 ≤ (L : ℝ) / 2 := by
      positivity
    have hscaled : ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
        ((L : ℝ) / 2) * (α * σD) ^ (3 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow hcoef_nonneg
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hstep_gap :
      Δ (k + 1) ≤
        (f yα - f problem.xStar) + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) := by
    -- Subtract the optimal value from the one-step feasible comparison estimate.
    have hsub := sub_le_sub_right hcomparison (f problem.xStar)
    change
      f (method (k + 1)) - f problem.xStar ≤
        (f yα - f problem.xStar) + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  -- Combine the convexity term and the transported cubic penalty into the scalar recurrence.
  nlinarith [hstep_gap, hobjective, hcube]

-- Proof sketch: use
-- `method.objective_succ_le_feasibleComparison hlevel_subset`
-- for the accepted cubic step, then combine it with the convexity of `φ` along the segment
-- joining `u (method 0)` to `uStar`. Use the distortion bound and the radius bound already
-- encoded by `problem.sigma` and `problem.D` to obtain the same scalar recursion as in
-- Theorem 4.1.4 with `D` replaced by `σ * D`, and then specialize that recursion at `k = 0`.
/-- Theorem 4.1.8 (1): for a nonlinear transformation of a convex objective, if the Hessian of
`problem = problem.φ ∘ problem.u` satisfies the canonical owner
`HessianLipschitzOn L 𝓕 problem` on a comparison set `𝓕` containing the sublevel set
`f ⁻¹' Set.Iic (f x₀)`, and the iterates are generated by the chapter
cubic-regularization method owner, then an initial gap of at least `(3 / 2) L (σ D)^3` implies
that the first-step gap is at most `(1 / 2) L (σ D)^3`. -/
theorem nonlinearTransformation_cubicRegularization_first_gap_le_half_sigmaD_cube
    (hgap0 : Δ 0 ≥ (3 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ)) :
    Δ 1 ≤ (1 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ) := by
  -- TODO: the public theorem needs the comparison-set assumption `hlevel_subset` in its local
  -- context so that the proven `nonlinear_transformation_cubic_gap_succ_le_alpha_step` helper can
  -- be specialized at `k = 0`, `α = 1`.
  sorry

-- Proof sketch: use the same derived one-step comparison estimate as in part (1) to obtain, for
-- every `k`, the scalar recurrence from Theorem 4.1.4 with `D` replaced by
-- `problem.sigma * problem.D`. Under the small-gap hypothesis at `k = 0`, solve that recurrence
-- to obtain the inverse-square upper bound for all later iterates.
/-- Theorem 4.1.8 (2): under the same nonlinear-transformation and cubic-regularization
hypotheses, if the initial gap is at most `(3 / 2) L (σ D)^3`, then every iterate satisfies the
inverse-square decay bound
`f(x_k) - f* ≤ 3 L (σ D)^3 / (2 (1 + k / 3)^2)`. -/
theorem nonlinearTransformation_cubicRegularization_gap_le_inverse_square_rate
    (hgap0 : Δ 0 ≤ (3 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ)) :
    ∀ k : ℕ,
      Δ k ≤
        (3 * (L : ℝ) * σD ^ (3 : ℕ)) /
          (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) := by
  -- TODO: the public theorem needs the comparison-set assumption `hlevel_subset` in its local
  -- context so that the proven transported scalar recurrence can be iterated exactly as in
  -- Theorem 4.1.4.
  sorry

end NonlinearTransformationCubicRate
