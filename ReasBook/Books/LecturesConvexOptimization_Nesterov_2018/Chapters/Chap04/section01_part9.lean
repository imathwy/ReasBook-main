import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_1_8 (from Chap04) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {X : Type u}

/- Definition 4.1.8 lies in the constrained global-minimization / quadratic error-bound domain on
feasible subsets of a pseudo-metric ambient space. The textbook statement on `ℝⁿ` is the
specialization to `X = EuclideanSpace ℝ (Fin n)`.

Sampled owner-style declarations:
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner for minimizer sets of an ambient objective on an explicit feasible set;
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the Chapter 1 owner for the
  primitive constrained-optimization data `(F, f)`;
* `StarConvexFunction` in `Chap04/Definition_4_1_7`, which keeps source-facing optimization data
  while exposing minimizers through `argmin[Set.univ] f`;
* `GradientDominatedOn` in `Chap04/Definition_4_1_9`, which is likewise organized around an
  ambient objective `f : X → ℝ` on an explicit feasible set `F`.

Best owner abstraction:
* the ambient constrained data `F : Set X` and `f : X → ℝ`;
* the canonical optimal set `argmin[F] f`;
* the canonical distance-to-optimal-set term `Metric.infDist x (argmin[F] f)`;
* the source-facing error-bound property `HasGloballyNondegenerateOptimalSet F f`.

Primitive data:
* a pseudo-metric ambient type `X`;
* a feasible set `F : Set X`;
* a real-valued ambient objective `f : X → ℝ`;
* nonemptiness of `argmin[F] f`;
* the quadratic error bound relative to `argmin[F] f`.

Derived API:
* pointwise membership in `argmin[F] f` via `mem_constrainedArgmin_iff`;
* distance-to-optimal-set expressions via `Metric.infDist`.
* the witness package `HasGloballyNondegenerateOptimalSet.UsesConstant F f xStar μ`;
* transport of an owner-level error-bound constant to any canonical minimizer in `argmin[F] f`.

Source/core/bridge triage:
* source-facing: `HasGloballyNondegenerateOptimalSet`;
* core/canonical: `argmin[F] f`, `IsMinOn f F x`, and `Metric.infDist`;
* bridge/view: `HasGloballyNondegenerateOptimalSet.UsesConstant`,
  `HasGloballyNondegenerateOptimalSet.exists_usesConstant_of_mem_argmin`, and the standard
  simplification route `mem_constrainedArgmin_iff`.

This refinement keeps the source-facing nondegeneracy property, but moves it onto the ambient
constrained owner layer used elsewhere in the project instead of packaging the objective on the
feasible subtype.
-/

namespace HasGloballyNondegenerateOptimalSet

/-- `UsesConstant F f xStar μ` packages the canonical `argmin` membership of `xStar` together with
the positive error-bound constant `μ` used in the source-facing quadratic growth inequality. -/
def UsesConstant [PseudoMetricSpace X] (F : Set X) (f : X → ℝ) (xStar : X) (μ : ℝ) : Prop :=
  xStar ∈ argmin[F] f ∧ 0 < μ ∧
    ∀ ⦃x : X⦄, x ∈ F →
      f x - f xStar ≥
        (μ / 2) * (Metric.infDist x (argmin[F] f)) ^ (2 : ℕ)

end HasGloballyNondegenerateOptimalSet

/-- Definition 4.1.8: a real-valued function `f` on a feasible set `F ⊆ X` has a globally
non-degenerate optimal set if `argmin[F] f` is nonempty and there exists a constant `μ > 0` such
that, for every feasible point `x ∈ F`, the objective gap above the constrained optimal value
`sInf (f '' F)` is bounded below by `(μ / 2)` times the squared distance from `x` to
`argmin[F] f`. The textbook `ℝⁿ` version is the specialization to
`X = EuclideanSpace ℝ (Fin n)`. -/
class HasGloballyNondegenerateOptimalSet [PseudoMetricSpace X] (F : Set X) (f : X → ℝ) : Prop where
  /-- The optimal set `argmin[F] f` is nonempty. -/
  optimalSet_nonempty : (argmin[F] f).Nonempty
  /-- The objective gap dominates the squared distance to the optimal set with a positive
  error-bound constant. -/
  exists_error_bound :
    ∃ μ : ℝ, 0 < μ ∧ ∀ ⦃x : X⦄, x ∈ F →
      f x - sInf (f '' F) ≥
        (μ / 2) * (Metric.infDist x (argmin[F] f)) ^ (2 : ℕ)

namespace HasGloballyNondegenerateOptimalSet

variable [PseudoMetricSpace X] {F : Set X} {f : X → ℝ}

theorem UsesConstant.mem_argmin
    {xStar : X} {μ : ℝ}
    (hμ : UsesConstant F f xStar μ) :
    xStar ∈ argmin[F] f :=
  hμ.1

theorem UsesConstant.pos
    {xStar : X} {μ : ℝ}
    (hμ : UsesConstant F f xStar μ) :
    0 < μ :=
  hμ.2.1

theorem UsesConstant.bound
    {xStar : X} {μ : ℝ}
    (hμ : UsesConstant F f xStar μ) {x : X} (hx : x ∈ F) :
    f x - f xStar ≥
      (μ / 2) * (Metric.infDist x (argmin[F] f)) ^ (2 : ℕ) :=
  hμ.2.2 hx

/-- Any point of the canonical minimizer set can be paired with some positive quadratic
error-bound constant. -/
theorem exists_usesConstant_of_mem_argmin
    (hf : HasGloballyNondegenerateOptimalSet F f) {xStar : X} (hxStar : xStar ∈ argmin[F] f) :
    ∃ μ, UsesConstant F f xStar μ := by
  rcases hf.exists_error_bound with ⟨μ, hμ, hbound⟩
  have hxStar_mem : xStar ∈ argmin[F] f := hxStar
  rw [mem_constrainedArgmin_iff] at hxStar
  have hxStar_glb : IsGLB (f '' F) (f xStar) := by
    simpa using hxStar.2.isGLB hxStar.1
  have hxStar_val : sInf (f '' F) = f xStar := by
    exact hxStar_glb.csInf_eq ⟨f xStar, ⟨xStar, hxStar.1, rfl⟩⟩
  refine ⟨μ, hxStar_mem, hμ, ?_⟩
  intro x hx
  simpa [hxStar_val] using hbound hx

end HasGloballyNondegenerateOptimalSet

/-- A constant objective on a nonempty feasible set has a globally non-degenerate optimal set. -/
theorem hasGloballyNondegenerateOptimalSet_const [PseudoMetricSpace X]
    {F : Set X} (hF : F.Nonempty) (c : ℝ) :
    HasGloballyNondegenerateOptimalSet F (fun _ : X ↦ c) := by
  have hargmin : argmin[F] (fun _ : X ↦ c) = F := by
    ext x
    rw [mem_constrainedArgmin_iff]
    simp [isMinOn_iff]
  have himage : (fun _ : X ↦ c) '' F = ({c} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp
    · intro hy
      rcases hF with ⟨x, hx⟩
      refine ⟨x, hx, ?_⟩
      simpa [Set.mem_singleton_iff] using hy.symm
  have hsInf : sInf ((fun _ : X ↦ c) '' F) = c := by
    rw [himage]
    simp
  refine ⟨?_, ?_⟩
  · rcases hF with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hargmin]
    exact hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    rw [hsInf, sub_self, hargmin, Metric.infDist_zero_of_mem hx]
    norm_num

end

/-! ### Lemma_4_1_8 (from Chap04) -/
open scoped CubicRegularizationResidual Gradient

noncomputable section

universe u

/- Lemma 4.1.8 lies in the chapter cubic-regularization / gradient-`3/2` descent domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the iterate and
  regularization sequences;
* `cubicRegularizationResidual` in `Lemma_4_1_5`, with notation `r[trialPoint] x`;
* `objective_sub_cubicRegularizationValue_ge_residual_cube` in `Lemma_4_1_5`, the owner-level
  descent estimate for a minimizing cubic trial point;
* `CubicRegularizationMethod.L0_le_regularization` and
  `CubicRegularizationMethod.regularization_le_two_mul_L` in `Algorithm_4_1_5`, the canonical
  bounds `L₀ ≤ M_k ≤ 2L`.

Source/core/bridge triage:
* source-facing: the textbook gradient-`3/2` lower bound for one cubic-regularization step;
* core/canonical: `CubicRegularizationMethod`, `cubicRegularizationValue`, and the residual owner
  `r[trialPoint]`;
* bridge/view: transport the owner-level residual-cube decrease estimate to the trajectory and
  combine it with the residual lower bound in terms of `‖∇ f(x_{k+1})‖`.

Primitive data:
* a cubic-regularization method `method`, whose owner data already supplies the minimizing cubic
  trial point at each step;
* a chosen step index `k`;
* the residual lower bound at the accepted step `k`.

Derived API:
* the objective-drop lower bound by `‖∇ f(x_{k+1})‖^(3/2)`.

The previous file duplicated the chapter owner data by taking separate sequences `x`, `M`, and an
arbitrary residual function together with standalone bounds `L₀ ≤ M_k ≤ 2L`. This refinement
reuses the canonical method owner and the canonical residual owner directly, and treats the
residual-cube objective drop as derived API rather than primitive input. -/

section CubicRegularizationGradientThreeHalvesDrop

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 L : ℝ} {x0 : E}

namespace CubicRegularizationMethod

/-- Helper for Lemma 4.1.8: the accepted trial point inherits the residual-cube objective drop
from the cubic-model minimizing inequality. -/
lemma objective_sub_acceptedTrialPoint_ge_regularization_mul_residual_cube
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 L x0)
    (k : ℕ) :
    f (method k) - f (method.acceptedTrialPoint k) ≥
      ((method.regularization k) / 12 : ℝ) * r[method.acceptedTrialPoint k] (method k) ^ (3 : ℕ) := by
  let modelValue :=
    EReal.toReal
      (SetConstrainedMinimizationProblem.optimalValue
        (cubicRegularizationProblem f (method.regularization k) (method k)))
  -- First rewrite the owner-level cubic decrease estimate at the accepted trial point.
  have hmodel :
      f (method k) - modelValue ≥
        ((method.regularization k) / 12 : ℝ) * r[method.acceptedTrialPoint k] (method k) ^ (3 : ℕ) := by
    simpa [CubicRegularizationMethod.acceptedTrialPoint, modelValue] using
      objective_sub_cubicRegularizationValue_ge_residual_cube
        (f := f)
        (M := method.regularization k)
        (x := method k)
        (trialPoint := method.acceptedTrialPoint k)
        (method.regularization_pos k).le
        (by
          simpa [CubicRegularizationMethod.acceptedTrialPoint] using method.step_isMinOn k)
  -- Then replace the model value by the actual accepted objective value.
  have haccept : f (method.acceptedTrialPoint k) ≤ modelValue := by
    simpa [CubicRegularizationMethod.acceptedTrialPoint, modelValue] using method.objective_step_le_value k
  have hdrop :
      f (method k) - modelValue ≤ f (method k) - f (method.acceptedTrialPoint k) := by
    simpa [modelValue] using sub_le_sub_left haccept (f (method k))
  exact le_trans hmodel hdrop

/-- Helper for Lemma 4.1.8: cubing the residual square-root lower bound produces the canonical
`‖∇ f‖^(3/2)` factor. -/
lemma sqrt_drop_factor_eq_gradient_norm_rpow_threeHalves
    {M g L : ℝ}
    (hg : 0 ≤ g)
    (hLM : 0 < L + M) :
    ((M / 12 : ℝ) * (Real.sqrt (2 * g / (L + M))) ^ (3 : ℕ)) =
      (M / (3 * Real.sqrt 2 * Real.rpow (L + M) (3 / 2 : ℝ)) : ℝ) *
        Real.rpow g (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  have hdiv_nonneg : 0 ≤ 2 * g / (L + M) := by
    exact div_nonneg (by nlinarith) hLM.le
  -- Collapse the cubic power of the square root into a single `3 / 2` exponent.
  rw [show ((2 * g / (L + M)) ^ (1 / 2 : ℝ)) ^ (3 : ℕ) = (2 * g / (L + M)) ^ (3 / 2 : ℝ) by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdiv_nonneg]
    norm_num]
  rw [Real.div_rpow (by nlinarith) hLM.le, Real.mul_rpow (by norm_num) hg]
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
    rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ)), Real.sqrt_eq_rpow]
    norm_num [Real.rpow_natCast]
  rw [htwo]
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hrpow_ne : Real.rpow (L + M) (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hLM _)
  -- Clearing the positive denominators leaves a purely scalar identity.
  field_simp [hsqrt2_ne, hrpow_ne]
  rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  ring_nf
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 4.1.8: on the admissible interval `L₀ ≤ M ≤ 2L`, the scalar coefficient
`M / (L + M)^(3/2)` is bounded below by its value at `L₀`. -/
lemma regularization_ratio_lower_bound
    {M L0 L : ℝ}
    (hL0 : 0 < L0)
    (hL0M : L0 ≤ M)
    (hM : M ≤ 2 * L) :
    L0 / Real.rpow (L + L0) (3 / 2 : ℝ) ≤ M / Real.rpow (L + M) (3 / 2 : ℝ) := by
  have hL_pos : 0 < L := by
    linarith
  have hLM0_pos : 0 < L + L0 := by
    linarith
  have hLM_pos : 0 < L + M := by
    linarith
  have hleft_nonneg : 0 ≤ L0 / Real.rpow (L + L0) (3 / 2 : ℝ) := by
    exact div_nonneg hL0.le (Real.rpow_nonneg hLM0_pos.le _)
  have hright_nonneg : 0 ≤ M / Real.rpow (L + M) (3 / 2 : ℝ) := by
    have hM_nonneg : 0 ≤ M := le_trans hL0.le hL0M
    exact div_nonneg hM_nonneg (Real.rpow_nonneg hLM_pos.le _)
  apply (sq_le_sq₀ hleft_nonneg hright_nonneg).1
  have hpoly : L0 ^ (2 : ℕ) * (L + M) ^ (3 : ℕ) ≤ M ^ (2 : ℕ) * (L + L0) ^ (3 : ℕ) := by
    have h_ab_le_Lsum : L0 * M ≤ L * (L0 + M) := by
      have h1 : L0 * M ≤ 2 * L * L0 := by
        nlinarith
      have h2 : 2 * L * L0 ≤ L * (L0 + M) := by
        have : 2 * L0 ≤ L0 + M := by
          linarith
        nlinarith [hL_pos]
      exact h1.trans h2
    have h_ab_le_fourL2 : L0 * M ≤ 4 * L ^ (2 : ℕ) := by
      have h1 : L0 * M ≤ M ^ (2 : ℕ) := by
        nlinarith
      have h2 : M ^ (2 : ℕ) ≤ 4 * L ^ (2 : ℕ) := by
        nlinarith
      exact h1.trans h2
    have hfactor_nonneg :
        0 ≤ L ^ (3 : ℕ) * (L0 + M) + 3 * L ^ (2 : ℕ) * L0 * M - L0 ^ (2 : ℕ) * M ^ (2 : ℕ) := by
      have hterm1 : 0 ≤ L ^ (2 : ℕ) * (L * (L0 + M) - L0 * M) := by
        exact mul_nonneg (sq_nonneg L) (sub_nonneg.mpr h_ab_le_Lsum)
      have hterm2 : 0 ≤ L0 * M * (4 * L ^ (2 : ℕ) - L0 * M) := by
        have hLM_nonneg : 0 ≤ L0 * M := mul_nonneg hL0.le (le_trans hL0.le hL0M)
        exact mul_nonneg hLM_nonneg (sub_nonneg.mpr h_ab_le_fourL2)
      have hEq :
          L ^ (3 : ℕ) * (L0 + M) + 3 * L ^ (2 : ℕ) * L0 * M - L0 ^ (2 : ℕ) * M ^ (2 : ℕ) =
            L ^ (2 : ℕ) * (L * (L0 + M) - L0 * M) + L0 * M * (4 * L ^ (2 : ℕ) - L0 * M) := by
        ring
      rw [hEq]
      exact add_nonneg hterm1 hterm2
    -- After squaring, the coefficient difference factors by `M - L₀`.
    have hdiff : 0 ≤ M ^ (2 : ℕ) * (L + L0) ^ (3 : ℕ) - L0 ^ (2 : ℕ) * (L + M) ^ (3 : ℕ) := by
      have hba : 0 ≤ M - L0 := by
        linarith
      have hEq :
          M ^ (2 : ℕ) * (L + L0) ^ (3 : ℕ) - L0 ^ (2 : ℕ) * (L + M) ^ (3 : ℕ) =
            (M - L0) *
              (L ^ (3 : ℕ) * (L0 + M) + 3 * L ^ (2 : ℕ) * L0 * M - L0 ^ (2 : ℕ) * M ^ (2 : ℕ)) := by
        ring
      rw [hEq]
      exact mul_nonneg hba hfactor_nonneg
    linarith
  have hleft_sq :
      (L0 / Real.rpow (L + L0) (3 / 2 : ℝ)) ^ (2 : ℕ) =
        L0 ^ (2 : ℕ) / (L + L0) ^ (3 : ℕ) := by
    rw [div_pow]
    have hsq : (Real.rpow (L + L0) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + L0) ^ (3 : ℕ) := by
      calc
        (Real.rpow (L + L0) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + L0) ^ ((3 / 2 : ℝ) * 2) := by
          symm
          exact Real.rpow_mul_natCast hLM0_pos.le (3 / 2 : ℝ) 2
        _ = (L + L0) ^ (3 : ℕ) := by
          norm_num [Real.rpow_natCast]
    rw [hsq]
  have hright_sq :
      (M / Real.rpow (L + M) (3 / 2 : ℝ)) ^ (2 : ℕ) =
        M ^ (2 : ℕ) / (L + M) ^ (3 : ℕ) := by
    rw [div_pow]
    have hsq : (Real.rpow (L + M) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + M) ^ (3 : ℕ) := by
      calc
        (Real.rpow (L + M) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + M) ^ ((3 / 2 : ℝ) * 2) := by
          symm
          exact Real.rpow_mul_natCast hLM_pos.le (3 / 2 : ℝ) 2
        _ = (L + M) ^ (3 : ℕ) := by
          norm_num [Real.rpow_natCast]
    rw [hsq]
  rw [hleft_sq, hright_sq]
  exact
    (div_le_div_iff₀
      (show 0 < (L + L0) ^ (3 : ℕ) by positivity)
      (show 0 < (L + M) ^ (3 : ℕ) by positivity)).2 hpoly

-- Proof sketch: first combine the method acceptance inequality with
-- `objective_sub_cubicRegularizationValue_ge_residual_cube` to obtain
-- `f(x_k) - f(x_{k+1}) ≥ (M_k / 12) r_{M_k}(x_k)^3`. Then use the residual lower bound
-- `r_{M_k}(x_k) ≥ sqrt (2 ‖∇ f(x_{k+1})‖ / (L + M_k))` to rewrite the right-hand side as
-- `(M_k / (3 * sqrt 2 * (L + M_k)^(3/2))) * ‖∇ f(x_{k+1})‖^(3/2)`, and finally use the owner
-- bounds `L₀ ≤ M_k ≤ 2L` to replace that coefficient by its lower bound at `L₀`.
/-- Lemma 4.1.8: if a cubic-regularization method uses at step `k` a global minimizer of the
cubic model, and if the residual at that step satisfies
`r_{M_k}(x_k) ≥ sqrt (2 ‖∇ f(x_{k+1})‖ / (L + M_k))`, then the one-step objective drop obeys
the gradient-`3/2` lower bound
`f(x_k) - f(x_{k+1}) ≥ [L0 / (3 sqrt 2 (L + L0)^(3/2))] ‖∇ f(x_{k+1})‖^(3/2)`. -/
theorem objective_sub_succ_ge_gradient_norm_rpow_threeHalves
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 L x0)
    (k : ℕ)
    (hresidual_lower :
      r[method.acceptedTrialPoint k] (method k) ≥
        Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) :
    f (method k) - f (method (k + 1)) ≥
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ) *
        Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
  have hdrop :=
    objective_sub_acceptedTrialPoint_ge_regularization_mul_residual_cube method k
  have hreg_nonneg : 0 ≤ (method.regularization k / 12 : ℝ) := by
    linarith [method.regularization_pos k]
  have hsqrt_nonneg :
      0 ≤
        Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)) :=
    Real.sqrt_nonneg _
  have hresidual_cube :
      (Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) ^ (3 : ℕ) ≤
        r[method.acceptedTrialPoint k] (method k) ^ (3 : ℕ) := by
    -- Cube the residual lower bound on the nonnegative square-root branch.
    exact pow_le_pow_left₀ hsqrt_nonneg hresidual_lower 3
  have hsqrt_drop :
      ((method.regularization k / 12 : ℝ) *
          (Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) ^ (3 : ℕ)) ≤
        f (method k) - f (method.acceptedTrialPoint k) := by
    -- Scale the cubed residual estimate by the nonnegative regularization coefficient.
    have hscaled :=
      mul_le_mul_of_nonneg_left hresidual_cube hreg_nonneg
    exact le_trans hscaled hdrop
  have hLM_pos : 0 < L + method.regularization k := by
    linarith [method.L0_pos, method.L0_le_L, method.regularization_pos k]
  have hsqrt_rewrite :
      ((method.regularization k / 12 : ℝ) *
          (Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) ^ (3 : ℕ)) =
        ((method.regularization k /
              (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) :=
    sqrt_drop_factor_eq_gradient_norm_rpow_threeHalves
      (g := ‖∇ f (method.acceptedTrialPoint k)‖)
      (M := method.regularization k)
      (L := L)
      (norm_nonneg _)
      hLM_pos
  have hgradient_drop :
      ((method.regularization k /
            (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) ≤
        f (method k) - f (method.acceptedTrialPoint k) := by
    rw [hsqrt_rewrite] at hsqrt_drop
    exact hsqrt_drop
  have hratio :
      L0 / Real.rpow (L + L0) (3 / 2 : ℝ) ≤
        method.regularization k / Real.rpow (L + method.regularization k) (3 / 2 : ℝ) :=
    regularization_ratio_lower_bound
      method.L0_pos
      (method.L0_le_regularization k)
      (method.regularization_le_two_mul_L k)
  have hscale_ratio :
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ) ≤
        (method.regularization k /
            (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) := by
    -- The scalar coefficient is minimized by replacing `M_k` with the lower endpoint `L₀`.
    have hscale :=
      mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 1 / (3 * Real.sqrt 2))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscale
  have hgrad_nonneg :
      0 ≤ Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hfinal_coeff :
      ((L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) ≤
        ((method.regularization k /
              (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hscale_ratio hgrad_nonneg
  -- Chaining the scalar lower bound with the owner-level descent estimate gives the target step.
  have hfinal :=
    le_trans hfinal_coeff hgradient_drop
  simpa [method.acceptedTrialPoint_eq_succ k] using hfinal

end CubicRegularizationMethod

end CubicRegularizationGradientThreeHalvesDrop

end

/-! ### Proposition_4_1_8 (from Chap04) -/
noncomputable section

open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The quadratic objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫` on `ℝⁿ`. -/
def quadraticObjective (α : ℝ) (a : E) (A : Matrix (Fin n) (Fin n) ℝ) : E → ℝ :=
  fun x ↦ α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x

/-- The scalar epigraph Lagrangian `𝓛(h, τ, λ)` for the cubic-regularized quadratic model. -/
def cubicRegularizedQuadraticScalarLagrangian
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) : ℝ :=
  dotProduct g h +
    (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) +
        lam * ((1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ)

/-- The scalar dual function `ψ(λ)` obtained by infimizing the epigraph Lagrangian over
`(h, τ) ∈ ℝⁿ × ℝ`. -/
def cubicRegularizedQuadraticDualFunction
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (lam : ℝ) : EReal :=
  sInf (Set.range fun z : E × ℝ ↦
    (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal))

/-- Expanding `cubicRegularizedQuadraticDualFunction g H M lam` gives the infimum definition of
`ψ(λ)`. -/
theorem cubicRegularizedQuadraticDualFunction_eq_sInf
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g H M lam =
      sInf (Set.range fun z : E × ℝ ↦
        (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal)) :=
  rfl

/-- The effective domain `dom ψ = {λ | ψ(λ) > -∞}` of the scalar dual function. -/
def cubicRegularizedQuadraticDualDomain
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : Set ℝ :=
  { lam | ⊥ < cubicRegularizedQuadraticDualFunction g H M lam }

/-- The explicit slack-variable minimizer `τ(λ) = 4 λ |λ| / M²`. -/
def cubicRegularizedQuadraticTauMinimizer
    (M lam : ℝ) : ℝ :=
  (4 : ℝ) * lam * |lam| / M ^ (2 : ℕ)

/-- Helper for Proposition 4.1.8: the zero-offset quadratic owner agrees with the displayed
coordinate formula `⟪g, h⟫ + (1 / 2) ⟪Ah, h⟫`. -/
lemma quadraticObjective_zero_eq_dotProduct
    (g : E) (A : Matrix (Fin n) (Fin n) ℝ) (h : E) :
    quadraticObjective 0 g A h =
      dotProduct g h + (1 / 2 : ℝ) * dotProduct (A.mulVec h) h := by
  -- Convert the abstract inner products in `quadraticObjective` to the coordinate `dotProduct`
  -- form used by the scalar Lagrangian.
  rw [quadraticObjective]
  have hg : inner ℝ g h = dotProduct g h := by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct g h)
  have hA : inner ℝ (A.toEuclideanLin h) h = dotProduct (A.mulVec h) h := by
    simpa [Matrix.toLpLin_apply, dotProduct_comm] using
      (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin h) h)
  rw [hg, hA]
  ring

/-- Helper for Proposition 4.1.8: the scalar Lagrangian splits into the shifted quadratic
`q_λ(h)` plus the pure slack-variable objective. -/
lemma cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g H M h τ lam =
      quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
        ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) := by
  -- Separate the `h`-dependent quadratic part from the scalar `τ`-objective.
  rw [cubicRegularizedQuadraticScalarLagrangian, quadraticObjective_zero_eq_dotProduct]
  have hnorm : dotProduct h h = ‖h‖ ^ (2 : ℕ) := by
    -- The identity-matrix contribution is exactly the Euclidean norm square.
    have hdot := (EuclideanSpace.inner_eq_star_dotProduct h h).symm
    simp at hdot
    exact hdot.trans (real_inner_self_eq_norm_sq h)
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, hnorm, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg, mul_add]
  ring

/-- Helper for Proposition 4.1.8: the slack objective is bounded below by the explicit cubic
penalty `-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_ge_minValue
    (M : ℝ) (lam : ℝ) (hM : 0 < M) (τ : ℝ) :
    -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
  -- First dominate the linear term by replacing `lam * τ` with `|lam| * |τ|`.
  have hlin : -(|lam| / 2 : ℝ) * |τ| ≤ -(lam / 2 : ℝ) * τ := by
    have hmul : lam * τ ≤ |lam| * |τ| := by
      calc
        lam * τ ≤ |lam * τ| := le_abs_self _
        _ = |lam| * |τ| := by rw [abs_mul]
    nlinarith
  let s : ℝ := Real.sqrt |τ|
  have hpow : |τ| ^ (3 / 2 : ℝ) = s ^ (3 : ℕ) := by
    -- Rewrite the `3 / 2` power as a cubic in `sqrt |τ|`.
    calc
      |τ| ^ (3 / 2 : ℝ) = (|τ| ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num, Real.rpow_mul (abs_nonneg τ)]
      _ = s ^ (3 : ℕ) := by
        simp [s, Real.sqrt_eq_rpow]
  have hs_sq : s ^ (2 : ℕ) = |τ| := by
    -- `s = sqrt |τ|` was chosen precisely so that its square recovers `|τ|`.
    dsimp [s]
    exact Real.sq_sqrt (abs_nonneg τ)
  have hpoly :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) := by
    -- The remaining inequality is the nonnegativity of a factored cubic polynomial.
    have hnonneg : 0 ≤ (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) := by
      positivity
    have hidentity :
        (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) =
          (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) +
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      field_simp [hM.ne']
      ring
    nlinarith
  have hpoly' :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (|lam| / 2 : ℝ) * |τ| := by
    rw [hpow, ← hs_sq]
    exact hpoly
  nlinarith

/-- Helper for Proposition 4.1.8: the explicit slack minimizer attains the lower-bound value
`-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer
    (M : ℝ) (lam : ℝ) (hM : 0 < M) :
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) := by
  have habs :
      |cubicRegularizedQuadraticTauMinimizer M lam| = ((2 : ℝ) * |lam| / M) ^ (2 : ℕ) := by
    -- The minimizer has squared magnitude `(2 |λ| / M)²`.
    rw [cubicRegularizedQuadraticTauMinimizer, abs_div, abs_mul, abs_mul,
      abs_of_nonneg (by positivity), abs_abs, abs_of_pos (pow_pos hM 2)]
    field_simp [hM.ne']
    ring_nf
  have hpow :
      |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) =
        ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by
    -- Raising that squared magnitude to `3 / 2` gives the expected cubic term.
    rw [habs]
    calc
      (((2 : ℝ) * |lam| / M) ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
          (((2 : ℝ) * |lam| / M) ^ (1 : ℕ) : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (2 : ℝ) * |lam| / M) 2 (3 / 2 : ℝ)]
        norm_num
      _ = ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by ring
  have hlamtau :
      lam * cubicRegularizedQuadraticTauMinimizer M lam =
        |lam| * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    -- The minimizer has the same sign as `lam`, so the linear term also depends only on `|lam|`.
    rw [cubicRegularizedQuadraticTauMinimizer]
    field_simp [hM.ne']
    ring_nf
    rw [← sq_abs lam]
    ring
  have hlinterm :
      (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        (|lam| / 2 : ℝ) * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    nlinarith [hlamtau]
  rw [hpow, hlinterm]
  field_simp [hM.ne']
  ring

-- Proof sketch: minimize the scalar function
-- `τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` directly; the critical point is the explicit owner
-- `cubicRegularizedQuadraticTauMinimizer M lam`, and convexity yields global minimality.
/-- For `M > 0`, the scalar function
`τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` is minimized at
`cubicRegularizedQuadraticTauMinimizer M lam`. -/
theorem cubicRegularizedQuadraticTauMinimizer_isMinOn
    (M : ℝ) (hM : 0 < M) (lam : ℝ) :
    IsMinOn
      (fun τ : ℝ ↦
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ)
      Set.univ
      (cubicRegularizedQuadraticTauMinimizer M lam) := by
  rw [isMinOn_univ_iff]
  intro τ
  -- Compare every slack value with the explicit minimum value attained at `τ(λ)`.
  calc
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) :=
      cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM
    _ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ :=
      cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ

/- Proposition 4.1.8 lies in the Chapter 4 cubic-regularized quadratic / epigraph-duality
domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticTauMinimizer` and
  `cubicRegularizedQuadraticTauMinimizer_isMinOn` in `Definition_4_1_14`, the chapter owner and
  owner minimization theorem for the scalar `τ`-subproblem;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction` in
  `Definition_4_1_13`, the bridge from the source-facing dual owner to the generic Chapter 1
  `LagrangianProblem.dualFunction`;
* `cubicRegularizedQuadraticEpigraphProblem` in `Definition_4_1_14`, the source-facing owner of
  the one-constraint epigraph reformulation.

Best owner abstraction:
* source-facing: eliminate the slack variable `τ` from the epigraph Lagrangian and characterize
  the resulting scalar dual domain;
* core/canonical: `cubicRegularizedQuadraticTauMinimizer`,
  `cubicRegularizedQuadraticDualFunction`, `cubicRegularizedQuadraticDualDomain`, and
  `cubicRegularizedQuadraticEpigraphProblem`;
* bridge/view: the two source-facing bridge theorems below together with the recalled upstream
  domain theorem, which express the source proposition in terms of those established owners.

Primitive data:
* the cubic-regularized quadratic data `g`, `H`, and `M`;
* the shifted quadratic owner `quadraticObjective 0 g (H + λ I)`.

Derived API:
* the explicit slack minimizer `cubicRegularizedQuadraticTauMinimizer M λ`;
* the dual value `cubicRegularizedQuadraticDualFunction g H M λ`;
* the domain `cubicRegularizedQuadraticDualDomain g H M`.

This file therefore stays at the source-facing bridge layer and reuses the existing owner
abstractions instead of introducing a parallel local scalar-dual or `τ`-minimizer owner. -/

section

/-- Helper for Proposition 4.1.8: splitting the scalar epigraph Lagrangian isolates the shifted
quadratic `q_λ(h)` and the one-dimensional `τ`-objective. -/
lemma cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (h : E) (τ lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam =
      quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
        ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) := by
  -- Reuse the owner-side split with the shifted matrix written explicitly.
  simpa using
    cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term g Hmat M h τ lam

/-- Helper for Proposition 4.1.8: the explicit slack minimizer satisfies the displayed
first-order stationarity equation. -/
lemma cubicRegularizedQuadraticTauMinimizer_stationary_eq
    (hM : 0 < M) (lam : ℝ) :
    let τ := cubicRegularizedQuadraticTauMinimizer M lam
    (M / 4 : ℝ) * |τ| ^ (1 / 2 : ℝ) * Real.sign τ = (lam / 2 : ℝ) := by
  -- Evaluate the explicit formula `τ(λ) = 4 λ |λ| / M²` branchwise in the sign of `λ`.
  rcases lt_trichotomy lam 0 with hlam | rfl | hlam
  · dsimp [cubicRegularizedQuadraticTauMinimizer]
    rw [abs_of_neg hlam]
    have htau_neg : (4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ) < 0 := by
      have hnum_neg : (4 : ℝ) * lam * (-lam) < 0 := by
        nlinarith
      have hden_pos : 0 < M ^ (2 : ℕ) := by
        positivity
      exact div_neg_of_neg_of_pos hnum_neg hden_pos
    rw [abs_of_neg htau_neg, Real.sign_of_neg htau_neg]
    -- On the negative branch, `|τ|^(1/2)` reduces to `2 (-λ) / M`.
    have hsqrt : ((-((4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ))) ^ (1 / 2 : ℝ)) = 2 * (-lam) / M := by
      have hsq : -((4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ)) = ((2 * (-lam) / M : ℝ) ^ (2 : ℕ)) := by
        field_simp [hM.ne']
        ring
      rw [hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      · have hnum_nonneg : 0 ≤ 2 * (-lam) := by
          nlinarith
        exact div_nonneg hnum_nonneg hM.le
    calc
      (M / 4 : ℝ) * (-((4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ))) ^ (1 / 2 : ℝ) * (-1 : ℝ)
          = (M / 4 : ℝ) * (2 * (-lam) / M) * (-1 : ℝ) := by
              rw [hsqrt]
      _ = (lam / 2 : ℝ) := by
            field_simp [hM.ne']
            ring
  · simp [cubicRegularizedQuadraticTauMinimizer]
  · dsimp [cubicRegularizedQuadraticTauMinimizer]
    rw [abs_of_pos hlam]
    have htau_pos : 0 < (4 : ℝ) * lam * lam / M ^ (2 : ℕ) := by
      positivity
    rw [abs_of_pos htau_pos, Real.sign_of_pos htau_pos]
    -- On the positive branch, `|τ|^(1/2)` reduces to `2 λ / M`.
    have hsqrt : (((4 : ℝ) * lam * lam / M ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) = 2 * lam / M := by
      have hsq : (4 : ℝ) * lam * lam / M ^ (2 : ℕ) = ((2 * lam / M : ℝ) ^ (2 : ℕ)) := by
        field_simp [hM.ne']
        ring
      rw [hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      · have hnum_nonneg : 0 ≤ 2 * lam := by
          nlinarith
        exact div_nonneg hnum_nonneg hM.le
    calc
      (M / 4 : ℝ) * ((4 : ℝ) * lam * lam / M ^ (2 : ℕ)) ^ (1 / 2 : ℝ) * (1 : ℝ)
          = (M / 4 : ℝ) * (2 * lam / M) * (1 : ℝ) := by
              rw [hsqrt]
      _ = (lam / 2 : ℝ) := by
            field_simp [hM.ne']
            ring

/-- Helper for Proposition 4.1.8: substituting the explicit slack minimizer evaluates the scalar
`τ`-objective to the cubic penalty `-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_at_minimizer
    (hM : 0 < M) (lam : ℝ) :
    let τ := cubicRegularizedQuadraticTauMinimizer M lam
    ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) =
      - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
  -- Reuse the owner-side evaluation of the minimized scalar objective.
  simpa using cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM

-- Proof sketch: differentiate the scalar `τ`-objective, solve the first-order equation
-- `(M / 4) |τ|^(1/2) sign(τ) = λ / 2`, and use convexity of `τ ↦ |τ|^(3/2)` to conclude that the
-- explicit critical point is the global minimizer of the `τ`-subproblem. This is a source-facing
-- bridge built on the owner theorem `cubicRegularizedQuadraticTauMinimizer_isMinOn`.
/-- Proposition 4.1.8 (1): for `M > 0`, minimizing the epigraph Lagrangian with respect to `τ`
at fixed `h` and `λ` is attained at `τ(λ) = 4 λ |λ| / M²`, equivalently at the point satisfying
`(M / 4) |τ|^(1/2) sign(τ) = λ / 2`. -/
theorem cubicRegularizedQuadraticEpigraphLagrangian_tau_isMinOn
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) (h : E) (lam : ℝ) :
    let τ := cubicRegularizedQuadraticTauMinimizer M lam
    (M / 4 : ℝ) * |τ| ^ (1 / 2 : ℝ) * Real.sign τ = (lam / 2 : ℝ) ∧
      IsMinOn
        (fun τ' : ℝ ↦ cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ' lam)
        Set.univ
        τ := by
  let τ := cubicRegularizedQuadraticTauMinimizer M lam
  refine ⟨?_, ?_⟩
  · -- The displayed stationarity identity is the explicit scalar minimizer formula.
    simpa [τ] using cubicRegularizedQuadraticTauMinimizer_stationary_eq (M := M) hM lam
  · rw [isMinOn_univ_iff]
    intro τ'
    have hscalar :
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ ≤
          (M / 6 : ℝ) * |τ'| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ' := by
      -- The owner theorem already minimizes the one-dimensional slack objective.
      simpa [τ] using
        (isMinOn_univ_iff.mp (cubicRegularizedQuadraticTauMinimizer_isMinOn M hM lam)) τ'
    have hsum :
        quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
            ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) ≤
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
            ((M / 6 : ℝ) * |τ'| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ') :=
      by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right hscalar
            (quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h)
    -- Adding the constant quadratic term transports the scalar minimum to the full Lagrangian.
    simpa [τ, cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective]
      using hsum

-- Proof sketch: split the epigraph Lagrangian into the `h`-dependent quadratic part and the
-- scalar `τ`-objective, substitute the explicit minimizer from
-- `cubicRegularizedQuadraticEpigraphLagrangian_tau_isMinOn`, and simplify the resulting minimum
-- value of the `τ`-term to `-(2 / (3 M²)) |λ|³`.
/-- Proposition 4.1.8 (2): after eliminating `τ`, the scalar dual function is the infimum over
`h : ℝⁿ` of the quadratic objective `q_λ(h)` minus the cubic penalty `(2 / (3 M²)) |λ|³`. -/
theorem cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) (lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g Hmat M lam =
      sInf (Set.range fun h : E ↦
        ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal)) := by
  rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
  let τ := cubicRegularizedQuadraticTauMinimizer M lam
  have hτvalue :
      ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) =
        - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
    -- Evaluate the scalar objective at the explicit minimizer once and reuse it on every fiber.
    simpa [τ] using cubicRegularizedQuadraticTauObjective_at_minimizer (M := M) hM lam
  apply le_antisymm
  · refine le_sInf ?_
    rintro y ⟨h, rfl⟩
    have hsInf :
        sInf
            (Set.range
              (fun z : E × ℝ ↦
                (cubicRegularizedQuadraticScalarLagrangian g Hmat M z.1 z.2 lam : EReal))) ≤
          (cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam : EReal) := by
      -- Insert the explicit minimizing slack value as a witness in the product-space infimum.
      exact sInf_le ⟨(h, τ), rfl⟩
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam =
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      -- Substituting the minimized slack term leaves only the shifted quadratic in `h`.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective, hτvalue]
      ring
    simpa [hvalue] using hsInf
  · refine le_sInf ?_
    rintro y ⟨⟨h, τ'⟩, rfl⟩
    have hfiber :
        (M / 4 : ℝ) * |τ| ^ (1 / 2 : ℝ) * Real.sign τ = (lam / 2 : ℝ) ∧
          IsMinOn
            (fun u : ℝ ↦ cubicRegularizedQuadraticScalarLagrangian g Hmat M h u lam)
            Set.univ
            τ := by
      -- Route correction: use the proposition-local fiberwise minimizer theorem instead of
      -- rebuilding the shifted-matrix bridge inside this `sInf` comparison.
      simpa [τ] using
        cubicRegularizedQuadraticEpigraphLagrangian_tau_isMinOn
          g Hmat hM h lam
    have hsInf :
        sInf
            (Set.range
              (fun h : E ↦
                ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
                    (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal))) ≤
          ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
              (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal) := by
      -- The reduced infimum is bounded above by the value on the current `h`-fiber.
      exact sInf_le ⟨h, rfl⟩
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam =
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      -- The minimizing point on the fiber has exactly the reduced objective value.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective, hτvalue]
      ring
    have hmin_real :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam ≤
          cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ' lam := by
      -- Fiberwise minimality compares the chosen slack minimizer with every other slack value.
      exact (isMinOn_univ_iff.mp hfiber.2) τ'
    have hmin :
        ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal) ≤
          (cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ' lam : EReal) := by
      -- Rewrite the minimizing-fiber value into the reduced quadratic form before coercing.
      rw [hvalue] at hmin_real
      exact EReal.coe_le_coe_iff.2 hmin_real
    exact le_trans hsInf hmin

-- Proof sketch: use
-- `cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic` and observe that subtracting
-- the finite constant `(2 / (3 M²)) |λ|³` does not change whether the infimum is strictly above
-- `-∞`; equivalently, the domain is determined exactly by boundedness below of the quadratic
-- objective `q_λ`.
/-- Proposition 4.1.8 (3): the effective domain consists exactly of those multipliers `λ` for
which the shifted quadratic objective `q_λ` is bounded below. -/
theorem cubicRegularizedQuadraticScalarDualDomain_eq
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) :
    cubicRegularizedQuadraticDualDomain g Hmat M =
      { lam |
        BddBelow
          (Set.range
            (quadraticObjective 0 g
              (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)))) } := by
  ext lam
  constructor
  · intro hdom
    change ⊥ < cubicRegularizedQuadraticDualFunction g Hmat M lam at hdom
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine ⟨(cubicRegularizedQuadraticDualFunction g Hmat M lam).toReal + κ, ?_⟩
    rintro y ⟨h, rfl⟩
    have hsle : cubicRegularizedQuadraticDualFunction g Hmat M lam ≤
        (cubicRegularizedQuadraticScalarLagrangian g Hmat M h
          (cubicRegularizedQuadraticTauMinimizer M lam) lam : EReal) := by
      -- Evaluate the infimum at the explicit slack minimizer.
      rw [cubicRegularizedQuadraticDualFunction]
      exact sInf_le ⟨(h, cubicRegularizedQuadraticTauMinimizer M lam), rfl⟩
    have hsle_real :
        (cubicRegularizedQuadraticDualFunction g Hmat M lam).toReal ≤
          cubicRegularizedQuadraticScalarLagrangian g Hmat M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam :=
      EReal.toReal_le_toReal hsle (ne_of_gt hdom) (EReal.coe_ne_top _)
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam =
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h - κ := by
      -- After minimizing over `τ`, only the shifted quadratic in `h` remains.
      dsimp [κ]
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term,
        cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM]
      ring
    rw [hvalue] at hsle_real
    dsimp [κ]
    nlinarith
  · rintro ⟨b, hb⟩
    change ⊥ < cubicRegularizedQuadraticDualFunction g Hmat M lam
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine lt_of_lt_of_le (EReal.bot_lt_coe (b - κ)) ?_
    rw [cubicRegularizedQuadraticDualFunction]
    refine le_sInf ?_
    rintro y ⟨⟨h, τ⟩, rfl⟩
    have hq : b ≤ quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h :=
      hb ⟨h, rfl⟩
    have hτ : -κ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
      -- The slack-variable objective is always at least the explicit minimum value.
      dsimp [κ]
      simpa using cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ
    have hsum : b - κ ≤ cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam := by
      -- Combine the quadratic lower bound with the universal scalar lower bound.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
      nlinarith
    exact EReal.coe_le_coe_iff.2 hsum

end

/-! ### Theorem_4_1_8 (from Chap04) -/
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
