import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap02.Theorem_2_5
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_23
import LecturesConvexOptimization_Nesterov_2018.Chap07.Proposition_7_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient PositiveDefMatrixNorm SmoothConvex

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.15 lies in the Chapter 7 smoothing / weighted-seminorm smoothness domain.

Sampled owner-style declarations:
- `absLinearLogSumExp_contDiff` in `Proposition_7_14`
- `absLinearLogSumExp_hessian_quadraticForm_eq` in `Proposition_7_14`
- `positiveDefMatrixNorm` in `Definition_7_23`
- `ConvexC1SeminormSmooth.dualNorm_gradient_sub_le` in `Chap02/Theorem_2_5`

Best owner abstraction:
- source-facing: the weighted `G`-norm Hessian and gradient estimates for `absLinearLogSumExp μ a`
- core/canonical: `absLinearLogSumExp μ a ∈ 𝓕[L, positiveDefMatrixNorm G.1 G.2]¹¹`
- bridge/view: the explicit Hessian quadratic-form bound and its source-facing dual-gradient
  Lipschitz corollary

Primitive data:
- the family `a : Fin m → E`
- the positive-definite matrix owner `G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}`
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`
- the weighted dual-norm bound on the vectors `a i`

Derived API:
- `ContDiff ℝ 2 (absLinearLogSumExp μ a)`, already owned by `Proposition_7_14`
- the weighted Hessian quadratic-form upper bound
- the owner-level smooth-convex membership theorem
- the source-facing weighted dual-gradient Lipschitz estimate

Source/core/bridge triage:
- source-facing: the weighted Hessian and gradient bounds
- core/canonical: the smooth-convex owner `𝓕[L, p]¹¹`
- bridge/view: the explicit quadratic-form estimate needed to enter that owner API

The previous conjunction theorem duplicated the upstream owner `absLinearLogSumExp_contDiff` and
attached the weighted-norm hypothesis `ha` to a smoothness statement that does not use it. This
refinement keeps only the genuinely new weighted estimates and routes the gradient conclusion
through the Chapter 2 owner API. -/

section

variable (a : Fin m → E) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) {ν : ℝ}
variable (μ : {μ : ℝ // 0 < μ})
variable (ha : ∀ i : Fin m, ‖a i‖[G,*] ≤ ν * Real.sqrt n)

-- Proof sketch: combine Proposition 7.14 with the chapter owner `positiveDefMatrixNorm`: the
-- smoothness is `absLinearLogSumExp_contDiff`, the Hessian quadratic form is
-- `absLinearLogSumExp_hessian_quadraticForm_eq`, and the weighted dual-norm bound on the `aᵢ`
-- controls the second-moment term by `ν² n / μ`.
/-- Proposition 7.15: if `‖aᵢ‖_G^* ≤ ν √n` for every `i`, then the Hessian quadratic form of
`f_μ(x) = μ log ∑ᵢ (exp(⟪aᵢ, x⟫ / μ) + exp(-⟪aᵢ, x⟫ / μ))`
is bounded above by `(ν² n / μ) ‖h‖_G²`. The `C²` regularity is already the owner theorem
`absLinearLogSumExp_contDiff` from `Proposition_7_14`. -/
theorem absLinearLogSumExp_hessian_quadraticForm_le (x h : E) :
    inner ℝ (hessian (absLinearLogSumExp μ a) x h) h ≤
      (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) * ‖h‖[G] ^ (2 : ℕ) := sorry

-- Proof sketch: `absLinearLogSumExp_contDiff μ` gives the regularity input, while
-- `absLinearLogSumExp_hessian_quadraticForm_le` supplies the upper Hessian bound. Combine these
-- with the Chapter 2 owner bridge `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` to
-- place `absLinearLogSumExp μ a` in the smooth-convex class for the weighted norm
-- `positiveDefMatrixNorm G.1 G.2`.
/-- The Chapter 2 smooth-convex owner view of Proposition 7.15 for the weighted norm `‖·‖_G`. -/
theorem absLinearLogSumExp_mem_F11_positiveDefMatrixNorm :
    absLinearLogSumExp μ a ∈
      𝓕[Real.toNNReal ((((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ))), positiveDefMatrixNorm G.1 G.2]¹¹ :=
  sorry

-- Proof sketch: apply the owner theorem
-- `absLinearLogSumExp_mem_F11_positiveDefMatrixNorm`, then specialize the defining
-- `dualNorm_gradient_sub_le` consequence of `𝓕[L, p]¹¹` to the weighted seminorm
-- `positiveDefMatrixNorm G.1 G.2`.
/-- The gradient of the log-sum-exp smoothing is Lipschitz with respect to the `G`-norm and its
dual norm, with constant `ν² n / μ`. -/
theorem absLinearLogSumExp_dual_gradient_sub_le (x y : E) :
    ‖∇ (absLinearLogSumExp μ a) x - ∇ (absLinearLogSumExp μ a) y‖[G,*] ≤
      (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) * ‖x - y‖[G] := sorry

end

end
