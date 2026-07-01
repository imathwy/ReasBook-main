import Mathlib
import Nesterov.Chap02.Theorem_2_5
import Nesterov.Chap01.Definition_1_4_16
import Nesterov.Chap01.Definition_1_10_2
import Nesterov.Chap03.Definition_3_9
import Nesterov.Chap07.Definition_7_42
import Nesterov.Chap07.Definition_7_23
import Nesterov.Chap07.Definition_7_35

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanSpace (nonnegativeOrthant)
open scoped BigOperators Gradient PositiveDefMatrixNorm SmoothConvex SupportFunction

noncomputable section

variable {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 7.21 lies in Chapter 7's sign-symmetric support / weighted smooth-max domain.

Sampled owner-style declarations:
- `hessian` in `Chap01/Definition_1_4_16`, the project owner for second-order derivatives;
- `ξ[Q]` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for support
  functions;
- `positiveDefMatrixNorm` and the notations `‖x‖[D]`, `‖x‖[D,*]` in `Chap07/Definition_7_23`,
  the chapter owners for the weighted norm and its dual;
- `𝓕[L, p]¹¹` and `ConvexC1SeminormSmooth.dualNorm_gradient_sub_le` in `Chap02/Theorem_2_5`,
  the canonical smoothness owner and its gradient-Lipschitz consequence;
- `Matrix.IsDiag` in mathlib's matrix diagonal API, the canonical owner for the diagonality
  needed to pass from `h` to `|h|` in the weighted norm;
- `signSymmetricConvexHull` in `Chap07/Definition_7_35`, the source-facing owner carrying the
  needed absolute-value support data;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the source-facing smoothing owner for
  finite max-inner objectives.

Best owner abstraction:
- source-facing: Proposition 7.21's Hessian and dual-gradient estimates for
  `smoothMaxInnerApproximation a μ`;
- core/canonical: `hessian`, `smoothMaxInnerApproximation a μ`, `positiveDefMatrixNorm`, and the
  Chapter 7 box-hull owner `signSymmetricConvexHull a`;
- bridge/view: the orthant support upper bound for `ξ[signSymmetricConvexHull a]`, which is the
  correct source-facing way to control the absolute pairings `|⟪aᵢ, h⟫|` entering the Hessian.

Primitive data:
- the finite family `a : ι → E`;
- the orthant hypothesis `ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n`;
- the diagonal positive-definite matrix owner `D` together with `hDdiag : D.1.IsDiag`;
- the positive smoothing parameter `μ`.

Derived API:
- the orthant support upper bound for the sign-symmetric hull;
- the Hessian quadratic-form bound;
- the Chapter 2 smooth-convex owner theorem for `smoothMaxInnerApproximation a μ`;
- the resulting weighted dual-gradient Lipschitz estimate.

Source/core/bridge triage:
- source-facing: the Hessian and weighted dual-gradient estimates below;
- core/canonical: `hessian`, `smoothMaxInnerApproximation a μ ∈ 𝓕[L, ‖·‖[D]]¹¹`,
  `signSymmetricConvexHull a`, and the weighted norm owner `‖·‖[D]`;
- bridge/view: the orthant support assumption, kept as theorem-level data rather than a duplicate
  public wrapper.

This refinement removes the orthant-restricted finite-range support hypothesis, which was too weak
for global Hessian control. Proposition 7.21 now uses the sign-symmetric hull owner that carries
the needed absolute-value layer from the surrounding Chapter 7 development.
-/

section

variable (a : ι → E)
variable (D : {D : Mat // D.PosDef}) (μ : {μ : ℝ // 0 < μ})

/-- Proposition 7.21: if the sign-symmetric box-hull support function of a nonnegative family
`(a i)_{i ∈ ι}` is bounded on the nonnegative orthant by `2 √n ‖·‖_D` for a diagonal
positive-definite matrix `D`, then the Hessian quadratic form of the log-sum-exp smoothing
`smoothMaxInnerApproximation a μ` is bounded by
`(4 n / μ) ‖h‖_D²`. -/
-- Proof sketch: the standard log-sum-exp Hessian estimate gives
-- `⟪∇²f_μ(x) h, h⟫ ≤ μ⁻¹ (max_i |⟪aᵢ, h⟫|)^2`. For arbitrary `h`, the nonnegative vector
-- `|h|` lies in `nonnegativeOrthant n`, and because each `aᵢ` is nonnegative one has
-- `|⟪aᵢ, h⟫| ≤ (ξ[signSymmetricConvexHull a] |h|).toReal`. Apply `hBoxSupport` at `|h|` and use
-- the diagonal-norm invariance `‖|h|‖[D] = ‖h‖[D]`.
theorem smoothMaxInnerApproximation_hessian_quadratic_form_le
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D])
    (x h : E) :
    inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h ≤
      (4 : ℝ) * n / μ.1 * ‖h‖[D] ^ 2 := sorry

-- Proof sketch: first prove the source-facing Hessian quadratic-form bound above, then combine it
-- with the `C²` regularity and convexity of `smoothMaxInnerApproximation a μ` and apply the
-- Chapter 2 owner bridge `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded`.
/-- The Chapter 2 smooth-convex owner view of Proposition 7.21 for the weighted norm `‖·‖[D]`. -/
theorem smoothMaxInnerApproximation_mem_F11_positiveDefMatrixNorm
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D]) :
    smoothMaxInnerApproximation a μ ∈
      𝓕[Real.toNNReal ((4 : ℝ) * n / μ.1), positiveDefMatrixNorm D.1 D.2]¹¹ := sorry

/-- The gradient of the log-sum-exp smoothing is Lipschitz with respect to the weighted norm
`‖·‖[D]` and its dual norm `‖·‖[D,*]`, with constant `4 n / μ`, for the same diagonal
sign-symmetric support hypothesis. -/
-- Proof sketch: apply the canonical owner theorem
-- `smoothMaxInnerApproximation_mem_F11_positiveDefMatrixNorm` and then specialize the
-- `dualNorm_gradient_sub_le` consequence of `𝓕[L, p]¹¹`.
theorem smoothMaxInnerApproximation_gradient_lipschitz_diagonalWeightedNorm
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D])
    (x y : E) :
    ‖∇ (smoothMaxInnerApproximation a μ) x - ∇ (smoothMaxInnerApproximation a μ) y‖[D,*] ≤
      ((4 : ℝ) * n / μ.1) * ‖x - y‖[D] := sorry

end

end
