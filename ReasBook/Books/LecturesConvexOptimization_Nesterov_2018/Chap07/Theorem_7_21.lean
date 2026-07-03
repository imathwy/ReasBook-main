import Mathlib
import Nesterov.Chap07.Definition_7_23
import Nesterov.Chap07.Lemma_7_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PositiveDefMatrixNorm RelativeScaleTransformNotation

variable {n : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin (n : ℕ))

/- Theorem 7.21 lies in the chapter's relative-scale / positive-definite weighted-norm /
estimating-sequence domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` and the notations `‖·‖[G]`, `‖·‖[G,*]` in `Chap07/Definition_7_23`,
  the chapter owner for the primal and dual norms induced by a positive-definite matrix;
- `positiveDefMatrixNorm_quadraticDistanceTo_apply` in `Chap07/Definition_7_46`, the weighted
  quadratic-prox owner behind the term `(1 / 2) ‖x₀ - x*‖[G₀]^2`;
- `relativeScaleTransformedObjective` and the notation `f̂` in `Chap07/Lemma_7_20`, the chapter
  owner for the transformed objective `x ↦ (1 / 2) f(x)^2`;
- `estimating_function_le_weighted_transformed_objective_add_initial` in `Chap07/Lemma_7_21`,
  the nearby additive estimating-sequence recursion theorem.

Best owner abstraction:
- source-facing: Theorem 7.21's best-point and weighted-average bounds for the relative-scale
  high-order method;
- core/canonical: `positiveDefMatrixNorm`, `f̂`, and the accumulated-weight sequence `A`;
- bridge/view: the explicit exponential lower bound on `A_{k+1}` coming from the preceding
  quasi-Newton metric analysis.

Primitive data:
- the objective `f`, the positive-definite metric `G₀`, the base point `x₀`, and the comparison
  point `x*`;
- the source-facing sequences `x_k^*`, `\tilde x_k`, and `A_k`;
- the positive dimension `n : ℕ+`, the scalar parameter `δ`, and the positive smoothness owner
  `L : NNRealˣ`.

Derived API:
- the transformed-objective bound for the best points `x_k^*`;
- the parallel transformed-objective bound for the weighted-average points `\tilde x_{k+1}`.

The previous version rebuilt theorem-local primal and dual norm owners and packaged the three
source sequences into a second wrapper structure. This refinement reuses the Chapter 7 weighted
norm owner directly and keeps the primitive sequences separate from the scalar side conditions and
one-step estimates that drive the theorem.
-/

section RelativeScaleHighOrderMethod

variable {f : E → ℝ}
variable {G0 : {G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // G.PosDef}}
variable {x0 xStar : E} {δ : ℝ} {L : NNRealˣ}
variable {A : ℕ → ℝ}

-- Proof sketch: combine the one-step estimate for `x_k^*` with the lower bound on `A_{k+1}`,
-- then substitute `R = ‖x₀ - x⋆‖_{G₀}` and simplify the reciprocal factor.
/-- Theorem 7.21: for the high-order method in relative scale, if `\hat f(x) = (1 / 2) f(x)^2`,
the quasi-Newton estimating-sequence analysis provides the standard one-step bound for the best
points `x_k^*` together with the exponential lower bound on `A_{k+1}`, then
`(1 - δ) \hat f(x_k^*) ≤ \hat f(x^*) + L^2 ‖x₀ - x^*‖_{G₀}^2 /
  (2 n (e^{δ (k + 1) / n} - 1))` for every `δ > 0`. -/
theorem relativeScaleHighOrderMethod_best_point_bound
    {xBest : ℕ → E}
    (hδ : 0 < δ)
    (hbest :
      ∀ k : ℕ,
        (1 - δ) * f̂ (xBest k) ≤
          f̂ xStar + (‖x0 - xStar‖[G0] ^ (2 : ℕ)) / (2 * A (k + 1)))
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    (1 - δ) * f̂ (xBest k) ≤
      f̂ xStar +
        (((L : ℝ) ^ (2 : ℕ)) * ‖x0 - xStar‖[G0] ^ (2 : ℕ)) /
          (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)) := sorry

-- Proof sketch: apply the same argument as for the best-point estimate, now starting from the
-- one-step inequality for the weighted-average points `\tilde x_{k+1}`.
/-- The weighted-average points satisfy the same transformed-objective estimate as the best
points, with `x_k^*` replaced by `\tilde x_{k+1}`. -/
theorem relativeScaleHighOrderMethod_weighted_average_bound
    {xTilde : ℕ → E}
    (hδ : 0 < δ)
    (hweighted :
      ∀ k : ℕ,
        (1 - δ) * f̂ (xTilde (k + 1)) ≤
          f̂ xStar + (‖x0 - xStar‖[G0] ^ (2 : ℕ)) / (2 * A (k + 1)))
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    (1 - δ) * f̂ (xTilde (k + 1)) ≤
      f̂ xStar +
        (((L : ℝ) ^ (2 : ℕ)) * ‖x0 - xStar‖[G0] ^ (2 : ℕ)) /
          (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)) := sorry

end RelativeScaleHighOrderMethod

end
