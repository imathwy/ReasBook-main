import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Algorithm_4_2_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_1_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Text_4_2_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LevelSetNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.2.2 lies in the whole-space cubic-Newton / Hessian-Lipschitz rate domain.

Sampled owner declarations:
* `CubicNewtonMethod` in `Algorithm_4_2_1`, the chapter owner for the iterate sequence, the
  chosen cubic Newton step, and the standing `C22[L3]` smoothness hypothesis;
* `CubicNewtonMethod.step_isMinOn` in `Algorithm_4_2_1`, the derived owner theorem recovering the
  minimizing property of each cubic Newton step on the canonical cubic model;
* `convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Text_4_2_8`, the
  chapter cubic-model comparison theorem turning convexity plus a minimizing step into one-step
  objective decrease;
* `IsMinOn` and `ConvexOn ℝ Set.univ f`, the canonical minimizer and convexity owners used on the
  theorem surface.

Source/core/bridge triage:
* source-facing: the inverse-square gap estimate for a monotone cubic Newton trajectory with a
  bounded initial sublevel set;
* core/canonical: `CubicNewtonMethod f L3 x0` together with `IsMinOn f Set.univ xStar`;
* bridge/view: the radius control on the initial sublevel set.

Primitive data:
* the objective `f`;
* the cubic Newton method owner `method`;
* the minimizer `xStar`;
* the explicit radius constant `D`;
* the bounded-sublevel radius control assumption.

Derived API:
* `ContDiff ℝ 2 f`;
* global Hessian-Lipschitz control for `hessian f`;
* positivity of `(L3 : ℝ)`;
* global minimality of each cubic Newton step on the canonical cubic model;
* the one-step decrease `f (method (k + 1)) ≤ f (method k)`, derived from convexity via
  `convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation`.

The previous theorem surface repeated those derived items as primitive hypotheses. This refinement
keeps the source-facing rate theorem, but rewrites it directly on the chapter owner
`CubicNewtonMethod` and leaves only the genuinely extra bounded-sublevel assumption public. -/

namespace CubicNewtonMethod

/-- Convexity and the cubic-model minimizing property force one-step objective decrease along a
cubic Newton method. -/
theorem objective_succ_le
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : CubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) :
    f (method (k + 1)) ≤ f (method k) := by
  rw [method.x_succ]
  have hdecrease :
      f (method k) - f (method.step (method k)) ≥
        ((L3 : ℝ) / 3 : ℝ) * ‖method k - method.step (method k)‖ ^ (3 : ℕ) :=
    convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation
      method.objective_mem
      hf_conv
      le_rfl
      (method.step_isMinOn (method k))
  have hnonneg :
      0 ≤ ((L3 : ℝ) / 3 : ℝ) * ‖method k - method.step (method k)‖ ^ (3 : ℕ) := by
    positivity
  linarith

end CubicNewtonMethod

section

variable {f : E → ℝ} {L3 : NNReal} {x0 xStar : E}

local notation "𝓛0" => (𝓛[f]((f x0)) : Set E)

-- Proof sketch: the derived one-step decrease theorem `method.objective_succ_le hf_conv`
-- keeps every iterate `method k` inside the canonical initial sublevel set `𝓛0`, so `hlevel`
-- gives `‖method k - xStar‖ ≤ D`. Use convexity on the segment from `method k` to `xStar`, then
-- combine the cubic-model minimizing property supplied by `method.step_isMinOn (method k)` with
-- the Taylor upper bound coming from `method.objective_mem : f ∈ C22[L3]` to obtain the scalar
-- recurrence `δ_{k+1} ≤ δ_k - τ δ_k + τ^3 (L₃ / 3) D^3` for
-- `δ_k = f (method k) - f xStar`. Optimizing in `τ` and telescoping the reciprocal square-root
-- inequality yields the inverse-square estimate.
/-- Theorem 4.2.2: for a convex objective with `L₃`-Lipschitz continuous Hessian, if the cubic
Newton initial sublevel set `𝓛[f]((f x₀))` is contained in the closed ball of radius `D`
around a minimizer `x*`, then every iterate with index `k ≥ 1` satisfies
`f(x_k) - f(x*) ≤ 9 L₃ D^3 / (k + 4)^2`. -/
theorem cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel
    (method : CubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (D : ℝ)
    (hlevel : ∀ ⦃z : E⦄, z ∈ 𝓛0 → ‖z - xStar‖ ≤ D)
    (k : ℕ) (hk : 1 ≤ k) :
    f (method k) - f xStar ≤
      (9 * (L3 : ℝ) * D ^ (3 : ℕ)) / ((k + 4 : ℝ) ^ (2 : ℕ)) := by
  sorry

end
