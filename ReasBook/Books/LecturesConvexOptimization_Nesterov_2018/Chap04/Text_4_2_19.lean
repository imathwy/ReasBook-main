import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MinGradientNormAlongIterates

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.19 lies in the chapter finite-window best-gradient domain for accelerated
cubic-Newton rate estimates.

Sampled owner declarations:
* `minGradientNormAlongIterates` in `Chap02/Definition_2_23`, the core owner for the sampled
  minimum gradient norm over a finite iterate window;
* the source-facing notation `g[f; x; k, T | h]` for that owner, also in
  `Chap02/Definition_2_23`;
* `accelerated_cubic_newton_min_gradient_norm_le_explicit_rate` in `Text_4_2_18`, the immediate
  predecessor source-facing rate statement for the same sampled-minimum domain.

Source/core/bridge triage:
* source-facing: Text 4.2.19's sampled minimum gradient norm over the window `1 ≤ k ≤ 4m`,
  written below as `g⋆[m]`;
* core/canonical: `minGradientNormAlongIterates f x 1 (4 * m) h`;
* bridge/view: the local source-facing notation `g⋆[m]`, with no extra owner-level wrapper.

Primitive data:
* the objective `f`, iterate sequence `x`, initial point `x0`, and comparison point `xStar`;
* the integer parameter `m`, with the source window condition `m ≥ 1`;
* the source-required positive-`L₃` regime `0 < (L3 : ℝ)`;
* the single comparison `f xStar ≤ f (x (4 * m))` used to pass from the gap at `x_{3m}`
  relative to `xStar` to the drop from `x_{3m}` to `x_{4m}`;
* the gap and descent inequalities at the iterates `x_{3m}` and `x_{4m}`.

Derived API:
* the specialized sampled minimum gradient norm `g⋆[m]`;
* the intermediate `rpow` estimate and the final explicit rate stated in the text.

Accordingly, this file works at the weaker iterate-sequence layer already used in `Text_4_2_18`:
the accelerated cubic-Newton algorithm package is not primitive mathematical data for the two
displayed inequalities, so the public theorems are stated for an arbitrary sequence `x : ℕ → E`.
The fixed-start sampled minimum is written with the local notation `g⋆[m]` so the theorem surface
does not expose the auxiliary witness `1 ≤ 4m`, and the intermediate and explicit estimates remain
separate atomic theorems instead of a conjunction-valued wrapper. -/

section AcceleratedCubicNewtonGradientNormBound

variable {f : E → ℝ} {L3 : NNReal} {x : ℕ → E} {x0 xStar : E}
variable {m : ℕ} (hm : 1 ≤ m)
local notation "g⋆[" m "]" => g[f; x; 1, 4 * m | by omega]

-- Proof sketch: the comparison `hxStar4m : f xStar ≤ f (x (4m))` gives
-- `f (x (3m)) - f (x (4m)) ≤ f (x (3m)) - f xStar`. Combine the assumed upper and
-- lower bounds, using `hL3 : 0 < (L3 : ℝ)` for the square-root and `rpow` manipulations, to get
-- an estimate on `Real.rpow g⋆[m] (3 / 2)`, then raise both sides to the power `2 / 3`.
/-- Under `0 < (L3 : ℝ)`, the comparison `f xStar ≤ f (x (4 * m))`, the gap bound at
`x_{3m}`, and the descent lower bound from `x_{3m}` to `x_{4m}`,
Text 4.2.19 first yields the intermediate estimate on the sampled minimum
`g⋆[m] = min_{1 ≤ k ≤ 4m} ‖∇ f (x k)‖`,
namely
`g⋆[m] ≤
(8 L₃^(3/2) R₀^3 / (m² (3m + 1) (3m + 2)))^(2/3)`, where `R₀ = ‖x₀ - xStar‖`. -/
theorem acceleratedCubicNewton_minGradientNorm_le_intermediate_bound
    (hL3 : 0 < (L3 : ℝ))
    (hxStar4m : f xStar ≤ f (x (4 * m)))
    (hgap :
      f (x (3 * m)) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
    (hdrop :
      f (x (3 * m)) - f (x (4 * m)) ≥
        ((m : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[m] (3 / 2 : ℝ)) :
    g⋆[m] ≤
      Real.rpow
        ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
        (2 / 3 : ℝ) := sorry

-- Proof sketch: apply `acceleratedCubicNewton_minGradientNorm_le_intermediate_bound`, then use
-- `(3m + 1) (3m + 2) > 9 m²` to simplify the denominator and rewrite the result in terms of
-- `(4m)^(8/3)`.
/-- Text 4.2.19: let `f` have third-order Lipschitz constant `L₃`, let `xStar` be a minimizer,
let `R₀ = ‖x₀ - xStar‖`, and let `x` be an iterate sequence satisfying the two displayed
inequalities at `x_{3m}` and `x_{4m}`. If for some `m ≥ 1` one has the objective-gap bound at
`x_{3m}` and the descent lower bound from `x_{3m}` to `x_{4m}` involving the sampled minimum
`g⋆[m] = min_{1 ≤ k ≤ 4m} ‖∇ f (x k)‖`, then, provided
`0 < (L3 : ℝ)` and `f xStar ≤ f (x (4 * m))` (for instance because `xStar` is a global
minimizer for the iterates under consideration), one gets
`g⋆[m] < 2^8 L₃ R₀² / (4m)^(8/3)`. -/
theorem acceleratedCubicNewton_minGradientNorm_lt_explicit_rate
    (hL3 : 0 < (L3 : ℝ))
    (hxStar4m : f xStar ≤ f (x (4 * m)))
    (hgap :
      f (x (3 * m)) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
    (hdrop :
      f (x (3 * m)) - f (x (4 * m)) ≥
        ((m : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[m] (3 / 2 : ℝ)) :
    g⋆[m] <
      ((2 : ℝ) ^ (8 : ℕ) * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        Real.rpow (4 * m : ℝ) (8 / 3 : ℝ) := sorry

end AcceleratedCubicNewtonGradientNormBound
