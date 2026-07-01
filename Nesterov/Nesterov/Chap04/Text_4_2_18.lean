import Mathlib
import Nesterov.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MinGradientNormAlongIterates

noncomputable section

universe u

/- Text 4.2.18 lies in the chapter finite-window best-gradient domain for accelerated
cubic-Newton iterates.

Sampled owner declarations:
* `minGradientNormAlongIterates` in `Chap02/Definition_2_23`, the core owner for the sampled
  minimum gradient norm over a finite iterate window;
* the source-facing notation `g[f; x; k, T | h]` for that owner, also in
  `Chap02/Definition_2_23`;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Theorem_4_2_2`, the nearby
  chapter rate theorem whose radius parameter is already owned canonically as a nonnegative
  constant;
* `false_acceleration_gap_le_inverse_eighth_rate` in `Text_4_2_17`, the neighboring scalar-rate
  theorem that likewise records its radius data with `R : NNReal`;
* `minGradientNormAlongIterates.le`, the canonical pointwise upper-bound API for the same owner;
* `acceleratedCubicNewton_minGradientNorm_le_intermediate_bound` and
  `acceleratedCubicNewton_minGradientNorm_lt_explicit_rate` in `Text_4_2_19`, the later
  accelerated-cubic-Newton rate statements using the same owner notation with `T = 4m`.

Source/core/bridge triage:
* source-facing: Text 4.2.18's sampled minimum gradient norm `g_T^*` for the first `T` iterates;
* core/canonical: `minGradientNormAlongIterates f x 1 T h`;
* bridge/view: the chapter owner notation `g[f; x; 1, T | h]`, with no extra local wrapper.

Primitive data:
* the objective `f`, the iterate sequence `x`, and the comparison point `xStar`;
* the chapter-standard Hessian-Lipschitz owner parameter `L3 : NNReal`, the chapter-standard
  nonnegative radius owner `D : NNReal`, and the source-required positivity hypothesis
  `0 < (L3 : ℝ)`;
* the fixed-start window witness `1 ≤ T`, and for the explicit-rate specialization only the index
  relation `T = 3m + 2`;
* the two displayed inequalities controlling the gap at `x_{2m}` and the drop from `x_{2m}` to
  `x_T`, both kept as explicit theorem binders rather than ambient section assumptions;
* the single comparison `f xStar ≤ f (x T)` used to pass from the gap at `x_{2m}` relative to
  `xStar` to the drop from `x_{2m}` to `x_T`.

Derived API:
* the intermediate and explicit rate bounds proved below.

Accordingly, this file keeps the source-facing textbook bound but replaces the duplicate scalar
placeholder `gT` by the chapter owner `minGradientNormAlongIterates`, hides the auxiliary witness
`1 ≤ T` behind local source-facing notation for the fixed-start sampled minimum, records the radius
with the chapter-standard nonnegative owner `D : NNReal`, and states the objective gaps directly as
evaluations of `f` on the iterates instead of as separate primitive scalar variables.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section AcceleratedCubicNewtonGradientNormBound

variable {f : E → ℝ} {x : ℕ → E} {xStar : E}
variable {m T : ℕ}
variable {L3 : NNReal} {D : NNReal}

section FixedStartWindow

variable (h1T : 1 ≤ T)

local notation "g⋆[" T "]" => g[f; x; 1, T | h1T]

-- Proof sketch: combine the upper bound on `f (x (2 * m)) - f xStar` with the lower bound on
-- `f (x (2 * m)) - f (x T)` and the direct comparison `f xStar ≤ f (x T)`. This yields an upper
-- bound on `Real.rpow g⋆[T] (3 / 2)`, after which one raises both sides to the
-- power `2 / 3`.
/-- The two displayed estimates preceding Text 4.2.18 imply the intermediate bound
`g_T^* ≤ ((27 L₃^(3/2) D^3) / (4 (m + 2)^3))^(2/3)` for the fixed-start sampled minimum
`g_T^* = g⋆[T] = min_{1 ≤ k ≤ T} ‖∇ f (x k)‖`, where `D` is recorded as a
nonnegative radius constant. -/
theorem accelerated_cubic_newton_min_gradient_norm_le_intermediate_bound
    (hL3 : 0 < (L3 : ℝ))
    (hxStarT : f xStar ≤ f (x T))
    (heven_gap :
      f (x (2 * m)) - f xStar ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)))
    (hterminal_drop :
      f (x (2 * m)) - f (x T) ≥
        ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[T] (3 / 2 : ℝ))
    :
    g⋆[T] ≤
      Real.rpow
        (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
        (2 / 3 : ℝ) := sorry

end FixedStartWindow

section FixedStartWindowExplicit

variable (hT : T = 3 * m + 2)

local notation "g⋆[" T "]" => g[f; x; 1, T | by omega]

-- Proof sketch: apply
-- `accelerated_cubic_newton_min_gradient_norm_le_intermediate_bound`, then substitute
-- `m + 2 = (T + 4) / 3` from `T = 3m + 2` and simplify the resulting powers of `3`, `2`, and
-- `(D : ℝ)`.
/-- Text 4.2.18: if the accelerated cubic-Newton iterates satisfy
`f(x_{2m}) - f(xStar) ≤ 9 L₃ D^3 / (4 (m + 2)^2)` and
`f(x_{2m}) - f(x_T) ≥ ((m + 2) / (3 √L₃)) (g_T^*)^(3/2)` with `T = 3m + 2`, then the fixed-start
sampled minimum gradient norm
`g_T^* = g⋆[T] = min_{1 ≤ k ≤ T} ‖∇ f (x k)‖` satisfies the explicit inverse-square bound
`g_T^* ≤ 3^4 L₃ D^2 / (2^(4/3) (T + 4)^2)` provided `L₃ > 0` and `f xStar ≤ f (x_T)`, for
instance when `xStar` is a global minimizer. -/
theorem accelerated_cubic_newton_min_gradient_norm_le_explicit_rate
    (hL3 : 0 < (L3 : ℝ))
    (hxStarT : f xStar ≤ f (x T))
    (heven_gap :
      f (x (2 * m)) - f xStar ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)))
    (hterminal_drop :
      f (x (2 * m)) - f (x T) ≥
        ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[T] (3 / 2 : ℝ))
    :
    g⋆[T] ≤
      ((3 : ℝ) ^ (4 : ℕ) * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
        (Real.rpow 2 (4 / 3 : ℝ) * (T + 4 : ℝ) ^ (2 : ℕ)) := sorry

end FixedStartWindowExplicit

end AcceleratedCubicNewtonGradientNormBound
