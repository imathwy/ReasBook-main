import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_2_18 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped DegreeConditioning

/- Definition 4.2.18 lies in Chapter 4's higher-order conditioning-class domain.

Sampled owner-style declarations:
* `HasIteratedFDerivLipschitzConstantOfDegree p f` in `Definition_4_2_11`
* `σ[p](f)` in `Definition_4_2_11`
* the sibling source-facing class `IsInFunctionClassF23 f` in `Definition_4_2_17`

Best owner abstraction:
* `source-facing`: `IsInFunctionClassF2Lip f`
* `core/canonical`: the inherited finiteness owners
  `HasUniformConvexityParameterOfDegree 2 f`,
  `HasIteratedFDerivLipschitzConstantOfDegree 2 f` and
  `HasIteratedFDerivLipschitzConstantOfDegree 3 f`
* `bridge/view`: the Lean surface notation `f ∈ 𝓕₂Lip`

Primitive data:
* a finite degree-`2` uniform-convexity parameter, carried by the parent owner
  `HasUniformConvexityParameterOfDegree 2 f`
* finiteness of `L[2](f)` and `L[3](f)`, carried by the parent owners

Derived API:
* the inherited instance for `HasIteratedFDerivLipschitzConstantOfDegree 3 f`
* the derived instance for `HasIteratedFDerivLipschitzConstantOfDegree 2 f`
* the positivity theorem `IsInFunctionClassF2Lip.sigma_pos`, now derived from the parent sigma
  owner
* the source-facing notation `f ∈ 𝓕₂Lip`

This file therefore keeps `𝓕₂^{Lip}` as the public source-facing owner, but it reuses the
canonical degree-two and degree-three Lipschitz-finiteness owners directly. It also reuses the
canonical finite-parameter owner for `σ[2](f)` instead of storing sigma-positivity as primitive
data, and it exposes positivity by theorem rather than a global `Fact` instance. -/

/-- Definition 4.2.18: a function belongs to the class `𝓕₂^{Lip}` when its degree-two
uniform-convexity parameter is positive and the degree-two and degree-three derivative Lipschitz
constants are finite. The finiteness clauses are carried by the canonical owner classes
`HasUniformConvexityParameterOfDegree 2 f`,
`HasIteratedFDerivLipschitzConstantOfDegree 2 f` and
`HasIteratedFDerivLipschitzConstantOfDegree 3 f`. -/
class IsInFunctionClassF2Lip (f : E → ℝ) : Prop where
  /-- The degree-two uniform-convexity parameter of `f` is a genuine finite real parameter. -/
  degreeTwo_uniform : HasUniformConvexityParameterOfDegree 2 f
  /-- The gradient of `f` admits a global Lipschitz constant. -/
  degreeTwo_lipschitz : HasIteratedFDerivLipschitzConstantOfDegree 2 f
  /-- The Hessian of `f` admits a global Lipschitz constant. -/
  degreeThree_lipschitz : HasIteratedFDerivLipschitzConstantOfDegree 3 f

attribute [instance] IsInFunctionClassF2Lip.degreeTwo_uniform
attribute [instance] IsInFunctionClassF2Lip.degreeTwo_lipschitz
attribute [instance] IsInFunctionClassF2Lip.degreeThree_lipschitz

scoped[FunctionClasses] notation:50 f:50 " ∈ " "𝓕₂Lip" => IsInFunctionClassF2Lip f

open scoped FunctionClasses

namespace IsInFunctionClassF2Lip

/-- Membership in `𝓕₂Lip` records positivity of the source-facing conditioning parameter
`σ[2](f)`. -/
theorem sigma_pos {f : E → ℝ} (hf : f ∈ 𝓕₂Lip) :
    0 < σ[2](f) := by
  letI : f ∈ 𝓕₂Lip := hf
  exact HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos

end IsInFunctionClassF2Lip

/-! ### Text_4_2_18 (from Chap04) -/
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

/-! ### Text_4_2_19 (from Chap04) -/
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

/-! ### Text_4_2_20 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Text 4.2.20 lies in the cubic-regularization / initial-sublevel-radius domain.

Sampled owner declarations:
* project `cubicallyRegularizedObjective` in `Definition_4_2_16`, the owner of the cubic
  perturbation;
* project `le_cubicallyRegularizedObjective_of_nonneg` in `Definition_4_2_16`, the derived
  monotonicity lemma for nonnegative cubic regularization;
* project `norm_sub_le_of_le_of_initialSublevelDistanceSet_isGreatest` in `Definition_4_2_16`,
  the canonical radius-bound bridge from the source-facing sublevel inequality and an
  `IsGreatest` hypothesis;
* mathlib `IsGreatest`, the canonical owner of the attained-maximum hypothesis.

Source/core/bridge triage:
* source-facing: Text 4.2.20's conclusion that a point with
  `cubicallyRegularizedObjective f δ x₀ x ≤ f x₀` lies within the textbook radius `D`;
* core/canonical: `cubicallyRegularizedObjective f δ x₀`, the canonical sublevel set
  `𝓛[f]((f x₀))`, and `IsGreatest`;
* bridge/view: `initialSublevelDistanceSet f x₀` and the imported owner lemmas relating it to the
  sublevel inequality.

Primitive data:
* the ambient normed additive group `E`;
* the objective `f`, base point `x₀`, and regularization parameter `δ`;
* the attained-maximum radius witness `IsGreatest (initialSublevelDistanceSet f x₀) D`.

Derived API:
* cubic domination of `f` by `cubicallyRegularizedObjective` for `δ ≥ 0`, yielding the
  source-facing sublevel inequality `f x ≤ f x₀`;
* the radius bound coming from the canonical initial-sublevel distance-set owner.

The target statement therefore stays source-facing, but the helper facts are reused from the owner
file and the ambient space is generalized from the concrete model `EuclideanSpace ℝ (Fin n)` to
the intrinsic `NormedAddCommGroup` level already used by the owner API. -/

/-- Text 4.2.20: for a nonnegative cubic regularization parameter, if the cubically regularized
objective at `x` is at most `f x₀`, then `x` belongs to the initial sublevel set
`{y | f y ≤ f x₀}`, hence `‖x - x₀‖` is bounded by any textbook radius `D` that is an attained
maximum of the distances to `x₀` on that sublevel set. -/
theorem norm_sub_le_of_cubicallyRegularizedObjective_le_of_initialSublevelDistanceSet_isGreatest
    (f : E → ℝ) (x0 x : E) {δ : ℝ} (hδ : 0 ≤ δ)
    {D : ℝ}
    (hD : IsGreatest (initialSublevelDistanceSet f x0) D)
    (hx : cubicallyRegularizedObjective f δ x0 x ≤ f x0) :
    ‖x - x0‖ ≤ D := by
  exact
    norm_sub_le_of_le_of_initialSublevelDistanceSet_isGreatest hD
      ((le_cubicallyRegularizedObjective_of_nonneg f x0 x hδ).trans hx)

end

/-! ### Text_4_2_21 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.21 lies in the restarting-gradient auxiliary-bound / logarithmic-threshold domain.

Sampled owner declarations:
* `radiusRatio_exp_neg_lt_one_of_log_threshold` in `Chap03/Proposition_3_45`, the project owner
  turning a logarithmic threshold into an exponential decay bound;
* `Real.exp_lt_one_iff` and `Real.exp_log`, the mathlib scalar owners used by that threshold
  bridge;
* `accelerated_cubic_newton_min_gradient_norm_le_explicit_rate` in `Text_4_2_18`, the nearby
  chapter pattern where the public surface is a source-facing estimate rather than a family of
  one-off scalar wrapper definitions.

Source/core/bridge triage:
* source-facing: Text 4.2.21's conclusion that every index above the displayed logarithmic
  threshold satisfies `‖∇ f (yAux k)‖ ≤ ε`;
* core/canonical: `radiusRatio_exp_neg_lt_one_of_log_threshold` together with `Real.exp`,
  `Real.log`, and `Real.sqrt`;
* bridge/view: the textbook scalar substitutions `δ = ε / (2 D²)` and `x = L₃ D² / ε`.

Primitive data:
* the objective `f`, third-derivative Lipschitz bound `L3`, radius `D`, target accuracy `ε`, and
  auxiliary sequence `yAux`;
* the positivity assumption `0 < ε`;
* the auxiliary gradient estimate after the textbook choice `δ = ε / (2 D²)` has been
  simplified to the source-facing form
  `e^(-2k/3) L₃ D² √(1 + ε / (L₃ D²)) + ε / 2`.

Derived API:
* the logarithmic threshold
  `(3 / 2) log (2 √(((L₃ D² / ε)^2) + L₃ D² / ε))`;
* the target estimate `‖∇ f (yAux k)‖ ≤ ε`.

A previous version exposed two public scalar abbreviations and a separate `δ` parameter whose only
role was to be specialized immediately by an equality hypothesis. The first refinement specialized
`δ` but still left the raw substitution artifacts on the public theorem surface. Those scalars are
not chapter owners, and `δ` is not primitive public data for the source-facing theorem. This
refinement keeps the theorem source-facing, deletes the disposable wrapper API, simplifies the
specialized auxiliary bound on the public surface, and uses ordinary binders for the thresholded
index `k`.
-/

-- Proof sketch: write `x = L₃ D² / ε`, so the assumed estimate becomes
-- `‖∇ f (yAux k)‖ ≤ ε * (x * exp (-(2k / 3)) * √(1 + 1 / x) + 1 / 2)`, and use the lower bound
-- on `k` to obtain `exp (-(2k / 3)) ≤ 1 / (2 * √(x² + x))`, which makes the parenthesized
-- factor at most `1`.
/-- Bridge/view companion for Text 4.2.21: the logarithmic threshold
`(3 / 2) log (2 √(((a / ε)^2) + a / ε))` forces the first scalar term in the restarting
auxiliary gradient estimate to be at most `ε / 2`. The source-facing theorem below then combines
this with the explicit `ε / 2` remainder term. -/
theorem restarting_auxiliary_scalar_term_le_half_of_log_threshold
    {a ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk :
      (3 / 2 : ℝ) * Real.log (2 * Real.sqrt (((a / ε) ^ 2) + a / ε)) ≤
        (k : ℝ)) :
    Real.exp (-(2 * (k : ℝ) / 3)) * a * Real.sqrt (1 + ε / a) ≤ ε / 2 := by
  let x : ℝ := a / ε
  have hkx : (3 / 2 : ℝ) * Real.log (2 * Real.sqrt (x ^ 2 + x)) ≤ (k : ℝ) := by
    simpa [x] using hk
  by_cases hx : 0 < x
  · have ha_pos : 0 < a := by
      have hx' : 0 < a / ε := by simpa [x] using hx
      exact (div_pos_iff_of_pos_right hε).1 hx'
    have hquad_nonneg : 0 ≤ x ^ 2 + x := by
      nlinarith [hx]
    have hlog_arg_pos : 0 < 2 * Real.sqrt (x ^ 2 + x) := by
      have hquad_pos : 0 < x ^ 2 + x := by
        nlinarith [hx]
      have hsqrt_pos : 0 < Real.sqrt (x ^ 2 + x) := Real.sqrt_pos.mpr hquad_pos
      nlinarith
    have hlog_le : Real.log (2 * Real.sqrt (x ^ 2 + x)) ≤ 2 * (k : ℝ) / 3 := by
      nlinarith [hkx]
    have harg_le : 2 * Real.sqrt (x ^ 2 + x) ≤ Real.exp (2 * (k : ℝ) / 3) := by
      exact (Real.log_le_iff_le_exp hlog_arg_pos).mp hlog_le
    have hsqrt_le_half :
        Real.exp (-(2 * (k : ℝ) / 3)) * Real.sqrt (x ^ 2 + x) ≤ 1 / 2 := by
      have hexp_pos : 0 < Real.exp (2 * (k : ℝ) / 3) := Real.exp_pos _
      have hsqrt_div : Real.sqrt (x ^ 2 + x) / Real.exp (2 * (k : ℝ) / 3) ≤ 1 / 2 := by
        refine (div_le_iff₀ hexp_pos).2 ?_
        linarith
      simpa [Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hsqrt_div
    have hsqrt_id : x * Real.sqrt (1 + 1 / x) = Real.sqrt (x ^ 2 + x) := by
      have hleft_nonneg : 0 ≤ x * Real.sqrt (1 + 1 / x) := by
        positivity
      have hright_nonneg : 0 ≤ Real.sqrt (x ^ 2 + x) := by
        positivity
      apply (mul_self_inj_of_nonneg hleft_nonneg hright_nonneg).1
      have hone_nonneg : 0 ≤ 1 + 1 / x := by
        positivity
      calc
        (x * Real.sqrt (1 + 1 / x)) * (x * Real.sqrt (1 + 1 / x)) =
            x ^ 2 * (Real.sqrt (1 + 1 / x)) ^ 2 := by
              ring
        _ = x ^ 2 * (1 + 1 / x) := by
          rw [Real.sq_sqrt hone_nonneg]
        _ = x ^ 2 + x := by
          field_simp [hx.ne']
        _ = Real.sqrt (x ^ 2 + x) * Real.sqrt (x ^ 2 + x) := by
          rw [← sq, Real.sq_sqrt hquad_nonneg]
    have ha_eq : a = ε * x := by
      dsimp [x]
      field_simp [hε.ne']
    have hdiv_eq : ε / (ε * x) = 1 / x := by
      field_simp [hε.ne', hx.ne']
    calc
      Real.exp (-(2 * (k : ℝ) / 3)) * a * Real.sqrt (1 + ε / a) =
          ε * (Real.exp (-(2 * (k : ℝ) / 3)) * (x * Real.sqrt (1 + 1 / x))) := by
            rw [ha_eq, hdiv_eq]
            ring
      _ = ε * (Real.exp (-(2 * (k : ℝ) / 3)) * Real.sqrt (x ^ 2 + x)) := by
        rw [hsqrt_id]
      _ ≤ ε * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hsqrt_le_half hε.le
      _ = ε / 2 := by ring
  · have hx_nonpos : x ≤ 0 := le_of_not_gt hx
    have ha_nonpos : a ≤ 0 := by
      have hx' : a / ε ≤ 0 := by simpa [x] using hx_nonpos
      simpa using (div_le_iff₀ hε).1 hx'
    have hfirst_nonpos :
        Real.exp (-(2 * (k : ℝ) / 3)) * a * Real.sqrt (1 + ε / a) ≤ 0 := by
      have hmid_nonpos : a * Real.sqrt (1 + ε / a) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha_nonpos (Real.sqrt_nonneg _)
      have hexp_nonneg : 0 ≤ Real.exp (-(2 * (k : ℝ) / 3)) := (Real.exp_pos _).le
      simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos hexp_nonneg hmid_nonpos
    linarith

/-- Text 4.2.21: if the auxiliary points of a restarting scheme satisfy
`‖∇ f (y_k^*)‖ ≤ e^(-2k/3) L₃ D² √(1 + ε / (L₃ D²)) + ε / 2` for every `k`, then every index
`k` above the logarithmic threshold `(3 / 2) log (2 √(x² + x))`, with `x = L₃ D² / ε`,
satisfies `‖∇ f (y_k^*)‖ ≤ ε`. -/
theorem gradient_norm_le_target_of_restarting_auxiliary_bound
    (f : E → ℝ) (L3 : NNReal) (D ε : ℝ) (yAux : ℕ → E)
    (hε : 0 < ε)
    (hbound :
      ∀ k : ℕ,
        ‖∇ f (yAux k)‖ ≤
          Real.exp (-(2 * (k : ℝ) / 3)) * (L3 : ℝ) * D ^ 2 *
              Real.sqrt (1 + ε / ((L3 : ℝ) * D ^ 2)) +
            ε / 2)
    (k : ℕ)
    (hk :
      (3 / 2 : ℝ) * Real.log
          (2 * Real.sqrt ((((L3 : ℝ) * D ^ 2 / ε) ^ 2) + (L3 : ℝ) * D ^ 2 / ε)) ≤
        (k : ℝ)) :
    ‖∇ f (yAux k)‖ ≤ ε := by
  have hfirst_le :
      Real.exp (-(2 * (k : ℝ) / 3)) * (L3 : ℝ) * D ^ 2 *
          Real.sqrt (1 + ε / ((L3 : ℝ) * D ^ 2)) ≤
        ε / 2 := by
    simpa [mul_assoc] using
      (restarting_auxiliary_scalar_term_le_half_of_log_threshold hε hk :
        Real.exp (-(2 * (k : ℝ) / 3)) * ((L3 : ℝ) * D ^ 2) *
            Real.sqrt (1 + ε / ((L3 : ℝ) * D ^ 2)) ≤
          ε / 2)
  linarith [hbound k, hfirst_le]

end

/-! ### Text_4_2_22 (from Chap04) -/
noncomputable section

open scoped DegreeConditioning FunctionClasses

universe u

variable {E : Type u}

section AcceleratedCubicNewtonQuadraticConvergenceRegion

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Text 4.2.22 lies in the accelerated cubic-Newton / local quadratic-convergence domain on real
Hilbert spaces.

Sampled owner declarations:
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, the chapter owner for Algorithm `(4.2.46)`;
* `HasQuadraticConvergenceFrom` in `Text_4_2_24`, the existing Chapter 4 owner for quadratic tail
  convergence from a given index;
* `strongConvexAcceleratedCubicNewtonQuadraticRegion` and
  `InStrongConvexAcceleratedCubicNewtonQuadraticRegion` in `Text_4_2_13`, the nearby Chapter 4
  owner pattern for a source-facing local region together with its iterate-entry predicate;
* `newtonQuadraticConvergenceRegion` and
  `hasQuadraticConvergenceFrom_of_mem_newtonQuadraticConvergenceRegion` in `Text_4_2_24`, where
  region membership is bridged to quadratic convergence of the same orbit.

Best owner abstraction:
* source-facing: the local quadratic-convergence region around `xStar`, i.e. the geometric
  threshold neighborhood in which the iterate of Algorithm `(4.2.46)` has entered the local
  regime from Text 4.2.22;
* core/canonical: the tail predicate `HasQuadraticConvergenceFrom` on a fixed accelerated
  cubic-Newton orbit;
* bridge/view: the theorem sending entry of the given orbit into the local region at index `k` to
  `HasQuadraticConvergenceFrom method xStar k`.

Primitive data:
* the objective `f`, the minimizer `xStar`, and the Chapter 4 tail-convergence owner
  `HasQuadraticConvergenceFrom`;
* the source-facing local-region threshold `L₃(f) ‖x - xStar‖ ≤ σ₃(f)`, written in
  multiplication form so the degenerate case `L₃(f) = 0` does not force a division-based API;
* the accelerated orbit `method`, the entry index `k`, and the multiplicative constant `C` for
  the entry-time theorem.

Derived API:
* the local quadratic-convergence region;
* the iterate-entry predicate for the accelerated cubic-Newton orbit into that region;
* the bridge theorem from region entry to `HasQuadraticConvergenceFrom` for the same orbit;
* the explicit nonnegative entry-time bound, obtained by clamping the source logarithmic
  expression below by `0`, together with the corresponding region-entry estimate.

The previous version replaced the source-facing local region by a restart-style wrapper saying
that every accelerated cubic-Newton method restarted from `x` converges quadratically. That
changed the public semantics: Text 4.2.22 is about the same orbit of Algorithm `(4.2.46)` once
it enters the local neighborhood. This refinement therefore keeps the public region as the
displayed threshold set and makes `HasQuadraticConvergenceFrom method xStar k` the semantic owner
attached to entry of the given orbit at index `k`.
-/

/-- The local quadratic-convergence region from Text 4.2.22, written in multiplication form so
that the degenerate case `L₃(f) = 0` does not force a division-based surface. -/
def acceleratedCubicNewtonQuadraticConvergenceRegion
    (f : E → ℝ) [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    [HasUniformConvexityParameterOfDegree 3 f]
    (xStar : E) : Set E :=
  {x | L[3](f) * ‖x - xStar‖ ≤ σ[3](f)}

-- Proof sketch: unfold `acceleratedCubicNewtonQuadraticConvergenceRegion`.
/-- Membership in `acceleratedCubicNewtonQuadraticConvergenceRegion f xStar` is exactly the
displayed threshold inequality `L₃(f) ‖x - xStar‖ ≤ σ₃(f)`. -/
theorem mem_acceleratedCubicNewtonQuadraticConvergenceRegion_iff
    {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    [HasUniformConvexityParameterOfDegree 3 f]
    {xStar x : E} :
    x ∈ acceleratedCubicNewtonQuadraticConvergenceRegion f xStar ↔
      L[3](f) * ‖x - xStar‖ ≤ σ[3](f) :=
  Iff.rfl

end AcceleratedCubicNewtonQuadraticConvergenceRegion

section AcceleratedCubicNewtonQuadraticConvergenceEntryPredicate

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ}
  [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
  [HasUniformConvexityParameterOfDegree 3 f]
  {x0 : E}

/-- `InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k` means that the `k`th
iterate of the accelerated cubic-Newton orbit lies in the local quadratic-convergence region from
Text 4.2.22. -/
def InAcceleratedCubicNewtonQuadraticConvergenceRegion
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (k : ℕ) : Prop :=
  method k ∈ acceleratedCubicNewtonQuadraticConvergenceRegion f xStar

-- Proof sketch: unfold `InAcceleratedCubicNewtonQuadraticConvergenceRegion`.
/-- Expanding `InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k` says exactly
that the `k`th iterate satisfies the local threshold inequality
`L₃(f) ‖x_k - xStar‖ ≤ σ₃(f)`. -/
theorem inAcceleratedCubicNewtonQuadraticConvergenceRegion_iff
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (k : ℕ) :
    InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k ↔
      L[3](f) * ‖method k - xStar‖ ≤ σ[3](f) :=
  Iff.rfl

/-- Entry of the `k`th accelerated cubic-Newton iterate into the local region from Text 4.2.22
forces quadratic convergence of the same orbit from index `k`. -/
theorem hasQuadraticConvergenceFrom_of_inAcceleratedCubicNewtonQuadraticConvergenceRegion
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    {xStar : E} {k : ℕ}
    (hk : InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k) :
    HasQuadraticConvergenceFrom method xStar k := by
  sorry

-- Proof sketch: unfold the local-region inequality at `method k`.
/-- If the `k`th accelerated cubic-Newton iterate satisfies the threshold inequality
`L₃(f) ‖x_k - xStar‖ ≤ σ₃(f)`, then it lies in the local quadratic-convergence region from
Text 4.2.22. -/
theorem inAcceleratedCubicNewtonQuadraticConvergenceRegion_of_threshold
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    {xStar : E} {k : ℕ}
    (hk : L[3](f) * ‖method k - xStar‖ ≤ σ[3](f)) :
    InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k := by
  exact hk

end AcceleratedCubicNewtonQuadraticConvergenceEntryPredicate

section AcceleratedCubicNewtonQuadraticConvergenceEntry

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ}
  [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
  [HasUniformConvexityParameterOfDegree 2 f]
  [HasUniformConvexityParameterOfDegree 3 f]
  {x0 : E}

-- Proof sketch: first use the global complexity estimate for the accelerated cubic-Newton method
-- on functions in `𝓕₂₃` to find an iterate satisfying the threshold inequality
-- `L₃(f) ‖x_k - xStar‖ ≤ σ₃(f)`. Then apply
-- `inAcceleratedCubicNewtonQuadraticConvergenceRegion_of_threshold` and then
-- `hasQuadraticConvergenceFrom_of_inAcceleratedCubicNewtonQuadraticConvergenceRegion` to upgrade
-- that threshold bound to quadratic convergence of the same orbit from index `k`. On the public
-- theorem surface, the only conditioning owner is `[f ∈ 𝓕₂₃]`; the degree-two and degree-three
-- uniform-convexity parameters together with the degree-three Lipschitz constant are inherited
-- from that source-facing class. The absolute constant is quantified before the problem data in
-- the repo-standard `∃ C > 0, ∀ ...` shape, and the real-valued source logarithmic expression is
-- factored through the explicit nonnegative owner
-- `acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound`, obtained by clamping it below by
-- `0`.
/-- The entry-time bound from Text 4.2.22, written as an explicit nonnegative real number because
it bounds a natural iterate index. This is the source logarithmic expression clamped below by
`0`. -/
def acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (C : ℝ) : ℝ :=
  max 0
    (C *
      (Real.rpow (L[3](f) / σ[3](f)) (1 / 3 : ℝ) *
        Real.log ((L[3](f) / σ[2](f)) * ‖method 0 - xStar‖)))

/-- The entry-time bound from Text 4.2.22 is nonnegative by construction. -/
theorem acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound_nonneg
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (C : ℝ) :
    0 ≤ acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound method xStar C :=
  le_max_left 0
    (C *
      (Real.rpow (L[3](f) / σ[3](f)) (1 / 3 : ℝ) *
        Real.log ((L[3](f) / σ[2](f)) * ‖method 0 - xStar‖)))

/-- Text 4.2.22: there exists a positive absolute constant `C` such that for every
`f ∈ 𝓕₂₃`, every minimizer `xStar` of `f`, and every accelerated cubic-Newton method `(4.2.46)`
initialized at `x₀` with the canonical Hessian-Lipschitz constant `L₃(f)`, some iterate enters
the local quadratic-convergence region `L₃(f) ‖x - xStar‖ ≤ σ₃(f)`, and from that same index the
orbit itself converges quadratically to `xStar`. The entry time is bounded by the nonnegative owner
`acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound method xStar C`, i.e. by the source
logarithmic expression
`C * ((L₃(f) / σ₃(f))^(1/3) * log ((L₃(f) / σ₂(f)) * ‖x₀ - xStar‖))`
clamped below by `0`. -/
theorem acceleratedCubicNewton_enters_quadratic_convergence_region :
    ∃ C > 0,
      ∀ {f : E → ℝ} [f ∈ 𝓕₂₃] {x0 : E}
        (xStar : E)
        (_ : IsMinOn f Set.univ xStar)
        (method : AcceleratedCubicNewtonMethod f L[3](f) x0),
          ∃ k : ℕ,
            (k : ℝ) ≤ acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound method xStar C ∧
              InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k ∧
              HasQuadraticConvergenceFrom method xStar k := by
  sorry

end AcceleratedCubicNewtonQuadraticConvergenceEntry

/-! ### Text_4_2_23 (from Chap04) -/
noncomputable section

universe u

open scoped DegreeConditioning FunctionClasses

/- Text 4.2.23 lies in Chapter 4's degree-conditioning example domain.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`, the chapter owner for the source functions `d₂` and `d₃`
* `powerDistance_two_uniformConvexityParameter` and
  `powerDistance_three_uniformConvexityParameter` in `Text_4_2_7`
* `powerDistance_three_lipschitzConstant` in `Text_4_2_7`
* `IsInFunctionClassF23` in `Definition_4_2_17`, the chapter owner for `𝓕₂₃`

Source/core/bridge triage:
* source-facing: the example `ξ_{α,β}`
* core/canonical: `powerDistance`, `σ[p](f)`, `L[p](f)`, and `f ∈ 𝓕₂₃`
* bridge/view: the exact identities for `σ₂`, `σ₃`, and `L₃` of `ξ_{α,β}`

Primitive data:
* the positive coefficients `α` and `β`, carried canonically by `NNRealˣ`
* the chapter owners `powerDistance (2 : ℝ) (0 : E)` and `powerDistance (3 : ℝ) (0 : E)`

Derived API:
* the source-facing function `xi_alpha_beta`
* the exact conditioning identities `σ₂(ξ_{α,β}) = α`, `σ₃(ξ_{α,β}) = β / 2`,
  and `L₃(ξ_{α,β}) = 2β`
* the resulting membership `ξ_{α,β} ∈ 𝓕₂₃`

The previous refinement replaced the conditioning example by a lattice-distance periodicity model,
which erased the mathematical content of Text 4.2.23. This file returns to the chapter's
conditioning owners: `ξ_{α,β}` is built directly from the canonical `powerDistance` owners from
Text 4.2.7, and the public surface states the exact `σ₂`/`σ₃`/`L₃` identities together with the
`𝓕₂₃` consequence. -/

section Basic

variable (E : Type u) [NormedAddCommGroup E]

/-- The source-facing example
`ξ_{α,β} = α d₂ + β d₃`, with `d₂` and `d₃` realized by the chapter owner `powerDistance` at the
origin. The positive coefficients are carried by the project-standard owner `NNRealˣ`. -/
def xi_alpha_beta (α β : NNRealˣ) : E → ℝ :=
  (α : ℝ) • powerDistance (2 : ℝ) (0 : E) + (β : ℝ) • powerDistance (3 : ℝ) (0 : E)

/-- Expanding `xi_alpha_beta α β` at `x` gives the textbook formula
`α d₂(x) + β d₃(x)`. -/
@[simp] theorem xi_alpha_beta_apply (α β : NNRealˣ) (x : E) :
    xi_alpha_beta E α β x =
      (α : ℝ) * powerDistance (2 : ℝ) (0 : E) x +
        (β : ℝ) * powerDistance (3 : ℝ) (0 : E) x :=
  rfl

end Basic

section Conditioning

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

instance xi_alpha_beta_degreeTwo_uniform (α β : NNRealˣ) :
    HasUniformConvexityParameterOfDegree 2 (xi_alpha_beta E α β) := by
  sorry

instance xi_alpha_beta_degreeThree_uniform (α β : NNRealˣ) :
    HasUniformConvexityParameterOfDegree 3 (xi_alpha_beta E α β) := by
  sorry

instance xi_alpha_beta_degreeThree_lipschitz (α β : NNRealˣ) :
    HasIteratedFDerivLipschitzConstantOfDegree 3 (xi_alpha_beta E α β) := by
  sorry

instance xi_alpha_beta_memFunctionClassF23 (α β : NNRealˣ) :
    IsInFunctionClassF23 (xi_alpha_beta E α β) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Text 4.2.23: the degree-two conditioning parameter of `ξ_{α,β}` is exactly `α`. -/
theorem xi_alpha_beta_sigma_two (α β : NNRealˣ) :
    σ[2](xi_alpha_beta E α β) = (α : ℝ) := by
  sorry

/-- Text 4.2.23: the degree-three conditioning parameter of `ξ_{α,β}` is exactly `β / 2`. -/
theorem xi_alpha_beta_sigma_three (α β : NNRealˣ) :
    σ[3](xi_alpha_beta E α β) = (β : ℝ) / 2 := by
  sorry

/-- Text 4.2.23: the degree-three Lipschitz constant of `ξ_{α,β}` is exactly `2β`. -/
theorem xi_alpha_beta_L_three (α β : NNRealˣ) :
    L[3](xi_alpha_beta E α β) = 2 * (β : NNReal) := by
  sorry

/-- Text 4.2.23: the exact conditioning identities imply `ξ_{α,β} ∈ 𝓕₂₃`. -/
theorem xi_alpha_beta_mem_F23 (α β : NNRealˣ) :
    xi_alpha_beta E α β ∈ 𝓕₂₃ := by
  let _ : Nontrivial E := inferInstance
  infer_instance

/-- Text 4.2.23: the source-facing function `ξ_{α,β}` has the exact conditioning data
`σ₂(ξ_{α,β}) = α`, `σ₃(ξ_{α,β}) = β / 2`, and `L₃(ξ_{α,β}) = 2β`; in particular,
`ξ_{α,β} ∈ 𝓕₂₃`. -/
theorem xi_alpha_beta_conditioning (α β : NNRealˣ) :
    σ[2](xi_alpha_beta E α β) = (α : ℝ) ∧
      σ[3](xi_alpha_beta E α β) = (β : ℝ) / 2 ∧
      L[3](xi_alpha_beta E α β) = 2 * (β : NNReal) ∧
      xi_alpha_beta E α β ∈ 𝓕₂₃ := by
  exact ⟨xi_alpha_beta_sigma_two α β, xi_alpha_beta_sigma_three α β, xi_alpha_beta_L_three α β,
    xi_alpha_beta_mem_F23 α β⟩

end Conditioning

/-! ### Text_4_2_24 (from Chap04) -/
open scoped Gradient DegreeConditioning FunctionClasses

noncomputable section

universe u

/- Text 4.2.24 lies in the Chapter 4 Newton / quadratic-entry domain.

Sampled owner declarations:
* `HasEventuallySuperlinearErrorBound` in `Chap01/Definition_1_2_7`, the Chapter 1 owner for
  the quadratic scalar error recursion;
* `quadraticGradientRegion` in `Text_4_2_12`, the nearby Newton threshold-region owner;
* `strongConvexAcceleratedCubicNewtonQuadraticRegion` in `Text_4_2_13`, the chapter pattern
  "region set + entry predicate + first-entry index";
* `acceleratedCubicNewtonQuadraticConvergenceRegion` and
  `InAcceleratedCubicNewtonQuadraticConvergenceRegion` in `Text_4_2_22`, the closest sibling
  declarations in the same local quadratic-entry domain;
* `HasIteratedFDerivLipschitzConstantOfDegree.contDiff` in `Definition_4_2_11`, the owner-level
  bridge from degree-three derivative Lipschitz control to the redundant `ContDiff ℝ 2 f`
  regularity that should stay derived rather than primitive here;
* `StrongConvexOn.eq_of_isMinOn` in `Chap03/Corollary_3_2_3`, the chapter owner for minimizer
  uniqueness once the `𝓕₂Lip` degree-two uniform-convexity data has been converted into
  strong convexity;
* `NewtonSystem.Method` in `Algorithm_1_7_1`, the orbit owner for Newton iterates.

Best owner abstraction:
* source-facing: the intrinsic Newton quadratic-convergence neighborhood around `xStar`, the raw
  threshold region used by the entry estimate, the direct tail property
  `HasQuadraticConvergenceFrom`, and the explicit entry-time estimate;
* core/canonical: the Newton orbit `NewtonSystem.Method (∇ f) x0`;
* bridge/view: the Chapter 1 scalar error owner `HasEventuallySuperlinearErrorBound`, and the
  bridge from a sufficiently small threshold inequality to quadratic convergence of the same
  Newton orbit.

Primitive data:
* an orbit `x` for the tail predicate, and the initial point `x0` for the explicit entry-time
  bound;
* the limit point `xStar`;
* the source-facing threshold parameter `σ₃`;
* the degree-two and degree-three conditioning constants `σ[2](f)`, `L[2](f)`, and `L[3](f)`.

Derived API:
* `HasQuadraticConvergenceFrom`, built from trajectory convergence plus the Chapter 1 scalar error
  owner;
* the fixed local neighborhood `newtonQuadraticConvergenceRegion`, written in multiplication form
  as `4 L₂(f) L₃(f) ‖x - xStar‖ ≤ σ₂(f)^2`;
* the raw threshold neighborhood `newtonThresholdRegion`, written in multiplication form to avoid
  the division-based surface `σ₃ / L₃(f)`;
* the bridge theorem sending entry into a sufficiently small threshold neighborhood to entry into
  `newtonQuadraticConvergenceRegion`, and hence to quadratic convergence of the same orbit from
  that iterate onward;
* the explicit nonnegative entry-time bound and the corresponding entry estimate;
* the induced tail-convergence theorem extracted from the entry estimate once the threshold is
  known to lie inside the fixed quadratic neighborhood.

The previous version duplicated the Chapter 1 quadratic-recurrence owner inside
`HasQuadraticConvergenceFrom`, and treated the raw threshold inequality
`L₃(f) ‖x - xStar‖ ≤ σ₃` as if it were itself the quadratic-convergence region for every `σ₃`.
This refinement keeps the canonical tail predicate `HasQuadraticConvergenceFrom` directly for
actual Newton orbits, splits the intrinsic quadratic neighborhood from the auxiliary threshold
region used by the entry estimate, and only upgrades threshold entry to quadratic convergence when
the threshold is small enough to lie inside the fixed neighborhood. The quadratic tail property is
expressed through the canonical scalar error owner `HasEventuallySuperlinearErrorBound`, the `C²`
regularity remains derived from the degree-three Lipschitz owner, minimizer uniqueness stays at
the strong-convexity owner layer instead of a local duplicate wrapper, and the entry-time bound is
exposed at the initial-data layer as an explicit nonnegative scalar owner obtained by clamping the
source logarithmic expression below by `0`. -/

section QuadraticConvergence

variable {E : Type u} [SeminormedAddCommGroup E]

variable {x : ℕ → E} {xStar : E}

/-- A Newton orbit has quadratic convergence to `xStar` from index `k` if it converges to
`xStar` and its error sequence satisfies the Chapter 1 quadratic scalar recurrence from that index
onward. -/
def HasQuadraticConvergenceFrom (x : ℕ → E) (xStar : E) (k : ℕ) : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      Filter.Tendsto x Filter.atTop (nhds xStar) ∧
        HasEventuallySuperlinearErrorBound (fun j ↦ ‖x j - xStar‖) 0 c k

end QuadraticConvergence

section NewtonMethodTail

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace NewtonSystem.Method

/-- If the tail of a Newton method converges quadratically from its initial index, then the
original Newton method converges quadratically from the corresponding shifted index. -/
theorem hasQuadraticConvergenceFrom_of_tail
    {F : E → E} {x0 xStar : E} (method : NewtonSystem.Method F x0) {k : ℕ}
    (h : HasQuadraticConvergenceFrom (method.tail k) xStar 0) :
    HasQuadraticConvergenceFrom method xStar k := by
  rcases h with ⟨c, hc, htendsto, hbound⟩
  refine ⟨c, hc, ?_, Nat.zero_le k, ?_⟩
  · simpa using (Filter.tendsto_add_atTop_iff_nat k).1 htendsto
  · intro j hj
    rcases Nat.exists_eq_add_of_le hj with ⟨n, rfl⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.sub_zero] using
      hbound.bound (Nat.zero_le n)

end NewtonSystem.Method

end NewtonMethodTail

section NewtonQuadraticConvergenceRegion

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip]

/-- The intrinsic Newton quadratic-convergence neighborhood around `xStar`. It is written in
multiplication form as `4 L₂(f) L₃(f) ‖x - xStar‖ ≤ σ₂(f)^2`, so no division-based surface is
forced. This is the fixed local neighborhood whose membership is bridged to
`HasQuadraticConvergenceFrom` below. -/
def newtonQuadraticConvergenceRegion
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (xStar : E) : Set E :=
  {x | 4 * L[2](f) * L[3](f) * ‖x - xStar‖ ≤ σ[2](f) ^ (2 : ℕ)}

-- Proof sketch: unfold `newtonQuadraticConvergenceRegion`.
/-- Membership in `newtonQuadraticConvergenceRegion f xStar` is exactly the displayed
local inequality `4 L₂(f) L₃(f) ‖x - xStar‖ ≤ σ₂(f)^2`. -/
theorem mem_newtonQuadraticConvergenceRegion_iff
    {f : E → ℝ} [f ∈ 𝓕₂Lip] {xStar x : E} :
    x ∈ newtonQuadraticConvergenceRegion f xStar ↔
      4 * L[2](f) * L[3](f) * ‖x - xStar‖ ≤ σ[2](f) ^ (2 : ℕ) :=
  Iff.rfl

end NewtonQuadraticConvergenceRegion

section NewtonThresholdRegion

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f]

/-- The raw threshold neighborhood `L₃(f) ‖x - xStar‖ ≤ σ₃` appearing in Text 4.2.24, written in
multiplication form so that the degenerate case `L₃(f) = 0` does not force a division-based
surface. This is the source-facing threshold region used in the entry estimate. -/
def newtonThresholdRegion
    (f : E → ℝ) [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    (xStar : E) (σ₃ : ℝ) : Set E :=
  {x | L[3](f) * ‖x - xStar‖ ≤ σ₃}

-- Proof sketch: unfold `newtonThresholdRegion`.
/-- Membership in `newtonThresholdRegion f xStar σ₃` is exactly the displayed threshold inequality
`L₃(f) ‖x - xStar‖ ≤ σ₃`. -/
theorem mem_newtonThresholdRegion_iff
    {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    {xStar x : E} {σ₃ : ℝ} :
    x ∈ newtonThresholdRegion f xStar σ₃ ↔
      L[3](f) * ‖x - xStar‖ ≤ σ₃ :=
  Iff.rfl

end NewtonThresholdRegion

section NewtonQuadraticConvergenceRegionBridge

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 : E}
variable {xStar : E} {σ₃ : ℝ}

-- Proof sketch: prove the local Newton-region theorem at index `0` for a Newton orbit started in
-- `newtonQuadraticConvergenceRegion f xStar` from the chapter `𝓕₂Lip` data and the minimizer
-- hypothesis on `xStar`, then apply it to the tail `method.tail k` and transfer the estimate back
-- to the original orbit via `NewtonSystem.Method.hasQuadraticConvergenceFrom_of_tail`.
/-- If `f ∈ 𝓕₂Lip`, `xStar` minimizes `f`, and the `k`th Newton iterate lies in the intrinsic
quadratic-convergence region `newtonQuadraticConvergenceRegion f xStar`, then the same Newton
orbit converges quadratically to `xStar` from index `k` onward. -/
theorem hasQuadraticConvergenceFrom_of_mem_newtonQuadraticConvergenceRegion
    (_ : IsMinOn f Set.univ xStar)
    (method : NewtonSystem.Method (∇ f) x0)
    {k : ℕ}
    (hk : method k ∈ newtonQuadraticConvergenceRegion f xStar) :
    HasQuadraticConvergenceFrom method xStar k := by
  sorry

-- Proof sketch: unfold the threshold-region and intrinsic-region inequalities, multiply the
-- threshold inequality by `4 L₂(f)`, and use the smallness hypothesis
-- `4 L₂(f) σ₃ ≤ σ₂(f)^2`.
section

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If the threshold parameter `σ₃` is small enough that
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, then membership in `newtonThresholdRegion f xStar σ₃` forces membership in
the intrinsic Newton quadratic-convergence region `newtonQuadraticConvergenceRegion f xStar`. -/
theorem mem_newtonQuadraticConvergenceRegion_of_mem_newtonThresholdRegion
    {x : E}
    (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ))
    (hx : x ∈ newtonThresholdRegion f xStar σ₃) :
    x ∈ newtonQuadraticConvergenceRegion f xStar := by
  have hmul :
      (4 * L[2](f)) * (L[3](f) * ‖x - xStar‖) ≤ (4 * L[2](f)) * σ₃ := by
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  change 4 * L[2](f) * L[3](f) * ‖x - xStar‖ ≤ σ[2](f) ^ (2 : ℕ)
  simpa [mul_assoc] using hmul.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hσ₃)

end

/-- If `f ∈ 𝓕₂Lip`, `xStar` minimizes `f`, the threshold parameter `σ₃` satisfies
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, and the `k`th Newton iterate lies in the threshold region
`newtonThresholdRegion f xStar σ₃`, then the same Newton orbit converges quadratically to `xStar`
from index `k` onward. -/
theorem hasQuadraticConvergenceFrom_of_mem_newtonThresholdRegion
    (hxStar : IsMinOn f Set.univ xStar)
    (method : NewtonSystem.Method (∇ f) x0)
    {k : ℕ}
    (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ))
    (hk : method k ∈ newtonThresholdRegion f xStar σ₃) :
    HasQuadraticConvergenceFrom method xStar k := by
  exact hasQuadraticConvergenceFrom_of_mem_newtonQuadraticConvergenceRegion hxStar method
    (mem_newtonQuadraticConvergenceRegion_of_mem_newtonThresholdRegion hσ₃ hk)

/-- If `f ∈ 𝓕₂Lip`, `xStar` minimizes `f`, the threshold parameter `σ₃` satisfies
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, and the `k`th Newton iterate satisfies the threshold inequality
`L₃(f) ‖x_k - xStar‖ ≤ σ₃`, then the actual Newton orbit converges quadratically to `xStar` from
that iterate onward. -/
theorem hasQuadraticConvergenceFrom_of_threshold
    (hxStar : IsMinOn f Set.univ xStar)
    (method : NewtonSystem.Method (∇ f) x0)
    {k : ℕ}
    (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ))
    (hk : L[3](f) * ‖method k - xStar‖ ≤ σ₃) :
    HasQuadraticConvergenceFrom method xStar k := by
  exact hasQuadraticConvergenceFrom_of_mem_newtonThresholdRegion hxStar method hσ₃
    (show method k ∈ newtonThresholdRegion f xStar σ₃ from hk)

end NewtonQuadraticConvergenceRegionBridge

section NewtonQuadraticConvergenceEntryBound

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} [f ∈ 𝓕₂Lip]

/-- The entry-time bound from Text 4.2.24, written as an explicit nonnegative real number because
it bounds a natural iterate index. It depends only on the initial point `x0`, the target point
`xStar`, the threshold `σ₃`, and the conditioning data of `f`. This is the source logarithmic
expression clamped below by `0`. -/
def newtonQuadraticConvergenceEntryBound
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (x0 xStar : E) (σ₃ C : ℝ) : ℝ :=
  max 0
    (C *
      (Real.sqrt (L[2](f) / σ[2](f)) *
        Real.log (L[2](f) * L[3](f) ^ (2 : ℕ) / σ₃ ^ (2 : ℕ)) *
        ‖x0 - xStar‖ ^ (2 : ℕ)))

/-- The entry-time bound from Text 4.2.24 is nonnegative by construction. -/
theorem newtonQuadraticConvergenceEntryBound_nonneg
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (x0 xStar : E) (σ₃ C : ℝ) :
    0 ≤ newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C :=
  le_max_left 0
    (C *
      (Real.sqrt (L[2](f) / σ[2](f)) *
        Real.log (L[2](f) * L[3](f) ^ (2 : ℕ) / σ₃ ^ (2 : ℕ)) *
        ‖x0 - xStar‖ ^ (2 : ℕ))
    )

end NewtonQuadraticConvergenceEntryBound

section NewtonQuadraticConvergenceEntry

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip]
variable {x0 : E}

-- Proof sketch: combine the `𝓕₂^{Lip}` regularity data `σ₂(f)`, `L₂(f)`, and `L₃(f)` with the
-- global Newton complexity estimate to obtain an iterate satisfying the threshold inequality
-- `L₃(f) ‖x_k - xStar‖ ≤ σ₃`, then convert that estimate to actual membership of `method k` in
-- `newtonThresholdRegion f xStar σ₃`. Because the displayed real expression upper-bounds a
-- natural-number iterate index, the statement factors it through the explicit nonnegative owner
-- `newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C`, defined at the initial-data layer by
-- clamping the source logarithmic expression below by `0`.
/-- Text 4.2.24, entry-threshold form: let `f ∈ 𝓕₂^{Lip}`, let `xStar` be a minimizer of `f`
(hence automatically the unique minimizer, since the degree-two uniform-convexity owner behind
`f ∈ 𝓕₂Lip` yields positive strong convexity and then `StrongConvexOn.eq_of_isMinOn`), and let
`x` be the Newton orbit
`x_{k+1} = x_k - [∇² f(x_k)]⁻¹ ∇ f(x_k)`. Then for every threshold `σ₃ > 0`, some iterate enters
the threshold region `L₃(f) ‖x - xStar‖ ≤ σ₃`. The entry time is at most
`newtonQuadraticConvergenceEntryBound f x₀ xStar σ₃ C = max 0
  (C * (sqrt (L₂(f) / σ₂(f)) * log (L₂(f) * L₃(f)^2 / σ₃^2) * ‖x₀ - xStar‖^2))`
steps for some positive absolute constant `C`. -/
theorem newton_enters_threshold_region_of_f2Lip
    : ∃ C > 0,
        ∀ {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 : E}
          (xStar : E)
          (_ : IsMinOn f Set.univ xStar)
          (method : NewtonSystem.Method (∇ f) x0)
          {σ₃ : ℝ} (_ : 0 < σ₃),
            ∃ k : ℕ,
              (k : ℝ) ≤ newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C ∧
                method k ∈ newtonThresholdRegion f xStar σ₃ := by
  sorry

-- Proof sketch: combine `newton_enters_threshold_region_of_f2Lip` with the bridge
-- `hasQuadraticConvergenceFrom_of_mem_newtonThresholdRegion`. The extra smallness hypothesis
-- `4 L₂(f) σ₃ ≤ σ₂(f)^2` ensures that the raw threshold region lies inside the intrinsic local
-- quadratic-convergence neighborhood.
/-- Text 4.2.24, quadratic-regime form: if the entry threshold `σ₃` is small enough that
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, then the same entry estimate forces an iterate of the Newton orbit into
the intrinsic quadratic-convergence region `newtonQuadraticConvergenceRegion f xStar`, and from
that iterate onward Newton's method converges quadratically to `xStar`. -/
theorem newton_enters_quadratic_convergence_region_of_f2Lip
    : ∃ C > 0,
        ∀ {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 : E}
          (xStar : E)
          (hxStar : IsMinOn f Set.univ xStar)
          (method : NewtonSystem.Method (∇ f) x0)
          {σ₃ : ℝ} (_ : 0 < σ₃)
          (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ)),
            ∃ k : ℕ,
              (k : ℝ) ≤ newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C ∧
                method k ∈ newtonQuadraticConvergenceRegion f xStar ∧
                HasQuadraticConvergenceFrom method xStar k := by
  sorry

end NewtonQuadraticConvergenceEntry
