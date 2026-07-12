import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SelfConcordantAuxiliaryFunction

noncomputable section

/- Lemma 5.1.5 lies in the Chapter 5 self-concordant auxiliary-function domain.

Sampled owner-style declarations:
* `selfConcordantOmega` and the scoped notation `ω` from `Definition_5_0_21`, the chapter owner
  for the auxiliary function `t ↦ t - log (1 + t)`;
* `selfConcordantOmegaStar` and the scoped notation `ω_*` from `Definition_5_0_21`, the chapter
  owner for the auxiliary function `t ↦ -t - log (1 - t)`;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  scaled-argument bridge constructors used elsewhere in Chapter 5 but not as the main scalar
  surface here;
* `selfConcordantOmega_apply` and `selfConcordantOmegaStar_apply`, the canonical owner-level
  evaluation lemmas recovering the textbook scalar formulas;
* `Real.log_le_sub_one_of_pos` in mathlib, the standard logarithmic comparison theorem underlying
  the elementary rational sandwich estimates.

Source/core/bridge triage:
* source-facing: the textbook rational lower and upper bounds for `ω` on `[0, ∞)` and for `ω_*`
  on `[0, 1)`;
* core/canonical: the Chapter 5 owners `ω` and `ω_*`;
* bridge/view: the subtype constructors `selfConcordantOmegaArg`,
  `selfConcordantOmegaStarArg`, and the subtype-level evaluation lemmas
  `selfConcordantOmega_apply`, `selfConcordantOmegaStar_apply`.

Primitive data:
* a real parameter `t` in the textbook domain (`0 ≤ t`, or `0 ≤ t < 1` for `ω_*`).

Derived API:
* the rational comparison statements, now stated directly against the canonical owners `ω` and
  `ω_*`, with the raw logarithmic formulas recovered by the existing evaluation lemmas.

This refinement keeps the source-facing inequalities unchanged while removing the duplicate raw
formula surface from the main declarations. -/

-- Proof sketch: use the elementary denominator comparison
-- `1 + (2 / 3) t ≤ 1 + t` for `t ≥ 0`, then divide the common numerator `t^2` by the
-- corresponding positive denominators.
/-- The simpler lower rational approximation with denominator `1 + t` is bounded above by the
intermediate lower bound with denominator `1 + (2 / 3) t`. -/
theorem selfConcordantOmega_simpleLowerBound_le_intermediate
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / (2 * (1 + t)) ≤
      t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) := sorry

-- Proof sketch: compare `ω' (t) = t / (1 + t)` with the derivatives of
-- `t ↦ t^2 / (2 * (1 + (2 / 3) * t))` and `t ↦ t^2 / (2 + t)` on `[0, ∞)`, use that all three
-- functions vanish at `t = 0`, and integrate the derivative inequalities.
/-- Lemma 5.1.5: for `t ≥ 0`, the self-concordant auxiliary function
`ω(t)` lies between the rational bounds
`t² / (2 * (1 + (2 / 3) t))` and `t² / (2 + t)`. -/
theorem selfConcordantOmega_bounds
    {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      have h : -1 < ((1 : NNReal) : ℝ) * t := neg_one_lt_mf_mul_of_nonneg ht
      simpa using h)
    t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) ≤ ω tω ∧
      ω tω ≤ t ^ 2 / (2 + t) := sorry

-- Proof sketch: compare `ω'_* (t) = t / (1 - t)` with the derivatives of
-- `t ↦ t^2 / (2 - t)` and `t ↦ t^2 / (2 * (1 - t))` on `[0, 1)`, note that all three functions
-- vanish at `t = 0`, and integrate the derivative inequalities along the interval.
/-- For `t ∈ [0, 1)`, the auxiliary function `ω_*(t)` is squeezed between
`t² / (2 - t)` and `t² / (2 * (1 - t))`. -/
theorem selfConcordantOmegaStar_bounds
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    τ ^ 2 / (2 - τ) ≤ ω_* τω ∧
      ω_* τω ≤ τ ^ 2 / (2 * (1 - τ)) := sorry

end
