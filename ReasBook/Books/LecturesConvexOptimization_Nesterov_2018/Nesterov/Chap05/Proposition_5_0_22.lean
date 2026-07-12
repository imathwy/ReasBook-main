import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SelfConcordantAuxiliaryFunction

noncomputable section

/-
Proposition 5.0.22 lies in the Chapter 5 one-variable convexity / auxiliary-function domain.

Sampled owner-style declarations:
* `selfConcordantOmega` and `selfConcordantOmegaStar` in `Definition_5_0_21`, the chapter owners
  for `ω` and `ω_*`;
* `selfConcordantOmega_apply` and `selfConcordantOmegaStar_apply`, the canonical owner-level
  evaluation lemmas recovering the textbook scalar formulas from those owners;
* `convexOn_of_deriv2_nonneg` in mathlib, the standard one-variable convexity owner for proving
  interval convexity from nonnegative second derivative;
* `convex_Ioi` and `convex_Iio`, the canonical interval-convexity owners for the two domains.

Source/core/bridge triage:
* source-facing: the convexity of the Chapter 5 auxiliary functions on their natural intervals;
* core/canonical: the chapter owners `ω` and `ω_*` together with mathlib's `ConvexOn`;
* bridge/view: the canonical ambient real-valued extensions
  `Function.extend Subtype.val ω 0` and `Function.extend Subtype.val ω_* 0`, used only because
  `ConvexOn` is stated for total functions on `ℝ`.

Primitive data:
* the source-facing owners `ω : Set.Ioi (-1) → ℝ` and `ω_* : Set.Iio 1 → ℝ`.

Derived API:
* their canonical ambient extensions via `Function.extend Subtype.val ... 0`, which agree with
  the owners on the relevant convex domains and are mathematically irrelevant off those domains.

This refinement removes the duplicate raw-formula surface from the proposition statements and
reuses the chapter owners directly. -/

-- Proof sketch: compute the second derivatives of the two scalar functions,
-- `ω''(t) = (1 + t)⁻²` on `(-1, ∞)` and `ω_*''(τ) = (1 - τ)⁻²` on `(-∞, 1)`,
-- and apply the standard one-variable criterion that nonnegative second derivative
-- on a convex interval implies convexity.
/-- Proposition 5.0.22 (1): the ambient real-function view of the Chapter 5 owner `ω` is convex
on `(-1, ∞)`. -/
theorem selfConcordantOmega_convexOn :
    ConvexOn ℝ (Set.Ioi (-1 : ℝ))
      (Function.extend Subtype.val ω 0) := by
  sorry

/-- Proposition 5.0.22 (2): the ambient real-function view of the Chapter 5 owner `ω_*` is convex
on `(-∞, 1)`. -/
theorem selfConcordantOmegaStar_convexOn :
    ConvexOn ℝ (Set.Iio (1 : ℝ))
      (Function.extend Subtype.val ω_* 0) := by
  sorry

end
