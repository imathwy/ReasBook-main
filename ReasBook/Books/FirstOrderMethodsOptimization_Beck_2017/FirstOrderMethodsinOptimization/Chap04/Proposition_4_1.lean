import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 4.1 is `source-facing`. Its owner abstractions already exist upstream:
`extendedIndicator` in Chapter 2, `support_function` in Chapter 2, and `conjugate_function` in
Definition 4.1. This file therefore keeps only the indicator-conjugate identity itself. -/

-- Proof sketch: unfold `conjugate_function`, `extendedIndicator`, and `support_function`. If
-- `x ∈ C`, then `(extendedIndicator C) x = 0`, so the conjugate integrand is `y x`; if `x ∉ C`,
-- then `(extendedIndicator C) x = ⊤`, so the integrand is `⊥`. Thus the supremum over all `x`
-- reduces to the supremum over `C`.
/-- The pointwise indicator-conjugate identity: the Fenchel conjugate of `δ_C` at `y` is the
support function `σ_C (y)`. -/
theorem conjugate_function_extendedIndicator_apply_eq_support_function (C : Set E)
    (y : Module.Dual ℝ E) :
    conjugate_function (extendedIndicator C) y = support_function C y := sorry

-- Proof sketch: use extensionality on the dual variable and apply
-- `conjugate_function_extendedIndicator_apply_eq_support_function` pointwise.
/-- Proposition 4.1: equations (4.2) and (4.3) identify the Fenchel conjugate of the indicator
function `δ_C` with the support function `σ_C`. The textbook assumes `C` is nonempty, but this
equality remains valid for `C = ∅` because both sides are then constantly `⊥`. -/
theorem conjugate_function_extendedIndicator_eq_support_function (C : Set E) :
    conjugate_function (extendedIndicator C) = support_function C := sorry

end
