import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 5.17 is a `bridge/view` item: it compares the source-facing strong-convexity owner
`is_strongly_convex_function` from Definition 5.16 with the source-facing convexity owner
`is_convex_function` from Definition 2.6, using Definition 2.7's segment formulation after
subtracting the quadratic function `x ↦ (σ / 2) ‖x‖²`. The Euclidean-space hypothesis is
formalized by `InnerProductSpace ℝ E`, which is exactly the structure needed for the quadratic
norm identity underlying this equivalence. -/

-- Proof sketch: rewrite convexity of the shifted function by its segment inequality, expand the
-- shifted function along a segment, and use the inner-product identity
-- `‖t • x + (1 - t) • y‖² - t * ‖x‖² - (1 - t) * ‖y‖² = -t * (1 - t) * ‖x - y‖²` to convert the
-- convexity inequality into the defining segment inequality from `is_strongly_convex_function`.
/-- Theorem 5.17: on a Euclidean space, for `σ > 0`, an extended-real-valued function is
`σ`-strongly convex if and only if subtracting `(σ / 2) ‖x‖²` yields a convex
extended-real-valued function. -/
theorem is_strongly_convex_function_iff_sub_half_sigma_norm_sq_is_convex
    (f : E → EReal) (σ : ℝ) :
    is_strongly_convex_function f σ ↔
      is_convex_function
        (fun x ↦ f x - ((((σ / 2) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) := sorry

end
