import FirstOrderMethodsinOptimization.Chap02.Definition_2_1
import FirstOrderMethodsinOptimization.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: the convexity hypothesis makes the effective domain an interval in `ℝ`, hence its
-- interior is again an interval where the finite-valued restriction of `f` is a real-valued convex
-- function and therefore continuous. At an endpoint of the effective domain, use the one-sided
-- monotonicity of secant slopes for convex functions to show that the one-sided limit exists, then
-- combine this with lower semicontinuity to identify that limit with the endpoint value.
/-- Theorem 2.10: a proper closed and convex extended-real-valued function on `ℝ` is continuous on
its effective domain. Here closedness is expressed by `LowerSemicontinuous`, convexity by the
chapter owner predicate `is_convex_function`, and the codomain restriction `(-∞, ∞]` by the
assumption that `f` never takes the value `⊥`. -/
theorem continuousOn_effective_domain_of_lowerSemicontinuous_convex_univariate
    {f : ℝ → EReal} (h_ne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) :
    ContinuousOn f (effective_domain f) := sorry
