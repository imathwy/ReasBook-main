import FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsinOptimization.Chap04.Definition_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.2 is `source-facing` in the chapter conjugacy API. The `core/canonical` owners are
Chapter 2's `is_convex_function` together with Mathlib's `LowerSemicontinuous` and Definition 4.2's
`biconjugate_function` (built on Definition 4.1's `conjugate_function`). This file therefore keeps
only the source-facing biconjugation theorem and reuses those owner abstractions directly. -/
recall is_convex_function
recall biconjugate_function

-- Proof sketch: combine the earlier inequality `f** ≤ f` with strict separation of the epigraph
-- of a closed convex function from any point below it. The separating functional produces a
-- dual vector contradicting Fenchel's inequality unless `f x ≤ f** x`, so pointwise equality
-- follows.
/-- Theorem 4.2: a closed convex extended-real-valued function on a finite-dimensional real normed
space coincides with its biconjugate. Here closedness is expressed by `LowerSemicontinuous` and
convexity by `is_convex_function`. -/
theorem biconjugate_function_eq_self_of_closed_convex
    (f : E → EReal) (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f) :
    biconjugate_function f = f := sorry

end
