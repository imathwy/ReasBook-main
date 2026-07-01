import FirstOrderMethodsinOptimization.Chap02.Definition_2_1
import FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsinOptimization.Chap03.Definition_3_2
import FirstOrderMethodsinOptimization.Chap03.Definition_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.6 is a `source-facing` existence statement in the chapter convex-analysis API.
Its owner notions are already provided earlier in the project by `effective_domain`,
`is_convex_function`, `subdifferential`, and `intrinsicInterior ℝ`, so this file reuses those
declarations directly rather than restating local copies. The relative-interior hypothesis already
forces `effective_domain f` to be nonempty, and for a convex extended-real-valued function any
occurrence of `⊥` is either absent on the effective domain or makes every dual vector a
subgradient there. Thus the theorem needs only the owner convexity and relative-interior
hypotheses. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall intrinsicInterior

-- Proof sketch: translate the textbook relative-interior hypothesis on `effective_domain f` into
-- the finite-dimensional supporting-hyperplane setup for the epigraph of `f`. A supporting
-- functional at `(x, f x)` has positive vertical coefficient, and normalizing it yields a linear
-- functional satisfying the subgradient inequality at `x`. If `f` takes the value `⊥` somewhere
-- on the effective domain, convexity forces the same at every relative-interior point, and then
-- the subgradient inequality is automatic for every dual vector.
/-- Theorem 3.6: if `f` is convex and `x` lies in the relative interior of `dom(f)`, then the
subdifferential `∂ f(x)` is nonempty. -/
theorem subdifferential_nonempty_at_relativeInterior_point
    (f : E → EReal) (x : E) (hconv : is_convex_function f)
    (hx : x ∈ intrinsicInterior ℝ (effective_domain f)) :
    (subdifferential f x).Nonempty := sorry

end
