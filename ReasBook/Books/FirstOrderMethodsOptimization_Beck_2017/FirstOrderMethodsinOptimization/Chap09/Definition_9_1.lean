import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.1 is recall-only in Chapter 9. Its `source-facing` content is the standing
assumption package for the constrained convex problem `(P)`, and the exact `core/canonical` owner
already exists as `IsConstrainedConvexProblem`; there is no new mathematics here that would
justify a second wrapper or alias. -/

/- Definition 9.1: the standing assumptions (A)-(D) for
`(P) := min {f(x) : x ∈ C}` are the existing owner class `IsConstrainedConvexProblem`, which
packages that `f : E → (-∞, ∞]` is proper, closed, and convex, that `C` is nonempty, closed,
convex, and contained in `interior (dom(f))`, and that the optimal set `X^*` is nonempty with
optimal value `f_opt`. -/
recall IsConstrainedConvexProblem
