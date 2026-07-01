import FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsinOptimization.Chap03.Definition_3_8
import FirstOrderMethodsinOptimization.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → EReal) (x d : E)

/- Theorem 3.8 is `source-facing` in the chapter directional-derivative API. Its owner notion is
`has_directional_derivative_at` from Definition 3.8. The canonical totalized owner
`directional_derivative` already comes with the bridge
`directional_derivative_eq_of_has_directional_derivative_at`, so this file keeps only the
textbook existence statement instead of a parallel owner-level wrapper theorem. For this local
existence result, the chapter's canonical finite-valued owner-side hypothesis is
`x ∈ interior (finite_domain f)`, not a stronger global no-`⊥` guard. -/
recall is_convex_function
recall has_directional_derivative_at
recall finite_domain

-- Proof sketch: restrict `f` to the affine line `t ↦ x + t • d`, obtaining a convex
-- extended-real-valued function on `ℝ`. Since `x` lies in the interior of `finite_domain f`,
-- this one-dimensional restriction is finite on some interval around `0`, so its secant slopes on
-- `(0, r]` are monotone and bounded. Their right limit at `0` therefore exists and is finite,
-- giving the desired directional derivative.
/-- Theorem 3.8: if `f` is a convex extended-real-valued function and `x` lies in the interior of
its finite domain, then for every direction `d` there is a finite real number that is the
directional derivative of `f` at `x` along `d`. -/
theorem exists_real_has_directional_derivative_at_of_convex_interior_point
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    ∃ ℓ : ℝ, has_directional_derivative_at f x d (ℓ : EReal) := sorry

end
