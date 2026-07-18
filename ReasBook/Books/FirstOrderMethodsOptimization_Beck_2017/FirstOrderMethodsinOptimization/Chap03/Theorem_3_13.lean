import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDual)
open scoped Gradient

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.13 is a `bridge/view` item in the chapter convex-analysis API. The source-facing
owners remain `effective_domain`, `finite_domain`, `is_convex_function`, and the extended-real
differentiability predicate `is_differentiable_at` from Definition 3.10, while the singleton
conclusion naturally lives on the continuous-dual bridge `strongDualSubdifferential`, because
`toDual` lands in `StrongDual ℝ E`. Here differentiability already supplies the interior
finite-domain hypothesis, and for a convex extended-real-valued function that interior finite point
forces the global no-`⊥` property needed by the directional-derivative owner theorem, so that
codomain restriction is derived API rather than primitive public data. -/
recall effective_domain
recall finite_domain
recall is_convex_function
recall is_differentiable_at
recall strongDualSubdifferential

-- Proof sketch: unpack `hdiff` as `x ∈ interior (finite_domain f)` plus differentiability of
-- `y ↦ (f y).toReal` at `x`. For a convex extended-real-valued function, that interior finite point
-- rules out `⊥` globally, so the owner max formula for directional derivatives applies without a
-- primitive public `h_ne_bot` hypothesis. It identifies the directional derivative with the
-- pairing against the gradient. For any `g ∈ strongDualSubdifferential f x`, the max formula bounds
-- `g d` by that directional derivative for every direction `d`, and applying this to both `d` and
-- `-d` forces `g` to coincide with the dual vector represented by
-- `∇ (fun y ↦ (f y).toReal) x`. Nonemptiness of the extendedRealSubdifferential at the interior finite point
-- then gives the stated singleton equality.
/-- Theorem 3.13 (1): if a convex extended-real-valued function is differentiable at a point in the
chapter sense `is_differentiable_at`, then its continuous-dual extendedRealSubdifferential there is the
singleton consisting of the dual vector represented by the gradient. -/
theorem subdifferential_eq_singleton_gradient_of_differentiableAt
    (f : E → EReal) (x : E) (hconvex : is_convex_function f) (hdiff : is_differentiable_at f x) :
    strongDualSubdifferential f x =
      {toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)} := sorry

-- Proof sketch: the interior-point theorem `subdifferential_nonempty_at_interior_point` upgrades
-- the owner-set uniqueness hypothesis `Set.Subsingleton (strongDualSubdifferential f x)` to an
-- actual singleton description. Since `x ∈ interior (finite_domain f)`, it also lies in the
-- interior of `effective_domain f`, and convexity forces the ambient no-`⊥` property needed by
-- the directional-derivative owner theorem, so no stronger primitive hypothesis is needed
-- publicly. Let `g` be that unique subgradient. Translate the function by `x` and subtract the
-- affine functional defined by `g`; the resulting convex function still avoids `⊥` and has unique
-- subgradient `0` at the origin. The max formula then gives vanishing directional derivatives in
-- every direction, and the standard finite-dimensional convex argument upgrades this to
-- differentiability at the origin. Translating back yields differentiability of
-- `y ↦ (f y).toReal` at `x`, and the forward implication identifies the extendedRealSubdifferential with the
-- singleton of the gradient.
/-- Theorem 3.13 (2): if a convex extended-real-valued function has a unique continuous-dual
subgradient at an interior point of its finite domain, then the real-valued map
`y ↦ (f y).toReal` is differentiable there, equivalently `f` is differentiable there in the
chapter sense `is_differentiable_at`, and the extendedRealSubdifferential is the singleton of the
corresponding gradient. -/
theorem differentiableAt_and_subdifferential_eq_singleton_gradient_of_unique_subgradient
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f))
    (hunique : (strongDualSubdifferential f x).Subsingleton) :
    is_differentiable_at f x ∧
      strongDualSubdifferential f x =
        {toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)} := sorry
