import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 5.25 is `source-facing`: it records the existence, uniqueness, and quadratic-growth
consequences of strong convexity for extended-real-valued functions. In item-per-file mode, the
natural owner abstraction is mathlib's `StrongConvexOn` on the real-valued restriction to the
finite-valued domain, while the source-side exclusion of the value `-∞` remains an explicit
separate hypothesis. -/

/-- The effective domain of an extended-real-valued function is the set where the value is finite
from above. Together with an explicit no-`-∞` hypothesis, this is the finite-valued domain used in
the source statements. -/
def effective_domain (f : E → EReal) : Set E := {x | f x < ⊤}

-- Proof sketch: choose `x₀ ∈ effective_domain f` from `hdom`. The owner hypothesis `hstrong`
-- yields a strictly convex real-valued restriction on `effective_domain f`, so
-- `StrictConvexOn.eq_of_isMinOn` gives uniqueness of any global minimizer. Existence follows from
-- the coercive quadratic lower bound implied by strong convexity, together with lower
-- semicontinuity and finite-dimensional compactness of a suitable sublevel set.
/-- Theorem 5.25 (1): a closed `σ`-strongly convex extended-real-valued function with nonempty
effective domain has a unique global minimizer. In this source-faithful item-file formulation, the
explicit source codomain condition excluding the value `-∞` is kept separate from the canonical
owner-level `StrongConvexOn` hypothesis. -/
theorem existsUnique_isMinOn_univ_of_closed_strongly_convex [FiniteDimensional ℝ E]
    {f : E → EReal} {σ : ℝ} (hσ : 0 < σ) (h_ne_bot : ∀ x, f x ≠ ⊥)
    (hdom : (effective_domain f).Nonempty) (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) :
    ∃! xStar : E, IsMinOn f Set.univ xStar := sorry

-- Proof sketch: combine the owner-level strong-convexity inequality with the minimizing property
-- of `xStar` on `Set.univ`. After specializing the Jensen inequality to the segment joining `xStar`
-- and `x` and using that `f xStar ≤ f ((1 - t) • xStar + t • x)` for `t ∈ (0, 1]`, pass to the
-- limit `t → 0` to obtain the quadratic growth estimate.
/-- Theorem 5.25 (2): if `xStar` is a global minimizer of a `σ`-strongly convex extended-real-
valued function, then every `x ∈ dom(f)` satisfies the quadratic growth bound above the minimum.
This is the extended-real rendering of the textbook estimate
`f(x) - f(x^*) ≥ (σ / 2) ‖x - x^*‖²`. -/
theorem lower_quadratic_bound_of_isMinOn_of_strongly_convex
    {f : E → EReal} {σ : ℝ} (hσ : 0 < σ) (h_ne_bot : ∀ x, f x ≠ ⊥)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar) (x : E) (hx : x ∈ effective_domain f) :
    f x ≥ f xStar + ((((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) : ℝ) : EReal) := sorry

end
