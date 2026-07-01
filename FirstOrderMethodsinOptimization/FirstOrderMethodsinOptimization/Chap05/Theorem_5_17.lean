import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- The effective domain of an extended-real-valued function is the set of points where the
function is finite above. -/
def effective_domain {E : Type u} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- An extended-real-valued function is convex when its real epigraph is a convex subset of
`E × ℝ`. -/
def is_convex_function {E : Type u} [AddCommMonoid E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- A source-facing strong-convexity predicate for extended-real-valued functions: the function
never takes the value `-∞`, its effective domain is convex, and it satisfies the quadratic Jensen
inequality on that domain. -/
class is_strongly_convex_function {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (σ : ℝ) : Prop where
  /-- A strongly convex extended-real-valued function never takes the value `-∞`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- The effective domain of a strongly convex function is convex. -/
  convex_effective_domain : Convex ℝ (effective_domain f)
  /-- The defining quadratic Jensen inequality along segments in the effective domain. -/
  segment_ineq :
    ∀ ⦃x⦄, x ∈ effective_domain f → ∀ ⦃y⦄, y ∈ effective_domain f → ∀ ⦃t : ℝ⦄,
      t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤
          (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
            (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  /-- The strong-convexity modulus is strictly positive. -/
  sigma_pos : 0 < σ

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
