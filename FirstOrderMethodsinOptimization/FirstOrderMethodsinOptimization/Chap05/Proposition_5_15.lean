import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- The effective domain of an extended-real-valued function is the set of points where the
function takes a finite value. -/
def effective_domain {E : Type u} (f : E → EReal) : Set E := {x | f x < ⊤}

/-- An extended-real-valued function is `σ`-strongly convex if it never takes the value `-∞`, its
effective domain is convex, and it satisfies the quadratic Jensen inequality on that domain for
every weight `t ∈ [0, 1]`. -/
class is_strongly_convex_function {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (σ : ℝ) : Prop where
  /-- A strongly convex extended-real-valued function never takes the value `-∞`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- The effective domain of a strongly convex function is convex. -/
  convex_effective_domain : Convex ℝ (effective_domain f)
  /-- The defining quadratic Jensen inequality holds along every segment in the effective domain. -/
  segment_ineq :
    ∀ ⦃x⦄, x ∈ effective_domain f → ∀ ⦃y⦄, y ∈ effective_domain f → ∀ ⦃t : ℝ⦄,
      t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤
          (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
            (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  /-- The strong-convexity modulus is strictly positive. -/
  sigma_pos : 0 < σ

noncomputable section

section

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

local notation "E" => WithLp (ENNReal.ofReal p) (Fin n → ℝ)

/- Proposition 5.15 is `source-facing`: the textbook object is the half-squared `ℓ_p` norm on
`ℝ^n` for `1 < p ≤ 2`. Domain sampling points to mathlib's owner predicate `StrongConvexOn` and
the canonical `WithLp` model of `ℝ^n`; the chapter's extended-real-valued predicate from
Definition 5.16 is the derived bridge/view rather than the owner-level main statement. -/

-- Proof sketch: use the standard uniform convexity of finite-dimensional `ℓ_p` spaces for
-- `1 < p ≤ 2`, in the form of Clarkson's inequality or the equivalent Hessian lower bound for
-- `x ↦ ‖x‖² / 2`, to verify the defining Jensen inequality for `StrongConvexOn` on `Set.univ`.
/-- Proposition 5.15: for `1 < p ≤ 2`, the half-squared `ℓ_p` norm on `ℝ^n`, viewed on the
canonical `WithLp` model, is globally `(p - 1)`-strongly convex with respect to the `ℓ_p` norm. -/
theorem half_squared_lp_norm_is_strongly_convex
    (hp_lower : 1 < p) (hp_upper : p ≤ 2) :
    StrongConvexOn Set.univ (p - 1) (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2) := sorry

-- Proof sketch: translate the owner-level `StrongConvexOn` statement into the defining quadratic
-- Jensen inequality for the finite-valued extended-real-valued function
-- `z ↦ ((‖z‖² / 2 : ℝ) : EReal)`, observing that its effective domain is all of `E` and that it
-- never takes the value `-∞`.
/-- The half-squared `ℓ_p` norm is strongly convex in the chapter's source-facing extended-real
sense. -/
theorem half_squared_lp_norm_is_strongly_convex_function
    (hp_lower : 1 < p) (hp_upper : p ≤ 2) :
    is_strongly_convex_function
      (fun z : E ↦ ((‖z‖ ^ (2 : ℕ) / 2 : ℝ) : EReal))
      (p - 1) := sorry

end
