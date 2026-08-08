import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

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
