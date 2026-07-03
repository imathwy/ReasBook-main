import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_8 (from Chap03) -/
universe u

open scoped Topology
open Filter

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/- Definition 3.8 is `source-facing` in the chapter directional-derivative API. Its
`core/canonical` owner abstractions are the right-hand filter `𝓝[>] (0 : ℝ)`, convergence
`Tendsto`, and the canonical right-limit operator `limUnder`. The bridge/view theorem below is
just the generic Hausdorff uniqueness statement for `limUnder`, specialized to the directional
difference quotient. -/

/-- A directional derivative of `f` at `x` in the direction `d` exists with value `ℓ` when the
directional difference quotients converge to `ℓ` as `α → 0⁺`. -/
def has_directional_derivative_at (f : E → EReal) (x d : E) (ℓ : EReal) : Prop :=
  Tendsto (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 ℓ)

/-- Definition 3.8: the directional derivative of an extended-real-valued function at `x` in the
direction `d` is the right-hand limit of the difference quotient
`α ↦ (f (x + α • d) - f x) / α`. The book introduces this at interior points of the effective
domain of a proper function. -/
noncomputable def directional_derivative (f : E → EReal) (x d : E) : EReal :=
  limUnder (𝓝[>] (0 : ℝ)) (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal))

-- Proof sketch: if the difference quotient tends to `ℓ` along `𝓝[>] 0`, then Hausdorff
-- uniqueness of limits identifies `limUnder` with that same value.
/-- If the directional difference quotients converge to `ℓ` as `α → 0⁺`, then the directional
derivative is equal to `ℓ`. -/
theorem directional_derivative_eq_of_has_directional_derivative_at
    {f : E → EReal} {x d : E} {ℓ : EReal}
    (h : has_directional_derivative_at f x d ℓ) :
    directional_derivative f x d = ℓ := by
  simpa [directional_derivative] using h.limUnder_eq

end

/-! ### Proposition_3_8 (from Chap03) -/
/- Proposition 3.8 is recall-only in the chapter convex-analysis API: the source-facing
proper-convex nonemptiness statement is already provided by
`subdifferential_domain_nonempty_of_proper_convex`, while Proposition 3.7.1 also exposes the
owner-level convex-plus-nonempty-domain theorem and the textbook witness-in-`effective_domain`
companion corollary. -/
recall subdifferential_domain_nonempty_of_proper_convex

/-! ### Theorem_3_8 (from Chap03) -/
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
