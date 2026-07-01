import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The effective domain of an extended-real-valued function is the set of points where the
function takes a finite value. -/
def effective_domain (f : E → EReal) : Set E := {x | f x < ⊤}

/-- An extended-real-valued function is strongly convex when it has no `-∞` values, its effective
domain is convex, and it satisfies the quadratic Jensen inequality there for a positive modulus. -/
class is_strongly_convex_function (f : E → EReal) (σ : ℝ) : Prop where
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

-- Proof sketch: translate the source predicate to the canonical owner statement
-- `StrongConvexOn (effective_domain f) σ₁ (fun x ↦ (f x).toReal)` on the finite-valued
-- restriction, apply `StrongConvexOn.mono hσ₂σ₁.le` to lower the modulus from `σ₁` to `σ₂`, and
-- then translate back while keeping the inherited no-`⊥` and convex-domain data from `hf` and the
-- new positivity hypothesis `hσ₂`.
/-- Proposition 5.10: if an extended-real-valued function is `σ₁`-strongly convex, then it is
also `σ₂`-strongly convex for every smaller positive modulus `σ₂ < σ₁`. -/
theorem is_strongly_convex_function.mono
    {f : E → EReal} {σ₁ σ₂ : ℝ} (hf : is_strongly_convex_function f σ₁)
    (hσ₂ : 0 < σ₂) (hσ₂σ₁ : σ₂ < σ₁) :
    is_strongly_convex_function f σ₂ := sorry

end
