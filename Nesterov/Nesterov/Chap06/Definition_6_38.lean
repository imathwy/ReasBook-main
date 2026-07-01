import Mathlib
import Nesterov.Chap03.Definition_3_1_5
import Nesterov.Chap03.Definition_3_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient StrongConvex WithTopConvexAnalysis

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (σ : ℝ) (f : E → ℝ)

/- Definition 6.38 [Chapter6_1.json:87]: strong convexity with parameter `\hatσ > 0` is the
existing whole-space positive-parameter strong-convexity owner `f ∈ 𝒮^0_σ(Set.univ)`. -/
#check (f ∈ 𝒮^0_σ(Set.univ))

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Whole-space positive-parameter strong convexity is equivalent to the textbook subgradient
lower-tangent inequality with quadratic term `(σ / 2) * ‖y - x‖²`. -/
-- Proof sketch: combine the source-facing owner equivalence `mem_S0On_iff` with the whole-space
-- specialization of the Chapter 3 strong-convexity lower bound for subgradients, then recover the
-- owner predicate from the same lower-tangent family in the reverse direction.
theorem wholeSpace_positiveStrongConvexity_iff_exists_subgradient_quadratic_lower_bound
    {σ : ℝ} {f : E → ℝ} :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
            f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := sorry

/-- For differentiable functions, whole-space positive-parameter strong convexity is equivalent to
the textbook gradient lower-tangent inequality with the same quadratic term. -/
-- Proof sketch: rewrite the subgradient formulation above using the singleton subdifferential
-- carried by differentiability, equivalently by replacing a chosen subgradient with the canonical
-- gradient `∇ f x` at each base point.
theorem wholeSpace_positiveStrongConvexity_iff_gradient_quadratic_lower_bound_of_differentiable
    [CompleteSpace E] {σ : ℝ} {f : E → ℝ} (hf : Differentiable ℝ f) :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := sorry

end
