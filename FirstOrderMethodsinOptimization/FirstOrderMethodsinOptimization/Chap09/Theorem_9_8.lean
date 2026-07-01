import Mathlib
import FirstOrderMethodsinOptimization.Chap09.Lemma_9_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-
Theorem 9.8 is a `source-facing` constrained specialization of the Chapter 9 owner theorem
`existsUnique_composite_minimizer_mem_domains`. Its primitive mathematical data are the feasible
set `C`, the dual linear perturbation `a`, and the Bregman potential hypothesis on `ω`; the
constrained formulation over `C` is derived by taking `ψ = ((a · : ℝ) : EReal) + δ_C`.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {ω : E → EReal} {σ : ℝ}

-- Proof sketch: apply Lemma 9.7 to
-- `ψ(x) = ((a x : ℝ) : EReal) + extendedIndicator C x`. The indicator of a nonempty closed convex
-- set is proper, closed, and convex, and adding the linear functional preserves those properties.
-- Then translate the resulting global minimizer statement back to minimization over `C`.
/-- Theorem 9.8: if `C` is nonempty, closed, and convex and `ω` is a Bregman potential on `C`,
then for every dual vector `a`, the constrained problem
`min_{x ∈ C} {⟨a, x⟩ + ω(x)}` has a unique minimizer, and that minimizer lies in
`C ∩ dom(∂ ω)`. -/
theorem existsUnique_mirror_descent_problem_minimizer_mem_domains
    (a : StrongDual ℝ E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hω : IsBregmanPotentialOn ω C σ) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + ω x) C xStar ∧
        xStar ∈ C ∩ subdifferential_domain ω := sorry

end
