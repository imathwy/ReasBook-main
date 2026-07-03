import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_57 (from Chap06) -/
noncomputable section

universe u

section

/- Definition 6.57 [Estimating functional sequence]: the Chapter 6 estimating sequence `φ_t` is
the recursively defined family with `φ_0(x) = a_0 * \tilde f(x)` and
`φ_{t+1}(x) = φ_t(x) + a_{t+1} * (f(x_t) + ∇f(x_t)(x - x_t) + Ψ(x))`. This is exactly the
chapter owner `ConditionalGradientContraction.estimatingFunctionalSequence`, so the item is
formalized as a direct recall of that canonical recursive definition. -/
recall ConditionalGradientContraction.estimatingFunctionalSequence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → ℝ) (tildeF f : E → ℝ) (gradF : E → StrongDual ℝ E) (Ψ : E → ℝ)
    (xSeq : ℕ → E) :
    ℕ → E → ℝ

end

end
