import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

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
