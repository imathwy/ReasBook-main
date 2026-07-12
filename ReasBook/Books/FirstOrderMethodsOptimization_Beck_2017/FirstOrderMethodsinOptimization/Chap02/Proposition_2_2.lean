import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

-- Proof sketch: use the convexity of the real epigraph from `hf` and show that the convex
-- combination of the points `(x i, f (x i))` with weights `λ` again belongs to the epigraph. The
-- first coordinate is `∑ i, λ i • x i`, while the second coordinate is
-- `∑ i, ((λ i : EReal) * f (x i))`, giving the desired inequality.
/-- Proposition 2.2: Jensen's inequality for a convex extended-real-valued function. If
`λ : stdSimplex ℝ (Fin k)` is the textbook simplex vector `Δ_k`, then
`f (∑ i, λ i • x i) ≤ ∑ i, (λ i : EReal) * f (x i)`. -/
theorem convex_function_jensen_inequality {k : ℕ} (hf : is_convex_function f)
    (x : Fin k → E) (w : stdSimplex ℝ (Fin k)) :
    f (∑ i, w i • x i) ≤ ∑ i, ((w i : EReal) * f (x i)) := sorry

end
