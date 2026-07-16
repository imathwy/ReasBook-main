import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {V : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid V] [Module ℝ V]

-- Proof sketch: for each `x`, the value `⨅ y, f (x, y)` is the fiberwise infimum of the convex
-- function `f`. To prove convexity, compare the epigraph of this partial infimum with the image of
-- the epigraph of `f`, then apply convexity of `f` on pairs `(x₁, y₁)` and `(x₂, y₂)`. In the
-- chapter owner formulation `is_convex_function : (E → EReal) → Prop`, the textbook fiberwise
-- finiteness side condition is redundant because the target function may legitimately take the value
-- `⊤`.
/-- Theorem 2.7: convexity is preserved under partial minimization. For the chapter owner notion
`is_convex_function`, if `f : E × V → EReal` is convex, then the fiberwise infimum
`x ↦ ⨅ y : V, f (x, y)` is convex. -/
theorem partial_infimum_is_convex_function
    {f : E × V → EReal} (hf : is_convex_function f) :
    is_convex_function (fun x ↦ ⨅ y : V, f (x, y)) := sorry

end
