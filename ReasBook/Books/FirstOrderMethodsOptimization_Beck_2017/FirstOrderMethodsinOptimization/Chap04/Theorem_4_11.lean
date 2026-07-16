import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 4.11 is `source-facing`: it rewrites Fenchel--Young equality in the textbook's
`argmax` language. The owner abstractions are already upstream: `conjugate_function` from
Definition 4.1 and Mathlib's `IsMaxOn`. This file is therefore only a `bridge/view` layer and
reuses those owners directly instead of repeating local copies of the same convex-analysis data. -/

recall conjugate_function

-- Proof sketch: unfold `conjugate_function`; by `isMaxOn_univ_iff`, saying that `x` maximizes the
-- affine-minus-`f` objective over `E` is exactly the statement that the value at `x` attains the
-- supremum defining `conjugate_function f y`.
/-- Theorem 4.11: the equality `f*(y) = ⟨y, x⟩ - f(x)` can be rewritten as the statement that `x`
is an argmax of the affine-minus-`f` objective, rendered in Lean as `IsMaxOn ... Set.univ x`. -/
theorem conjugate_function_eq_iff_isMaxOn_pairing_sub_function
    (f : E → EReal) (x : E) (y : Module.Dual ℝ E) :
    conjugate_function f y = (y x : EReal) - f x ↔
      IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall is_convex_function
recall conjugate_function

-- Proof sketch: rewrite the right-hand side as the statement that `y` attains the supremum in
-- the definition of `f**(x)`, then use `biconjugate_function_eq_self_of_closed_convex` to
-- identify `f**` with `f`. The properness hypothesis from the textbook statement is redundant for
-- this equivalence, so the canonical owner-based formulation omits it.
/-- Under the chapter closedness and convexity hypotheses, the equality
`f(x) = ⟨x, y⟩ - f*(y)` is equivalent to saying that `y` is an argmax of the affine-minus-`f*`
objective on the dual space. -/
theorem self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_closed_convex
    (f : E → EReal) (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f)
    (x : E) (y : Module.Dual ℝ E) :
    f x = (y x : EReal) - conjugate_function f y ↔
      IsMaxOn
        (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
        Set.univ y := sorry

end
