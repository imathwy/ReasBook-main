import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Proposition 4.19 is `source-facing`: its primitive local data is the concrete extended-valued
unit-ball function `negative_sqrt_one_sub_norm_sq_extension`. The `core/canonical` owner
abstractions already live upstream in the project as Chapter 4's `conjugate_function` and Chapter
1's `dualNorm`, so this file reuses those owners directly instead of restating parallel local
definitions. -/

section

variable {E : Type u} [NormedAddCommGroup E]

/-- The extended-real-valued function equal to `-√(1 - ‖x‖²)` on the closed unit ball and `∞`
outside it. -/
def negative_sqrt_one_sub_norm_sq_extension : E → EReal :=
  fun x ↦
    if ‖x‖ ≤ 1 then ((-Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_sqrt_one_sub_norm_sq_extension`; the statement is exactly its
-- defining conditional formula on the closed unit ball.
/-- Evaluating `negative_sqrt_one_sub_norm_sq_extension` returns `-√(1 - ‖x‖²)` on the closed unit
ball and `∞` outside it. -/
theorem negative_sqrt_one_sub_norm_sq_extension_apply (x : E) :
    negative_sqrt_one_sub_norm_sq_extension x =
      if ‖x‖ ≤ 1 then ((-Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤ :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall conjugate_function
recall conjugate_function_apply
recall dualNorm

-- Proof sketch: unfold `conjugate_function` and restrict the supremum to the closed unit ball,
-- since the function is `⊤` outside it. Write `x = α u` with `α ∈ [0, 1]` and `‖u‖ = 1`; then
-- the inner supremum over `u` is `α * dualNorm y` by the chapter dual-norm formula. The remaining
-- one-variable maximization of `α * dualNorm y + √(1 - α²)` over `α ∈ [0, 1]` is attained at
-- `α = dualNorm y / √(dualNorm y ^ 2 + 1)`, giving the value `√(dualNorm y ^ 2 + 1)`.
/-- Proposition 4.19: for the function equal to `-√(1 - ‖x‖²)` on the closed unit ball and `∞`
outside it, the Fenchel conjugate at a dual vector `y ∈ E*` is `√(‖y‖_*² + 1)`. -/
theorem conjugate_negative_sqrt_one_sub_norm_sq_extension_eq_sqrt_dualNorm_sq_add_one
    (y : Module.Dual ℝ E) :
    conjugate_function negative_sqrt_one_sub_norm_sq_extension y =
      ((Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal) := sorry

end
