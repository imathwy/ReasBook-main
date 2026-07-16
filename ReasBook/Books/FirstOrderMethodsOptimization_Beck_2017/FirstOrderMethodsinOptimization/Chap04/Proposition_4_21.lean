import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap01.Lemma_1_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/-- The function `x ↦ √(α² + ‖x‖²)`, regarded as an `EReal`-valued function so it can be fed to
the chapter owner `conjugate_function`. -/
def sqrt_alpha_sq_add_norm_sq_function (α : ℝ) : E → EReal :=
  fun x ↦ ((Real.sqrt (α ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)

-- Proof sketch: unfold `sqrt_alpha_sq_add_norm_sq_function`; the statement is exactly its defining
-- formula.
/-- Evaluating `sqrt_alpha_sq_add_norm_sq_function α` at `x` gives the `EReal` lift of
`√(α² + ‖x‖²)`. -/
theorem sqrt_alpha_sq_add_norm_sq_function_apply (α : ℝ) (x : E) :
    sqrt_alpha_sq_add_norm_sq_function α x =
      ((Real.sqrt (α ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.21 is `source-facing` in the chapter conjugacy API. The owner abstractions for
the conjugate and the dual norm already live upstream as `conjugate_function` and `dualNorm`, so
the only primitive data local to this file are the specific model function
`x ↦ √(α² + ‖x‖²)` and the source-facing conjugacy formula for that function. -/
recall conjugate_function
recall dualNorm

-- Proof sketch: rewrite `g_α` as the positive scalar multiple
-- `x ↦ α * √(1 + ‖(1 / α) • x‖²)` and combine the scaling rule for Fenchel conjugates with the
-- preceding unit-ball conjugacy formula from Proposition 4.19. After simplifying the rescaled dual
-- norm condition, the value on the dual unit ball is `-α * √(1 - ‖y‖_*²)` and it is `∞`
-- outside that ball.
/-- Proposition 4.21: for `α > 0`, the Fenchel conjugate of `g_α(x) = √(α² + ‖x‖²)` is
`-α √(1 - ‖y‖_*²)` on the dual unit ball and `∞` outside it, where `‖y‖_*` is `dualNorm y`. -/
theorem sqrt_alpha_sq_add_norm_sq_function_conjugate_eq
    (α : ℝ) (hα : 0 < α) (y : Module.Dual ℝ E) :
    conjugate_function (sqrt_alpha_sq_add_norm_sq_function α) y =
      if dualNorm y ≤ 1 then
        ((-α * Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal)
      else ⊤ := sorry

end
