import FirstOrderMethodsinOptimization.Chap01.Lemma_1_1
import FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 4.20 is `source-facing`: its new mathematical content is the radius-`α` variant of
the closed-ball square-root barrier from Proposition 4.19. The ambient `core/canonical` owners are
already upstream in the project, namely `conjugate_function` from Definition 4.1 and `dualNorm`
from Lemma 1.1, so this file reuses those owners directly instead of keeping parallel local
copies. -/

/-- The extended-real-valued function equal to `-√(α² - ‖x‖²)` on the closed ball of radius `α`
and `∞` outside that ball. -/
def negative_sqrt_alpha_sq_sub_norm_sq_extension (α : ℝ) : E → EReal :=
  fun x ↦
    if ‖x‖ ≤ α then ((-Real.sqrt (α ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_sqrt_alpha_sq_sub_norm_sq_extension`; the statement is exactly
-- its defining conditional formula.
/-- Evaluating `negative_sqrt_alpha_sq_sub_norm_sq_extension α` returns `-√(α² - ‖x‖²)` on the
closed ball of radius `α` and `∞` outside. -/
theorem negative_sqrt_alpha_sq_sub_norm_sq_extension_apply (α : ℝ) (x : E) :
    negative_sqrt_alpha_sq_sub_norm_sq_extension α x =
      if ‖x‖ ≤ α then ((-Real.sqrt (α ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤ :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall conjugate_function
recall dualNorm

-- Proof sketch: if `0 < α`, rewrite `negative_sqrt_alpha_sq_sub_norm_sq_extension α` as
-- `x ↦ α * negative_sqrt_one_sub_norm_sq_extension ((1 / α) • x)`, then apply the positive-scaling
-- conjugacy identity from the chapter and Proposition 4.19 for the unit-ball case. If `α = 0`,
-- the function is `0` at `x = 0` and `∞` elsewhere, so its conjugate is identically `0`, which
-- matches the right-hand side. Simplifying the positive-radius case yields
-- `α * √(1 + ‖y‖_*²)`.
/-- Proposition 4.20: for `α ≥ 0`, if `f_α` is the function equal to `-√(α² - ‖x‖²)` on the
closed ball of radius `α` and `∞` outside, then its Fenchel conjugate at `y ∈ E*` is
`α √(1 + ‖y‖_*²)`. -/
theorem conjugate_negative_sqrt_alpha_sq_sub_norm_sq_extension_eq_alpha_mul_sqrt_one_add_dualNorm_sq
    (α : ℝ) (hα : 0 ≤ α) (y : Module.Dual ℝ E) :
    conjugate_function (negative_sqrt_alpha_sq_sub_norm_sq_extension α) y =
      ((α * Real.sqrt (1 + dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := sorry

end
