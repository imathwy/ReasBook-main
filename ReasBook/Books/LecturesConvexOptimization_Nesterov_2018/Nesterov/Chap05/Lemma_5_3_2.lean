import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_20
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: rewrite the approximate-centering hypothesis as
-- `t ‖c‖*_x ≤ ‖t c + ∇ F(x)‖*_x + ‖∇ F(x)‖*_x` by the triangle inequality for the dual local norm.
-- Then use the barrier gradient estimate `‖∇ F(x)‖*_x ≤ √ν`, which is the inverse-Hessian form of
-- the barrier-parameter bound, and divide by the positive scalar `t`.
/-- Lemma 5.3.2: if `x` in the domain of a `ν`-self-concordant barrier `F` satisfies the
approximate-centering condition `‖t c + ∇ F(x)‖*ₓ ≤ β` for some `t > 0`, then the dual local norm
of the objective vector is bounded by `‖c‖*ₓ ≤ (β + √ν) / t`. -/
theorem dualLocalNorm_objectiveVector_le_add_sqrt_barrierParameter_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) {t β : ℝ} (ht : 0 < t)
    {x : dom}
    (hH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hH
        ((InnerProductSpace.toDual ℝ E) (t • c + ∇ F (x : E))) ≤ β) :
    HessianDualLocalNorm.ofDetNeZero F (x : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hH
      ((InnerProductSpace.toDual ℝ E) c) ≤
      (β + Real.sqrt (ν : ℝ)) / t := sorry

end
