import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter04.Assumption_4_3_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter04.Theorem_4_3_4

noncomputable section

open Filter

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n

/-- Chapter04 Theorem 4.3.5: let `f : ℝ^n → ℝ` be twice continuously
differentiable, assume the initial lower level set
`lowerLevelSetOn Set.univ f method.x0` is bounded, and assume `method` is a
Fletcher-Reeves conjugate-gradient run with strong Wolfe-Powell parameters
`0 < ρ < σ < 1 / 2`, allowing finite termination at a stationary point. Then
the method is globally convergent in the source sense:
`liminf ‖gradient f (x_k)‖ = 0`. -/
theorem fletcherReevesConjugateGradient_liminf_gradientNorm_eq_zero
    (f : Point → ℝ) (hC2 : ContDiff ℝ 2 f)
    (method : ConjugateGradientIterativeScheme n f)
    (hWolfe : ConjugateGradientRun.StrongWolfePowell f method.toConjugateGradientRun)
    (hLevelSetBounded : Bornology.IsBounded (lowerLevelSetOn Set.univ f method.x0)) :
    liminf (fun k : ℕ ↦ ‖gradient f (method.x k)‖) atTop = 0 := sorry

end
