import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_23
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_24
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Lemma_5_1_4
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_13
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_8
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm NewtonDecrement SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.2.1 lies in the Chapter 5 self-concordant minimization / Newton-decrement domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for the
  positive-definite-Hessian regime in which the Newton decrement is evaluated from domain
  membership alone;
* `newtonDecrement`, the notation `λ[f; x | hx]`, and
  `NewtonDecrement.omegaArgOfPosDefMem` in `Definition_5_0_24`, the chapter owner for the Newton
  decrement, its positive-definite-domain theorem surface, and the canonical `ω` argument;
* `hessianLocalNorm` and `hessianLocalNorm_nonneg` in `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv` in `Theorem_5_1_13`,
  the chapter minimizer / Newton-decrement owner for the upper `ω_*` bound.

Best owner abstraction:
* source-facing: the minimizer-distance and suboptimality bounds of Theorem 5.2.1;
* core/canonical: `newtonDecrement`, `HasPositiveDefiniteHessianOn`, `hessianLocalNorm`, and the
  chapter self-concordant auxiliary functions;
* bridge/view: the domain-point notation `λ[f; x | hx]` together with the `ω'` / `ω'_*` scalar
  reparameterizations of the same canonical `ω` and `ω_*` arguments.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom` and a feasible minimizer `xStar : dom`.
* for the Newton-decrement clauses only, positive definiteness of the Hessian of `f` on `dom`.

Derived API:
* the domain-level Newton decrement `λ[f; x | hx]`;
* the canonical `ω` argument `NewtonDecrement.omegaArgOfPosDefMem Mf f x hx`;
* the canonical `ω_*` argument obtained from the small-decrement hypothesis;
* the local minimizer distance `‖x - xStar‖[f; x]`.

This file stays source-facing. Its Newton-decrement clauses live in the finite-dimensional
positive-definite-Hessian owner layer, while the minimizer-distance clause stays on the weaker
self-concordant/local-norm layer. The refinement removes the file-local duplicate witnesses for
Hessian nondegeneracy from the theorem surface, reusing the Chapter 5 positive-definite-Hessian
owner and the domain-level Newton-decrement bridge directly instead of keeping a parallel
determinant-witness surface. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

section NewtonDecrementBounds

variable [FiniteDimensional ℝ E]
variable [HasPositiveDefiniteHessianOn dom f]

-- Proof sketch: apply the lower and upper self-concordant value bounds at the minimizer `xStar`.
-- The lower bound comes from Theorem 5.1.12, while the upper bound is the minimizer estimate from
-- Theorem 5.1.13 specialized to the Newton decrement at `x`.
/-- Theorem 5.2.1: if `xStar` minimizes a self-concordant function `f` on `dom` and the Newton
decrement at `x` is smaller than `1 / M_f`, then the scaled suboptimality
`M_f^2 (f x - f xStar)` lies between `ω(M_f λ_f(x))` and `ω_*(M_f λ_f(x))`. This is the textbook
inequality `(5.2.3)`. -/
theorem selfConcordant_suboptimality_bounds_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let tω := NewtonDecrement.omegaArgOfPosDefMem Mf f x hx
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ω tω ≤ (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ∧
      (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ ω_* τω := sorry

-- Proof sketch: combine the gradient-pairing comparison from Theorem 5.1.8 with the Hessian
-- transport estimate from Corollary 5.1.5 to compare the minimizer distance
-- `‖x - xStar‖_x` to the Newton decrement `λ_f(x)`, then rewrite the resulting scalar bounds in
-- terms of `ω'` and `ω'_*`.
/-- The local minimizer distance `‖x - xStar‖_x` satisfies the textbook two-sided estimate
`(5.2.4)` in terms of the Newton decrement `λ_f(x)`. -/
theorem selfConcordant_minimizerDistance_bounds_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let tω := NewtonDecrement.omegaArgOfPosDefMem Mf f x hx
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ω' tω ≤ (Mf : ℝ) * ‖x - xStar‖[f; x] ∧
      (Mf : ℝ) * ‖x - xStar‖[f; x] ≤ ω'_* τω := sorry

end NewtonDecrementBounds

-- Proof sketch: apply the lower and upper self-concordant value bounds with `y = xStar`, using
-- the local distance `r_*(x) = ‖x - xStar‖_x` as the step size. The admissibility hypothesis
-- `r_*(x) < 1 / M_f` supplies the upper `ω_*` estimate.
/-- If the local distance from `x` to a minimizer `xStar` is smaller than `1 / M_f`, then the
scaled suboptimality is bounded between `ω(M_f r_*(x))` and `ω_*(M_f r_*(x))`, which is the
textbook inequality `(5.2.5)`. -/
theorem selfConcordant_suboptimality_bounds_of_minimizerDistance_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hr : ‖x - xStar‖[f; x] < 1 / (Mf : ℝ)) :
    let r := ‖x - xStar‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (x - xStar)))
    let τω := selfConcordantOmegaStarArg Mf r (mf_mul_lt_one_of_lt_inv hr)
    ω tω ≤ (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ∧
      (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ ω_* τω := sorry

end

end
