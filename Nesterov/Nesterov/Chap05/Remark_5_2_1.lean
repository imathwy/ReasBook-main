import Mathlib
import Nesterov.Chap05.Lemma_5_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: unfold `satisfies_approximate_centering_condition` and then expand
-- `dualLocalNorm` via `dualLocalNorm_def`. Writing `s = ∇ f y`, the shifted covector becomes
-- `s - t ∇ f(y₀)`, so the condition is exactly the inverse-Hessian quadratic-neighborhood bound
-- around the straight line `t ↦ t ∇ f(y₀)` in dual coordinates.
/-- Remark 5.2.1: in dual coordinates `s = ∇ f(y)`, the central path is the straight line
`s(t) = t ∇ f(y₀)`, and the approximate centering condition `(5.2.13)` is exactly the statement
that `s` lies in the inverse-Hessian quadratic neighborhood of that line with radius `β / M_f`.
This is the project's library-facing form of the textbook dual interpretation using
`∇² f_* (s)`. -/
theorem approximateCenteringCondition_iff_dualCentralPathNeighborhood
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ) (β : ℝ) :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      let s := ∇ f y
      Real.sqrt
          (inner ℝ (s - (t : ℝ) • ∇ f (y0 : E))
            ((hessian f y).inverse (s - (t : ℝ) • ∇ f (y0 : E)))) ≤
        β / (Mf : ℝ) := sorry

end
