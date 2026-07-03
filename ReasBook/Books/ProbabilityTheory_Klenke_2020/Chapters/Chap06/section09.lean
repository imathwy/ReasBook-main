import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_6_9 (from Items/Chap06) -/
/- Remark 6.9: If `f_n → f` in `L¹(μ)`, then in particular the integrals converge,
`∫ x, f_n x ∂μ → ∫ x, f x ∂μ`. This is the canonical continuity of the Bochner integral with
respect to `L¹` convergence. -/
recall MeasureTheory.tendsto_integral_of_L1'
