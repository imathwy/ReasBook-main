import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Real

-- The source-facing integral is canonically the Beta value `β(1 - α, α)`, and the closed form is
-- the standard reflection identity `Real.Gamma_mul_Gamma_one_sub`.

private theorem integral_inv_rpow_mul_one_add_eq_beta
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ α * (1 + x)) ∂volume =
      ProbabilityTheory.beta (1 - α) α := by
  sorry

/-- Example III.6-extra-5: for `0 < α < 1`,
`∫_0^∞ dx / (x^α (1 + x)) = π / sin (π α)`. -/
theorem integral_inv_rpow_mul_one_add
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ α * (1 + x)) ∂volume =
      Real.pi / Real.sin (Real.pi * α) := by
  rw [integral_inv_rpow_mul_one_add_eq_beta α hα0 hα1, ProbabilityTheory.beta,
    show 1 - α + α = 1 by ring, Real.Gamma_one, div_one, mul_comm,
    Real.Gamma_mul_Gamma_one_sub]
