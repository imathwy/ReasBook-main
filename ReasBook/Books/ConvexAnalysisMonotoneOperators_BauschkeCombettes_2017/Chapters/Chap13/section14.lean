import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_13_14 (from Chap13) -/
open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: Example 13.4 identifies this function with the Fenchel conjugate of
-- `x ↦ φ x + ‖x‖² / (2γ)`, and Proposition 13.13 places every conjugate in `Γ(H)`.
/-- Example 13.14 (1): for `γ ∈ ℝ_{++}`, the function
`u ↦ (γ / 2) ‖u‖² - {}^γφ(γ u)` belongs to `Γ(H)`. -/
theorem scaledQuadratic_sub_moreauEnvelope_comp_smul_mem_gamma
    (φ : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) :
    (fun u : H ↦ ((((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) : EReal) - ({}^[γ] φ) ((γ : ℝ) • u))
      ∈ gamma H := by
  rw [← conjugate_regularized_eq_scaledQuadratic_sub_moreauEnvelope φ γ]
  exact conjugate_mem_gamma ((φ + moreauQuadraticKernel γ).asEReal)

-- Proof sketch: Example 13.5 identifies
-- `u ↦ (‖u‖² - d(u, C)²) / 2` with a Fenchel conjugate when `C` is nonempty, hence
-- Proposition 13.13 places it in `Γ(H)`; the corresponding `]-∞,+∞]`-valued representative then
-- belongs to `Γ₀(H)`.
/-- Example 13.14 (2): if `C` is nonempty, then the function
`u ↦ ‖u‖² - d(u, C)²`, viewed via `Function.toEReal`, belongs to `Γ₀(H)`. -/
theorem sqNormSubSqInfDist_mem_gammaZero
    (C : Set H) (hC_nonempty : C.Nonempty) :
    (fun u : H ↦ ‖u‖ ^ 2 - Metric.infDist u C ^ 2).toEReal ∈ Γ₀(H) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  have hhalf :
      (fun u : H ↦ ((((‖u‖ ^ 2 - Metric.infDist u C ^ 2) / 2 : ℝ) : EReal))) ∈ gamma H := by
    rw [← fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two C
      hC_nonempty]
    exact conjugate_mem_gamma ((ι[C] + halfSquaredNorm).asEReal)
  have hscaled :
      (fun u : H ↦ (2 : EReal) * ((((‖u‖ ^ 2 - Metric.infDist u C ^ 2) / 2 : ℝ) : EReal))) ∈
        gamma H :=
    const_mul_mem_gamma_of_nonneg hhalf (by positivity)
  convert hscaled using 1
  ext u
  symm
  change (((2 : ℝ) * ((‖u‖ ^ 2 - Metric.infDist u C ^ 2) / 2) : ℝ) : EReal) =
    (((‖u‖ ^ 2 - Metric.infDist u C ^ 2 : ℝ) : EReal))
  exact_mod_cast by ring

end

end ERealFunction
