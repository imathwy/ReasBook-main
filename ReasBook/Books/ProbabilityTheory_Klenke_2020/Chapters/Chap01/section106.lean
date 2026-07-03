import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_106 (from Items/Chap01) -/
open MeasureTheory

/-- Definition 1.106: A function `f : (Fin n → ℝ) → ℝ` is a density of the distribution function
`F` on `ℝⁿ`, modeled as `Fin n → ℝ`, if `f` is integrable, nonnegative, and for every
`x : Fin n → ℝ` the value `F x` is the integral of `f` over the closed lower orthant
`Set.Iic x = (-∞, x₁] × ⋯ × (-∞, xₙ]`. -/
class IsDensityOfDistributionFunction {n : ℕ}
    (F : outParam ((Fin n → ℝ) → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop where
  integrable : Integrable f
  nonneg : ∀ x, 0 ≤ f x
  eq_integral_lowerClosedOrthant : ∀ x, F x = ∫ t in Set.Iic x, f t

/-- A density of a distribution function is canonically integrable. -/
instance instFactIntegrableOfIsDensityOfDistributionFunction {n : ℕ}
    {F f : (Fin n → ℝ) → ℝ} [h : IsDensityOfDistributionFunction F f] :
    Fact (Integrable f) :=
  ⟨h.integrable⟩
