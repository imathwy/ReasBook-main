import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section

/-- Example 7.4 (11): the coordinatewise character `εⁿ : ℝⁿ → (S¹)ⁿ` is an additive character. -/
def torus_epsilon_add_char (n : ℕ) : AddChar (Fin n → ℝ) (Fin n → Circle) where
  toFun := fun x i ↦ Real.fourierChar (x i)
  map_zero_eq_one' := sorry
  map_add_eq_mul' := sorry

scoped[Torus] notation "ε^{" n:max "}" => torus_epsilon_add_char n
