import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: the first inequality is the `n = 1` case of mathlib's canonical remainder bound
-- for the complex exponential series, and the second is the standard real estimate
-- `exp t - 1 ≤ t * exp t` applied to `t = ‖z‖`.
/-- Exercise 10: for a complex number `z`, the distance from `e^z` to `1` is bounded above by
`e^{‖z‖} - 1`, and this quantity is bounded above by `‖z‖ e^{‖z‖}`. -/
theorem complex_exp_sub_one_bounds (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 ∧
      Real.exp ‖z‖ - 1 ≤ ‖z‖ * Real.exp ‖z‖ := by
  have h_exp : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
    simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
  have h_real : Real.exp ‖z‖ - 1 ≤ ‖z‖ * Real.exp ‖z‖ := by
    have h := Real.one_sub_le_exp_neg ‖z‖
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_nonneg ‖z‖)
    have h'' : Real.exp ‖z‖ - ‖z‖ * Real.exp ‖z‖ ≤ 1 := by
      calc
        Real.exp ‖z‖ - ‖z‖ * Real.exp ‖z‖ = (1 - ‖z‖) * Real.exp ‖z‖ := by ring
        _ ≤ Real.exp (-‖z‖) * Real.exp ‖z‖ := h'
        _ = 1 := by rw [← Real.exp_add]; simp
    linarith
  exact ⟨h_exp, h_real⟩
