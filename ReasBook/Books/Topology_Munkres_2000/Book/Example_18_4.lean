module

public import Mathlib.Topology.Algebra.Ring.Real

public section

/-- Example 18.4: The function `x ↦ 3 * x + 1` is a homeomorphism of `ℝ`. -/
noncomputable def threeMulAddOneHomeomorph : ℝ ≃ₜ ℝ :=
  (Homeomorph.mulLeft₀ 3 (by norm_num)).trans (Homeomorph.addRight 1)

/-- Applying `threeMulAddOneHomeomorph` gives the source formula. -/
@[simp]
theorem threeMulAddOneHomeomorph_apply (x : ℝ) :
    threeMulAddOneHomeomorph x = 3 * x + 1 := by
  rfl

/-- The inverse homeomorphism is `y ↦ (y - 1) / 3`. -/
@[simp]
theorem threeMulAddOneHomeomorph_symm_apply (y : ℝ) :
    threeMulAddOneHomeomorph.symm y = (y - 1) / 3 := by
  norm_num [threeMulAddOneHomeomorph, Homeomorph.addRight_symm, div_eq_mul_inv]
  ring

/-- The unbundled homeomorphism property of `x ↦ 3 * x + 1`. -/
theorem threeMulAddOne_isHomeomorph :
    IsHomeomorph (fun x : ℝ ↦ 3 * x + 1) := by
  convert threeMulAddOneHomeomorph.isHomeomorph using 1
  funext x
  exact threeMulAddOneHomeomorph_apply x
