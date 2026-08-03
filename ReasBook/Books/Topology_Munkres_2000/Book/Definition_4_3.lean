module

import Mathlib.Data.Real.Basic

/- Definition 4.3 (1). The negative of `x : ℝ` is `-x`, characterized by
`x + y = 0 ↔ y = -x`. -/
#check (fun x : ℝ ↦ -x)
#check (add_eq_zero_iff_eq_neg' : ∀ {x y : ℝ}, x + y = 0 ↔ y = -x)

/- Definition 4.3 (2). Subtraction on `ℝ` is defined by
`z - x = z + -x`. -/
#check (fun z x : ℝ ↦ z - x)
#check (sub_eq_add_neg : ∀ z x : ℝ, z - x = z + -x)

/- Definition 4.3 (3). For nonzero `x : ℝ`, its reciprocal is `x⁻¹`,
characterized by `x * y = 1 ↔ x⁻¹ = y`. -/
#check (fun x : ℝ ↦ x⁻¹)
#check (mul_eq_one_iff_inv_eq₀ : ∀ {x y : ℝ}, x ≠ 0 → (x * y = 1 ↔ x⁻¹ = y))

/- Definition 4.3 (4). The quotient `z / x` is `z * x⁻¹`. Lean writes
multiplication explicitly as `z * x` rather than by juxtaposition. -/
#check (fun z x : ℝ ↦ z / x)
#check (div_eq_mul_inv : ∀ z x : ℝ, z / x = z * x⁻¹)
