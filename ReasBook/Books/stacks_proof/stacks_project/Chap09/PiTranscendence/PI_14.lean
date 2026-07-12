import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this environment; the statement
-- below uses the direct source-faithful complex norm formulation from the item.

/-- Lemma PI-14: If `Z ∈ ℤ` and `Z ≠ 0`, then `‖(Z : ℂ)‖ ≥ 1`. -/
theorem norm_int_cast_complex_ge_one (Z : ℤ) (hZ : Z ≠ 0) : ‖(Z : ℂ)‖ ≥ (1 : ℝ) := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hZ
