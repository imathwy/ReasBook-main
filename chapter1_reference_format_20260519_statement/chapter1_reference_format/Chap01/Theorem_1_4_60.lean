import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: rewrite `z ∈ Metric.sphere (0 : ℂ) 1` as `‖z‖ = 1`, use the canonical
-- parametrization `Complex.norm_eq_one_iff` coming from `Circle.exp`, and then rewrite
-- `Complex.exp (θ * Complex.I)` as `Real.cos θ + Real.sin θ * Complex.I` via
-- `Complex.exp_ofReal_mul_I`.
/-- Theorem 1.4.60: a complex number belongs to the unit circle `S^1` if and only if it can be
written in the form `cos θ + i sin θ` for some real number `θ`. -/
theorem mem_complex_unit_circle_iff_eq_cos_add_sin_mul_I (z : ℂ) :
    z ∈ Metric.sphere (0 : ℂ) 1 ↔
      ∃ θ : ℝ, z = Real.cos θ + Real.sin θ * Complex.I := by
  rw [mem_sphere_zero_iff_norm, Complex.norm_eq_one_iff]
  constructor
  · rintro ⟨θ, hθ⟩
    refine ⟨θ, ?_⟩
    rw [← hθ, Complex.exp_ofReal_mul_I]
  · rintro ⟨θ, rfl⟩
    refine ⟨θ, ?_⟩
    rw [Complex.exp_ofReal_mul_I]
