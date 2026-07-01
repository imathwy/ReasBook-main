import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries Filter
open scoped NNReal ENNReal

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Proposition I.2-extra-4: Hadamard's formula for a scalar power series `∑ a n z^n` identifies
the inverse of its radius of convergence with the `limsup` of the roots `‖a n‖^(1 / n)`. -/
-- Proof sketch: apply the canonical Cauchy-Hadamard theorem
-- `radius_inv_eq_limsup` to the scalar formal multilinear series
-- `ofScalars 𝕜 a`, then rewrite the norm of its `n`th coefficient using `ofScalars_norm`.
theorem ofScalars_radius_inv_eq_limsup (a : ℕ → 𝕜) :
    (ofScalars 𝕜 a).radius⁻¹ =
      limsup (fun n ↦ ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  have hnorm : ∀ n, ‖ofScalars 𝕜 a n‖₊ = ‖a n‖₊ := fun n ↦
    Subtype.ext (ofScalars_norm 𝕜 a n)
  simpa [hnorm] using radius_inv_eq_limsup (ofScalars 𝕜 a)
