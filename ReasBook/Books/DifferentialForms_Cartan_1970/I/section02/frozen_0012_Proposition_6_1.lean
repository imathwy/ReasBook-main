import Mathlib
import cartan.I.section02.«frozen_0008_Proposition_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PowerSeries
open scoped PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Proof sketch: first identify `T` with the formal inverse `S⁻¹` using `hST`, hence `S` has
-- nonzero constant coefficient. After dividing by `a₀ = PowerSeries.constantCoeff S`, rewrite `S`
-- as `1 - U` with `U(0) = 0`; then `T` is obtained by composing `U` with the geometric series
-- `∑ Y^n`, whose radius is `1`, and Proposition `5.1` gives that this composed inverse series has
-- nonzero radius of convergence.
/-- Proposition 6.1: if a scalar power series `S` has nonzero radius of convergence and `T` is a
formal power series satisfying `S * T = 1`, then `T` also has nonzero radius of convergence. -/
theorem powerSeries_right_inverse_radius_ne_zero
    (S T : 𝕜⟦X⟧)
    (hST : S * T = 1)
    (hS : S.radius ≠ 0) :
    T.radius ≠ 0 := sorry

-- Proof sketch: apply `powerSeries_right_inverse_radius_ne_zero` to `S` and `S⁻¹`, using
-- `PowerSeries.mul_inv_cancel hS0` to provide the formal identity `S * S⁻¹ = 1`.
/-- The canonical inverse formal power series of `S` inherits nonzero radius of convergence from
`S` itself. -/
theorem powerSeries_inv_radius_ne_zero
    (S : 𝕜⟦X⟧)
    (hS0 : constantCoeff S ≠ 0)
    (hS : S.radius ≠ 0) :
    (S⁻¹).radius ≠ 0 := by
  simpa using
    powerSeries_right_inverse_radius_ne_zero S S⁻¹ (PowerSeries.mul_inv_cancel S hS0) hS
