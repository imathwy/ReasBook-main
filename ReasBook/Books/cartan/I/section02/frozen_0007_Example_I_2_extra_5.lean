import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries NormedSpace

universe u

variable {𝕜 : Type u}

/-- Example I.2-extra-5 (1): the scalar power series `∑_{n ≥ 0} n! z^n` has radius of convergence
equal to `0`. -/
-- Proof sketch: apply the ratio-test statement
-- `FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto` to the coefficients `n!`, using
-- `(n + 1)! / n! = n + 1` and the fact that this tends to `+∞`.
theorem factorial_coefficients_radius_eq_zero [RCLike 𝕜] :
    (ofScalars 𝕜 (fun n ↦ (n.factorial : 𝕜))).radius = 0 := sorry

/-- Example I.2-extra-5 (2): the scalar power series `∑_{n ≥ 0} z^n / n!` has infinite radius of
convergence. -/
-- Proof sketch: identify this scalar series with the exponential formal power series via
-- `NormedSpace.expSeries_eq_ofScalars`, then use `NormedSpace.expSeries_radius_eq_top`.
theorem inverse_factorial_coefficients_radius_eq_top
    [NontriviallyNormedField 𝕜] [CharZero 𝕜] [ContinuousSMul ℚ 𝕜] :
    (ofScalars 𝕜 (fun n ↦ (n.factorial : 𝕜)⁻¹)).radius = ⊤ := by
  simpa [expSeries_eq_ofScalars] using expSeries_radius_eq_top 𝕜 𝕜

/-- Example I.2-extra-5 (3): the geometric series `∑_{n ≥ 0} z^n` has radius of convergence
equal to `1`. -/
-- Proof sketch: identify this scalar series with the canonical geometric formal multilinear series
-- via `formalMultilinearSeries_geometric_eq_ofScalars`, then use
-- `formalMultilinearSeries_geometric_radius`.
theorem geometric_series_radius_eq_one [NontriviallyNormedField 𝕜] :
    (ofScalars 𝕜 (fun _ ↦ (1 : 𝕜))).radius = 1 := by
  simpa [formalMultilinearSeries_geometric_eq_ofScalars] using
    formalMultilinearSeries_geometric_radius 𝕜 𝕜

/-- Example I.2-extra-5 (4): the harmonic power series `∑_{n ≥ 1} z^n / n`, written in Lean by
setting the undefined constant coefficient to `0`, has radius of convergence equal to `1`. -/
-- Proof sketch: apply the ratio-test statement
-- `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto` to the coefficients
-- `if n = 0 then 0 else 1 / n`, since the ratio of successive nonzero coefficients tends to `1`.
theorem harmonic_series_radius_eq_one [RCLike 𝕜] :
    (ofScalars 𝕜
      (fun n ↦ if n = 0 then 0 else (n : 𝕜)⁻¹)).radius = 1 := sorry

/-- Example I.2-extra-5 (5): the power series `∑_{n ≥ 1} z^n / n^2`, written in Lean by setting
the undefined constant coefficient to `0`, has radius of convergence equal to `1`. -/
-- Proof sketch: apply the ratio-test statement
-- `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto` to the coefficients
-- `if n = 0 then 0 else 1 / n^2`, since the ratio of successive nonzero coefficients tends to
-- `1`.
theorem inverse_square_series_radius_eq_one [RCLike 𝕜] :
    (ofScalars 𝕜
      (fun n ↦ if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹)).radius = 1 := sorry
