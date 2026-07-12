import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries NormedSpace
open Filter

universe u

variable {𝕜 : Type u}

/-- Cartan section02 frozen_0007_Example_I_2_extra_5. Example I.2-extra-5 (1): the scalar power
series `∑_{n ≥ 0} n! z^n` has radius of convergence equal to `0`. -/
-- Proof sketch: apply the ratio-test statement
-- `FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto` to the coefficients `n!`, using
-- `(n + 1)! / n! = n + 1` and the fact that this tends to `+∞`.
theorem factorial_coefficients_radius_eq_zero [RCLike 𝕜] :
    (ofScalars 𝕜 (fun n ↦ (n.factorial : 𝕜))).radius = 0 := by
  -- Apply the ratio-test radius criterion on `ofScalars` and normalize the ratio to `n + 1`.
  apply ofScalars_radius_eq_zero_of_tendsto 𝕜
  refine Filter.Tendsto.congr' ?_
    ((Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop)
  refine Filter.Eventually.of_forall fun n ↦ ?_
  change (n.succ : ℝ) = ‖((n.succ.factorial : ℕ) : 𝕜)‖ / ‖((n.factorial : ℕ) : 𝕜)‖
  -- Rewrite `(n + 1)! / n!` as `n + 1`, then express the norms via `RCLike.norm_natCast`.
  calc
    (n.succ : ℝ) = ‖((n.succ : ℕ) : 𝕜)‖ := by
      simpa using (RCLike.norm_natCast n.succ).symm
    _ = ‖((n.succ.factorial : ℕ) : 𝕜)‖ / ‖((n.factorial : ℕ) : 𝕜)‖ := by
      symm
      rw [Nat.factorial_succ, Nat.cast_mul, norm_mul, RCLike.norm_natCast]
      have hfac : ‖((n.factorial : ℕ) : 𝕜)‖ ≠ 0 := by
        have hfac' : (n.factorial : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero n
        simpa [RCLike.norm_natCast] using hfac'
      rw [mul_div_assoc, div_self hfac, mul_one]

/-- Helper for Cartan section02 frozen_0007_Example_I_2_extra_5: Example I.2-extra-5 (2), the
scalar power series `∑_{n ≥ 0} z^n / n!` has infinite radius of convergence. -/
-- Proof sketch: identify this scalar series with the exponential formal power series via
-- `NormedSpace.expSeries_eq_ofScalars`, then use `NormedSpace.expSeries_radius_eq_top`.
theorem inverse_factorial_coefficients_radius_eq_top
    [NontriviallyNormedField 𝕜] [CharZero 𝕜] [ContinuousSMul ℚ 𝕜] :
    (ofScalars 𝕜 (fun n ↦ (n.factorial : 𝕜)⁻¹)).radius = ⊤ := by
  simpa [expSeries_eq_ofScalars] using expSeries_radius_eq_top 𝕜 𝕜

/-- Helper for Cartan section02 frozen_0007_Example_I_2_extra_5: Example I.2-extra-5 (3), the
geometric series `∑_{n ≥ 0} z^n` has radius of convergence equal to `1`. -/
-- Proof sketch: identify this scalar series with the canonical geometric formal multilinear series
-- via `formalMultilinearSeries_geometric_eq_ofScalars`, then use
-- `formalMultilinearSeries_geometric_radius`.
theorem geometric_series_radius_eq_one [NontriviallyNormedField 𝕜] :
    (ofScalars 𝕜 (fun _ ↦ (1 : 𝕜))).radius = 1 := by
  simpa [formalMultilinearSeries_geometric_eq_ofScalars] using
    formalMultilinearSeries_geometric_radius 𝕜 𝕜

/-- Helper for Cartan section02 frozen_0007_Example_I_2_extra_5: Example I.2-extra-5 (4), the
harmonic power series `∑_{n ≥ 1} z^n / n`, written in Lean by setting the undefined constant
coefficient to `0`, has radius of convergence equal to `1`. -/
-- Proof sketch: apply the ratio-test statement
-- `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto` to the coefficients
-- `if n = 0 then 0 else 1 / n`, since the ratio of successive nonzero coefficients tends to `1`.
theorem harmonic_series_radius_eq_one [RCLike 𝕜] :
    (ofScalars 𝕜
      (fun n ↦ if n = 0 then 0 else (n : 𝕜)⁻¹)).radius = 1 := by
  -- Apply the ratio-test criterion with target radius `1`.
  apply ofScalars_radius_eq_of_tendsto 𝕜 (fun n ↦ if n = 0 then 0 else (n : 𝕜)⁻¹) one_ne_zero
  have hlim : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) + (n : ℝ)⁻¹) atTop (nhds 1) := by
    -- The normalized ratio is `1 + 1 / n`, which tends to `1`.
    simpa using
      (tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) + (n : ℝ)⁻¹) atTop (nhds ((1 : ℝ) + 0)))
  refine Filter.Tendsto.congr' ?_ hlim
  refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn0
  -- For `n ≥ 1`, both coefficients are nonzero and the ratio simplifies explicitly.
  symm
  change ‖if n = 0 then 0 else (n : 𝕜)⁻¹‖ / ‖if n.succ = 0 then 0 else (n.succ : 𝕜)⁻¹‖ =
    1 + (n : ℝ)⁻¹
  rw [if_neg hn0, if_neg (Nat.succ_ne_zero n), norm_inv, norm_inv, RCLike.norm_natCast,
    RCLike.norm_natCast]
  field_simp [hnR]
  simp [Nat.cast_add]

/-- Helper for Cartan section02 frozen_0007_Example_I_2_extra_5: Example I.2-extra-5 (5), the
power series `∑_{n ≥ 1} z^n / n^2`, written in Lean by setting the undefined constant coefficient
to `0`, has radius of convergence equal to `1`. -/
-- Proof sketch: apply the ratio-test statement
-- `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto` to the coefficients
-- `if n = 0 then 0 else 1 / n^2`, since the ratio of successive nonzero coefficients tends to
-- `1`.
theorem inverse_square_series_radius_eq_one [RCLike 𝕜] :
    (ofScalars 𝕜
      (fun n ↦ if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹)).radius = 1 := by
  -- Apply the same ratio-test criterion, now with squared coefficients.
  apply ofScalars_radius_eq_of_tendsto 𝕜
    (fun n ↦ if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹) one_ne_zero
  have hlim : Filter.Tendsto (fun n : ℕ ↦ ((1 : ℝ) + (n : ℝ)⁻¹) ^ 2) atTop (nhds 1) := by
    -- The normalized ratio is the square of the harmonic ratio.
    simpa using
      ((tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) + (n : ℝ)⁻¹) atTop (nhds ((1 : ℝ) + 0))).pow 2)
  refine Filter.Tendsto.congr' ?_ hlim
  refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn0
  -- For `n ≥ 1`, the ratio of successive coefficients simplifies to the square of `1 + 1 / n`.
  symm
  change ‖if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹‖ /
      ‖if n.succ = 0 then 0 else ((n.succ : 𝕜) ^ 2)⁻¹‖ =
    ((1 : ℝ) + (n : ℝ)⁻¹) ^ 2
  rw [if_neg hn0, if_neg (Nat.succ_ne_zero n), norm_inv, norm_inv, norm_pow, norm_pow,
    RCLike.norm_natCast, RCLike.norm_natCast]
  field_simp [hnR]
  simp [Nat.cast_add]

/-- Helper for Cartan section02 frozen_0007_Example_I_2_extra_5: package the five scalar power
series radius computations into a single conjunction. -/
theorem scalarPowerSeriesExampleRadii [RCLike 𝕜] [ContinuousSMul ℚ 𝕜] :
    (ofScalars 𝕜 (fun n ↦ (n.factorial : 𝕜))).radius = 0 ∧
      (ofScalars 𝕜 (fun n ↦ (n.factorial : 𝕜)⁻¹)).radius = ⊤ ∧
      (ofScalars 𝕜 (fun _ ↦ (1 : 𝕜))).radius = 1 ∧
      (ofScalars 𝕜 (fun n ↦ if n = 0 then 0 else (n : 𝕜)⁻¹)).radius = 1 ∧
      (ofScalars 𝕜 (fun n ↦ if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹)).radius = 1 := by
  -- Package the five example computations into the single item-level statement expected here.
  refine ⟨factorial_coefficients_radius_eq_zero (𝕜 := 𝕜), ?_, ?_, ?_, ?_⟩
  · exact inverse_factorial_coefficients_radius_eq_top (𝕜 := 𝕜)
  · exact geometric_series_radius_eq_one (𝕜 := 𝕜)
  · exact harmonic_series_radius_eq_one (𝕜 := 𝕜)
  · exact inverse_square_series_radius_eq_one (𝕜 := 𝕜)
