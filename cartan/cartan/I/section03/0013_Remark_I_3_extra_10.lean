import cartan.I.section03.«0011_Proposition_6_1»

open scoped Topology

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: use `logarithmic_power_series_tsum_eq` from Proposition 6.1 to identify
-- `Complex.logarithmicPowerSeries` locally with `z ↦ Complex.log (1 + z)` on a ball inside the
-- open unit disk, then apply `Complex.hasDerivAt_log` at `1 + u ∈ Complex.slitPlane`.
/-- The textbook logarithmic power series has derivative `1 / (1 + u)` on the open unit disk. -/
theorem logarithmic_power_series_hasDerivAt (u : ℂ) (hu : ‖u‖ < 1) :
    HasDerivAt Complex.logarithmicPowerSeries (1 / (1 + u)) u := by
  have hEq :
      Complex.logarithmicPowerSeries =ᶠ[𝓝 u] fun z : ℂ ↦ Complex.log (1 + z) := by
    filter_upwards [Metric.ball_mem_nhds u (sub_pos.mpr hu)] with z hz
    have hz' : ‖z‖ < 1 := by
      have hzdist : ‖z - u‖ < 1 - ‖u‖ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hnorm : ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
        calc
          ‖z‖ = ‖(z - u) + u‖ := by congr 1; ring
          _ ≤ ‖z - u‖ + ‖u‖ := norm_add_le _ _
      have : ‖z‖ < (1 - ‖u‖) + ‖u‖ := by
        refine lt_of_le_of_lt hnorm ?_
        simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right hzdist ‖u‖
      simpa using this
    exact logarithmic_power_series_tsum_eq z hz'
  have hlog : HasDerivAt (fun z : ℂ ↦ Complex.log (1 + z)) (1 / (1 + u)) u := by
    simpa using
      (HasDerivAt.clog ((hasDerivAt_id u).const_add 1) (Complex.mem_slitPlane_of_norm_lt_one hu))
  exact hlog.congr_of_eventuallyEq hEq

-- Proof sketch: apply `HasDerivAt.deriv` to `logarithmic_power_series_hasDerivAt u hu`.
/-- Remark I.3-extra-10: the derivative of the logarithmic power series
`T(u) = ∑_{n ≥ 1} (-1)^(n - 1) u^n / n` is `1 / (1 + u)` on the open unit disk. -/
theorem logarithmic_power_series_deriv_eq (u : ℂ) (hu : ‖u‖ < 1) :
    deriv Complex.logarithmicPowerSeries u = 1 / (1 + u) := by
  exact (logarithmic_power_series_hasDerivAt u hu).deriv
