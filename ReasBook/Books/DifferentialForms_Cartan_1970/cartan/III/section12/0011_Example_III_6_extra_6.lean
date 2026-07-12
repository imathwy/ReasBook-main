import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- Helper for Example III.6-extra-6: the map `t ↦ t / (1 - t)` sends `(0, 1)` onto `(0, ∞)`. -/
lemma unit_fraction_image_Ioo :
    (fun t : ℝ ↦ t / (1 - t)) '' Set.Ioo (0 : ℝ) 1 = Set.Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    -- Positivity of the numerator and denominator keeps the image in `(0, ∞)`.
    exact div_pos ht.1 (sub_pos.mpr ht.2)
  · intro hx
    have hx0 : 0 < x := hx
    refine ⟨x / (1 + x), ?_, ?_⟩
    constructor
    · have h1x : 0 < 1 + x := by linarith
      exact div_pos hx0 h1x
    · have h1x : 0 < 1 + x := by linarith
      exact (div_lt_one h1x).2 (by linarith)
    -- The explicit inverse is `x ↦ x / (1 + x)`.
    have h1x : (1 : ℝ) + x ≠ 0 := by linarith
    field_simp [h1x]
    ring

/-- Helper for Example III.6-extra-6: on `(0, 1)`, the derivative of `t ↦ t / (1 - t)` is
`1 / (1 - t)^2`. -/
lemma hasDerivWithinAt_unit_fraction {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun s : ℝ ↦ s / (1 - s)) (1 / (1 - t) ^ 2) (Set.Ioo (0 : ℝ) 1) t := by
  have hne : 1 - t ≠ 0 := sub_ne_zero.mpr ht.2.ne'
  have hden_deriv : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
    simpa using (hasDerivAt_const t 1).sub (hasDerivAt_id t)
  -- Differentiate the fractional-linear map first, then normalize the scalar derivative.
  have hderiv :
      HasDerivAt (fun s : ℝ ↦ s / (1 - s))
        (((1 : ℝ) * (1 - t) - t * (-1)) / (1 - t) ^ 2) t := by
    exact (hasDerivAt_id t).div hden_deriv hne
  have hsimpl :
      (((1 : ℝ) * (1 - t) - t * (-1)) / (1 - t) ^ 2) = 1 / (1 - t) ^ 2 := by
    ring_nf
  exact hsimpl ▸ hderiv.hasDerivWithinAt

/-- Helper for Example III.6-extra-6: the map `t ↦ t / (1 - t)` is strictly increasing on
`(0, 1)`. -/
lemma strictMonoOn_unit_fraction :
    StrictMonoOn (fun t : ℝ ↦ t / (1 - t)) (Set.Ioo (0 : ℝ) 1) := by
  -- A positive derivative on the open interval gives the monotonicity needed for substitution.
  refine strictMonoOn_of_hasDerivWithinAt_pos (D := Set.Ioo (0 : ℝ) 1)
    (f' := fun t ↦ 1 / (1 - t) ^ 2) (convex_Ioo (0 : ℝ) 1) ?_ ?_ ?_
  · intro t ht
    exact (hasDerivWithinAt_unit_fraction ht).continuousWithinAt
  · simpa [interior_Ioo] using fun t ht ↦ hasDerivWithinAt_unit_fraction ht
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using ht
    have hpos : 0 < 1 - t := sub_pos.mpr ht'.2
    positivity

/-- Helper for Example III.6-extra-6: after the substitution `x = t / (1 - t)`, the Jacobian and
the rational kernel simplify to `(1 - t) * (log t - log (1 - t))`. -/
lemma fractional_substitution_integrand {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) *
        (Real.log (t / (1 - t)) / (1 + t / (1 - t)) ^ 3) =
      (1 - t) * (Real.log t - Real.log (1 - t)) := by
  have hden : 1 - t ≠ 0 := sub_ne_zero.mpr ht.2.ne'
  have hlog :
      Real.log (t / (1 - t)) = Real.log t - Real.log (1 - t) := by
    rw [Real.log_div ht.1.ne' hden]
  have hone :
      1 + t / (1 - t) = 1 / (1 - t) := by
    field_simp [hden]
    ring
  -- Once the logarithm and denominator are normalized, clearing denominators finishes the step.
  rw [hlog, hone]
  field_simp [hden]

/-- Helper for Example III.6-extra-6: the moment `∫_0^1 t log t` is `-1 / 4`. -/
lemma integral_mul_log_unitInterval :
    ∫ t in (0 : ℝ)..1, t * Real.log t = -1 / 4 := by
  let prim : ℝ → ℝ := fun t ↦ t * (t * Real.log t) / 2 - t ^ 2 / 4
  have hprim_cont : Continuous prim := by
    -- Writing the primitive via `t * log t` keeps continuity at `0` explicit.
    have hsq : Continuous fun t : ℝ ↦ t ^ 2 / 4 := by
      simpa [pow_two] using (continuous_id.mul continuous_id).div_const (4 : ℝ)
    simpa [prim] using ((continuous_id.mul Real.continuous_mul_log).div_const (2 : ℝ)).sub hsq
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := prim) (fa := 0) (fb := -((4 : ℝ)⁻¹))
    (hint := Real.continuous_mul_log.intervalIntegrable (a := (0 : ℝ)) (b := 1))]
  · ring
  · norm_num
  · intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hmul_log : HasDerivAt (fun t : ℝ ↦ t * Real.log t) (Real.log x + 1) x := by
      simpa using Real.hasDerivAt_mul_log hx0
    have hfirst :
        HasDerivAt (fun t : ℝ ↦ t * (t * Real.log t) / 2)
          ((x * Real.log x + x * (Real.log x + 1)) / 2) x := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id x).mul hmul_log).div_const (2 : ℝ)
    have hsquare :
        HasDerivAt (fun t : ℝ ↦ t ^ 2 / 4) ((2 * x) / 4) x := by
      simpa [pow_two, two_mul, div_eq_mul_inv, mul_assoc] using
        ((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const (4 : ℝ)
    -- The derivative of the primitive collapses exactly to `x * log x`.
    convert hfirst.sub hsquare using 1
    ring
  · have hcont0 : ContinuousAt prim 0 := hprim_cont.continuousAt
    have hlim0 :
        Filter.Tendsto prim (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (prim 0)) :=
      hcont0.tendsto.mono_left nhdsWithin_le_nhds
    simpa [prim] using hlim0
  · have hcont1 : ContinuousAt prim 1 := hprim_cont.continuousAt
    have hlim1 :
        Filter.Tendsto prim (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (prim 1)) :=
      hcont1.tendsto.mono_left nhdsWithin_le_nhds
    simpa [prim] using hlim1

/-- Helper for Example III.6-extra-6: the transformed logarithmic kernel on `(0, 1)` integrates to
`-1 / 2`. -/
lemma integral_transformed_log_kernel_unitInterval :
    ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t) * (Real.log t - Real.log (1 - t)) ∂volume = -1 / 2 := by
  have hmul_log :
      IntervalIntegrable (fun t : ℝ ↦ t * Real.log t) volume (0 : ℝ) 1 :=
    Real.continuous_mul_log.intervalIntegrable (a := (0 : ℝ)) (b := 1)
  have hone_sub_log :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * Real.log (1 - t)) volume (0 : ℝ) 1 := by
    have hcont : Continuous fun t : ℝ ↦ (1 - t) * Real.log (1 - t) := by
      simpa using Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
    exact hcont.intervalIntegrable (a := (0 : ℝ)) (b := 1)
  have hlog_sub :
      IntervalIntegrable (fun t : ℝ ↦ Real.log t - t * Real.log t) volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'.sub hmul_log
  have hrewrite :
      ∫ t in (0 : ℝ)..1, (1 - t) * (Real.log t - Real.log (1 - t)) =
        ∫ t in (0 : ℝ)..1, (Real.log t - t * Real.log t) - (1 - t) * Real.log (1 - t) := by
    -- Expand the transformed kernel into the three standard logarithmic moments.
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t
    intro _
    ring
  have hlog :
      ∫ t in (0 : ℝ)..1, Real.log t = -1 := by
    simpa using (intervalIntegral.integral_log (a := (0 : ℝ)) (b := 1))
  have hone_sub :
      ∫ t in (0 : ℝ)..1, (1 - t) * Real.log (1 - t) =
        ∫ t in (0 : ℝ)..1, t * Real.log t := by
    -- Reflecting `t ↦ t * log t` across `t = 1 / 2` identifies the last term with the same moment.
    simpa using
      (intervalIntegral.integral_comp_sub_left (f := fun t : ℝ ↦ t * Real.log t)
        (a := (0 : ℝ)) (b := 1) (d := 1))
  calc
    ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t) * (Real.log t - Real.log (1 - t)) ∂volume
        = ∫ t in Set.Icc (0 : ℝ) 1, (1 - t) * (Real.log t - Real.log (1 - t)) ∂volume := by
            rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
    _ = ∫ t in (0 : ℝ)..1, (1 - t) * (Real.log t - Real.log (1 - t)) := by
          rw [intervalIntegral.integral_of_le zero_le_one]
          rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ t in (0 : ℝ)..1, (Real.log t - t * Real.log t) - (1 - t) * Real.log (1 - t) := hrewrite
    _ = (∫ t in (0 : ℝ)..1, (Real.log t - t * Real.log t)) -
          ∫ t in (0 : ℝ)..1, (1 - t) * Real.log (1 - t) := by
            rw [intervalIntegral.integral_sub hlog_sub hone_sub_log]
    _ = ((∫ t in (0 : ℝ)..1, Real.log t) - ∫ t in (0 : ℝ)..1, t * Real.log t) -
          ∫ t in (0 : ℝ)..1, (1 - t) * Real.log (1 - t) := by
            rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log' hmul_log]
    _ = (-1 - (-1 / 4)) - (-1 / 4) := by
          rw [hlog, integral_mul_log_unitInterval, hone_sub, integral_mul_log_unitInterval]
    _ = -1 / 2 := by norm_num

/-- Example III.6-extra-6: the residue computation for
`z ↦ (Complex.log z) ^ 2 / (1 + z) ^ 3` yields
`∫_0^∞ log x / (1 + x)^3 dx = -1 / 2`. -/
theorem integral_log_div_one_add_pow_three :
    ∫ x in Set.Ioi (0 : ℝ), Real.log x / (1 + x) ^ 3 ∂volume = -1 / 2 := by
  -- The main route is the textbook substitution `x = t / (1 - t)` from `(0, 1)` to `(0, ∞)`.
  calc
    ∫ x in Set.Ioi (0 : ℝ), Real.log x / (1 + x) ^ 3 ∂volume
        = ∫ x in (fun t : ℝ ↦ t / (1 - t)) '' Set.Ioo (0 : ℝ) 1,
            Real.log x / (1 + x) ^ 3 ∂volume := by
              rw [unit_fraction_image_Ioo]
    _ = ∫ t in Set.Ioo (0 : ℝ) 1,
          (1 / (1 - t) ^ 2) *
            (Real.log (t / (1 - t)) / (1 + t / (1 - t)) ^ 3) ∂volume := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
              (s := Set.Ioo (0 : ℝ) 1)
              (f := fun t : ℝ ↦ t / (1 - t))
              (f' := fun t : ℝ ↦ 1 / (1 - t) ^ 2)
              measurableSet_Ioo
              (fun t ht ↦ hasDerivWithinAt_unit_fraction ht)
              strictMonoOn_unit_fraction.monotoneOn
              (fun x : ℝ ↦ Real.log x / (1 + x) ^ 3))
    _ = ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t) * (Real.log t - Real.log (1 - t)) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro t ht
          exact fractional_substitution_integrand ht
    _ = -1 / 2 := integral_transformed_log_kernel_unitInterval
