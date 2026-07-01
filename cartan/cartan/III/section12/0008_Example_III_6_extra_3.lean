import Mathlib
import cartan.III.section12.SectorArc

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool `lean_leansearch` was unavailable in this environment.

noncomputable section

open Filter MeasureTheory Set
open scoped Real Interval Topology

/-- Bridge from the textbook integrand to mathlib's canonical `Real.sinc` on each finite interval
`[0, r]` with `r > 0`. -/
theorem intervalIntegral_sin_div_eq_intervalIntegral_sinc {r : ℝ} (hr : 0 < r) :
    ∫ x in (0 : ℝ)..r, Real.sin x / x = ∫ x in (0 : ℝ)..r, Real.sinc x := by
  refine intervalIntegral.integral_congr_ae ?_
  refine ae_of_all _ fun x hx ↦ ?_
  have hx' : x ∈ Ioc (0 : ℝ) r := by
    simpa [uIoc_of_le hr.le] using hx
  rw [Real.sinc_of_ne_zero (ne_of_gt hx'.1)]

/-- Helper for Example III.6-extra-3: along the real axis, the exponential difference equals
`(2 i)` times the complex-valued `sinc` integral. -/
private lemma real_axis_difference_eq_two_I_mul_intervalIntegral_sinc {ε R : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) :
    (∫ t in ε..R, Complex.exp (Complex.I * t) / t) -
        ∫ t in ε..R, Complex.exp (-Complex.I * t) / t =
      (2 * Complex.I) * ∫ t in ε..R, (Real.sinc t : ℂ) := by
  have hInt_pos :
      IntervalIntegrable (fun t : ℝ ↦ Complex.exp (Complex.I * t) / t) MeasureTheory.volume ε R := by
    -- The positive real-axis integrand is continuous away from `0`, and `ε > 0` keeps the interval
    -- inside that regularity region.
    apply ContinuousOn.intervalIntegrable_of_Icc hεR
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t ht
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le hε ht.1))
  have hInt_neg :
      IntervalIntegrable (fun t : ℝ ↦ Complex.exp (-Complex.I * t) / t) MeasureTheory.volume ε R := by
    -- The same continuity argument applies to the conjugate exponential.
    apply ContinuousOn.intervalIntegrable_of_Icc hεR
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t ht
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le hε ht.1))
  calc
    (∫ t in ε..R, Complex.exp (Complex.I * t) / t) -
        ∫ t in ε..R, Complex.exp (-Complex.I * t) / t
      = ∫ t in ε..R,
          (Complex.exp (Complex.I * t) / t - Complex.exp (-Complex.I * t) / t) := by
            rw [← intervalIntegral.integral_sub hInt_pos hInt_neg]
    _ = ∫ t in ε..R, (2 * Complex.I) * (Real.sinc t : ℂ) := by
          -- On the positive interval, `sinc t = sin t / t`, so the exponential difference
          -- collapses to the usual `2 i sin t / t`.
          refine intervalIntegral.integral_congr ?_
          intro t ht
          have ht' : t ∈ Set.Icc ε R := by
            simpa [Set.uIcc_of_le hεR] using ht
          have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hε ht'.1)
          have ht0' : (t : ℂ) ≠ 0 := by
            exact_mod_cast ht0
          change
            Complex.exp (Complex.I * t) / t - Complex.exp (-Complex.I * t) / t =
              (2 * Complex.I) * (Real.sinc t : ℂ)
          rw [Real.sinc_of_ne_zero ht0]
          have hpos_mul : Complex.I * t = t * Complex.I := by ring
          have hneg_mul : -Complex.I * t = (-t) * Complex.I := by ring
          rw [hpos_mul, Complex.exp_mul_I, hneg_mul, Complex.exp_mul_I]
          simp [div_eq_mul_inv]
          field_simp [ht0']
          ring
    _ = (2 * Complex.I) * ∫ t in ε..R, (Real.sinc t : ℂ) := by
          rw [intervalIntegral.integral_const_mul]

/-- Helper for Example III.6-extra-3: the shrinking upper semicircle contributes `π i`. -/
private lemma small_semicircle_exp_div_tendsto_pi_I :
    Tendsto
      (fun ε : ℝ ↦ sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi * Complex.I)) := by
  let F : ℝ → ℝ → ℂ := fun ε θ ↦ Complex.I * Complex.exp (Complex.I * circleMap 0 ε θ)
  have hEq :
      (fun ε : ℝ ↦ sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun ε ↦ ∫ θ in (0 : ℝ)..Real.pi, F ε θ := by
    -- On the punctured neighborhood, the `z` factor from `sectorArcIntegral_def` cancels exactly.
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [sectorArcIntegral_def]
    refine intervalIntegral.integral_congr ?_
    intro θ hθ
    have hcircle : circleMap 0 ε θ ≠ 0 := circleMap_ne_center (c := 0) (R := ε) (θ := θ) hε.ne'
    dsimp [F]
    field_simp [hcircle]
  have hcont : Continuous F.uncurry := by
    -- The arc integrand is continuous jointly in radius and angle.
    fun_prop
  have hparam :
      Continuous fun ε : ℝ ↦ ∫ θ in (0 : ℝ)..Real.pi, F ε θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont 0 Real.pi
  have hlimit :
      Tendsto (fun ε : ℝ ↦ ∫ θ in (0 : ℝ)..Real.pi, F ε θ) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ θ in (0 : ℝ)..Real.pi, F 0 θ)) :=
    hparam.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine Tendsto.congr' hEq.symm ?_
  convert hlimit using 1
  -- Evaluate the limiting constant integrand.
  simp [F, intervalIntegral.integral_const]

/-- Helper for Example III.6-extra-3: on the upper semicircle, the damping integral
`∫_0^π exp (-r sin θ) r dθ` is bounded above by `π`. -/
private theorem exp_neg_sin_mul_intervalIntegral_le_pi
    {r : ℝ} (hr : 0 ≤ r) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-r * Real.sin θ) * r ≤ Real.pi := by
  let g : ℝ → ℝ := fun θ ↦ Real.exp (-r * Real.sin θ) * r
  have hg_cont : Continuous g := by
    -- The damping kernel is continuous on the whole semicircle.
    fun_prop
  have hg_int_left : IntervalIntegrable g MeasureTheory.volume 0 (Real.pi / 2) := by
    exact hg_cont.intervalIntegrable _ _
  have hg_int_right : IntervalIntegrable g MeasureTheory.volume (Real.pi / 2) Real.pi := by
    exact hg_cont.intervalIntegrable _ _
  have hsymm :
      ∫ θ in (Real.pi / 2)..Real.pi, g θ = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
    -- Reflect the second half of the interval using `θ ↦ π - θ`.
    calc
      ∫ θ in (Real.pi / 2)..Real.pi, g θ
          = ∫ θ in (Real.pi / 2)..Real.pi, g (Real.pi - θ) := by
              refine intervalIntegral.integral_congr_ae ?_
              filter_upwards with θ
              simp [g, Real.sin_pi_sub]
      _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
            have hpi_half : Real.pi - Real.pi / 2 = Real.pi / 2 := by
              ring
            rw [intervalIntegral.integral_comp_sub_left]
            simp [hpi_half]
  have hleft_bound : ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤ Real.pi / 2 := by
    have hcomparison_int :
        IntervalIntegrable
          (fun θ : ℝ ↦ Real.exp (-(2 / Real.pi * r) * θ) * r)
          MeasureTheory.volume
          0
          (Real.pi / 2) := by
      -- The comparison kernel is also continuous on the compact interval.
      have hcomparison_cont :
          Continuous (fun θ : ℝ ↦ Real.exp (-(2 / Real.pi * r) * θ) * r) := by
        fun_prop
      exact hcomparison_cont.intervalIntegrable _ _
    have hcomparison :
        ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤
          ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-(2 / Real.pi * r) * θ) * r := by
      -- Jordan's inequality gives the linear lower bound on `sin`.
      refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := Real.pi / 2)
        (by positivity) hg_int_left hcomparison_int ?_
      intro θ hθ
      have hsin : 2 / Real.pi * θ ≤ Real.sin θ :=
        Real.mul_le_sin hθ.1 hθ.2
      have hexp :
          Real.exp (-r * Real.sin θ) ≤ Real.exp (-(2 / Real.pi * r) * θ) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsin, hr]
      exact mul_le_mul_of_nonneg_right hexp hr
    rcases eq_or_lt_of_le hr with rfl | hrpos
    · simpa [g]
        using (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    · let c : ℝ := -(2 / Real.pi * r)
      have hc : c ≠ 0 := by
        dsimp [c]
        exact neg_ne_zero.mpr <| mul_ne_zero (div_ne_zero two_ne_zero Real.pi_ne_zero) hrpos.ne'
      have hc_pi : c * (Real.pi / 2) = -r := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
      have hrc : r * c⁻¹ = -(Real.pi / 2) := by
        dsimp [c]
        field_simp [Real.pi_ne_zero, hrpos.ne']
      calc
        ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ
            ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (c * θ) * r := by
                simpa [g, c] using hcomparison
        _ = r * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (c * θ) := by
              rw [intervalIntegral.integral_mul_const]
              ring
        _ = r * (c⁻¹ * ∫ x in c * (0 : ℝ)..c * (Real.pi / 2), Real.exp x) := by
              simpa [smul_eq_mul] using
                congrArg (fun x : ℝ => r * x)
                  (intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := (0 : ℝ))
                    (b := Real.pi / 2) (c := c) hc)
        _ = r * (c⁻¹ * (Real.exp (c * (Real.pi / 2)) - 1)) := by
              rw [integral_exp, mul_zero, Real.exp_zero]
        _ = Real.pi / 2 * (1 - Real.exp (-r)) := by
              rw [hc_pi]
              calc
                r * (c⁻¹ * (Real.exp (-r) - 1))
                    = (r * c⁻¹) * (Real.exp (-r) - 1) := by ring
                _ = -(Real.pi / 2) * (Real.exp (-r) - 1) := by rw [hrc]
                _ = Real.pi / 2 * (1 - Real.exp (-r)) := by ring
        _ ≤ Real.pi / 2 := by
              have hexp_nonneg : 0 ≤ Real.exp (-r) := Real.exp_nonneg (-r)
              nlinarith [Real.pi_pos]
  have hsplit :
      (∫ θ in (0 : ℝ)..(Real.pi / 2), g θ) + ∫ θ in (Real.pi / 2)..Real.pi, g θ =
        ∫ θ in (0 : ℝ)..Real.pi, g θ := by
    -- Split the upper semicircle into the two symmetric halves.
    simpa using intervalIntegral.integral_add_adjacent_intervals hg_int_left hg_int_right
  have hdouble :
      2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤ 2 * (Real.pi / 2) := by
    linarith [hleft_bound]
  let I : ℝ := ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ
  have hIbound : 2 * I ≤ 2 * (Real.pi / 2) := by
    simpa [I] using hdouble
  calc
    ∫ θ in (0 : ℝ)..Real.pi, g θ
        = I + ∫ θ in (Real.pi / 2)..Real.pi, g θ := by
            simpa [I] using hsplit.symm
    _ = I + I := by
          rw [hsymm]
    _ = 2 * I := by
          ring
    _ ≤ 2 * (Real.pi / 2) := hIbound
    _ = Real.pi := by ring

/-- Helper for Example III.6-extra-3: the contribution of the outer upper semicircle tends to
zero. -/
private lemma outer_semicircle_exp_div_tendsto_zero :
    Tendsto
      (fun R : ℝ ↦ sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi)
      atTop
      (nhds 0) := by
  have hbound :
      ∀ᶠ R : ℝ in atTop,
        ‖sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi‖ ≤ Real.pi / R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have harc_eq :
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi =
          ∫ θ in (0 : ℝ)..Real.pi, Complex.I * Complex.exp (Complex.I * circleMap 0 R θ) := by
      -- On a positive-radius arc, the denominator `z` cancels against the geometric `z` factor.
      rw [sectorArcIntegral_def]
      refine intervalIntegral.integral_congr ?_
      intro θ hθ
      have hne : circleMap 0 R θ ≠ 0 :=
        circleMap_ne_center (c := 0) (R := R) (θ := θ) hR.ne'
      change
        Complex.I * circleMap 0 R θ * (Complex.exp (Complex.I * circleMap 0 R θ) / circleMap 0 R θ) =
          Complex.I * Complex.exp (Complex.I * circleMap 0 R θ)
      rw [div_eq_mul_inv]
      calc
        Complex.I * circleMap 0 R θ *
            (Complex.exp (Complex.I * circleMap 0 R θ) * (circleMap 0 R θ)⁻¹)
            = Complex.I * (circleMap 0 R θ * (circleMap 0 R θ)⁻¹) *
                Complex.exp (Complex.I * circleMap 0 R θ) := by ring
        _ = Complex.I * Complex.exp (Complex.I * circleMap 0 R θ) := by
              simp [hne]
    have hnorm :
        ‖sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi‖ ≤
          ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-R * Real.sin θ) := by
      rw [harc_eq]
      calc
        ‖∫ θ in (0 : ℝ)..Real.pi, Complex.I * Complex.exp (Complex.I * circleMap 0 R θ)‖
            ≤ ∫ θ in (0 : ℝ)..Real.pi,
                ‖Complex.I * Complex.exp (Complex.I * circleMap 0 R θ)‖ := by
                  exact intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le
        _ = ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-R * Real.sin θ) := by
              refine intervalIntegral.integral_congr ?_
              intro θ hθ
              change
                ‖Complex.I * Complex.exp (Complex.I * circleMap 0 R θ)‖ =
                  Real.exp (-R * Real.sin θ)
              rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
              simp [circleMap_zero_im]
    have hkernel :
        ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-R * Real.sin θ) ≤ Real.pi / R := by
      have hJordan := exp_neg_sin_mul_intervalIntegral_le_pi (r := R) hR.le
      have hscaled :
          (∫ θ in (0 : ℝ)..Real.pi, Real.exp (-R * Real.sin θ)) * R ≤ Real.pi := by
        simpa [intervalIntegral.integral_mul_const, mul_comm, mul_left_comm, mul_assoc] using hJordan
      exact (le_div_iff₀ hR).2 hscaled
    exact hnorm.trans hkernel
  have hdecay : Tendsto (fun R : ℝ ↦ Real.pi / R) atTop (nhds 0) := by
    -- The scalar Jordan bound decays like `1 / R`.
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun R : ℝ ↦ Real.pi * R⁻¹) atTop (nhds (Real.pi * 0)))
  exact squeeze_zero_norm' hbound hdecay

/-- Helper for Example III.6-extra-3: after rewriting an edge point as a nonzero point on the
circle, the `z` factor from `sectorArcIntegral_def` cancels against the denominator. -/
private lemma circle_factor_cancel_exp_div {z : ℂ} (hz : z ≠ 0) :
    Complex.I * Complex.exp (Complex.I * z) =
      Complex.I * z * (Complex.exp (Complex.I * z) / z) := by
  -- Cancel the geometric circle factor before matching the sector-arc integrand.
  rw [div_eq_mul_inv]
  calc
    Complex.I * Complex.exp (Complex.I * z)
      = Complex.I * (Complex.exp (Complex.I * z) * (z * z⁻¹)) := by simp [hz]
    _ = Complex.I * z * (Complex.exp (Complex.I * z) * z⁻¹) := by ring
    _ = Complex.I * z * (Complex.exp (Complex.I * z) / z) := by rw [div_eq_mul_inv]

/-- Helper for Example III.6-extra-3: the lower horizontal edge of the logarithmic rectangle
becomes the positive real-axis exponential integral after the substitution `t = exp x`. -/
private lemma positive_log_edge_eq_exp_div {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ x in Real.log ε..Real.log R, Complex.exp (Complex.I * Complex.exp x)) =
      ∫ t in ε..R, Complex.exp (Complex.I * t) / t := by
  let g : ℝ → ℂ := fun t ↦ Complex.exp (Complex.I * t) / t
  have hR : 0 < R := lt_of_lt_of_le hε hεR
  have hderiv : ∀ x ∈ Set.uIcc (Real.log ε) (Real.log R), HasDerivAt Real.exp (Real.exp x) x := by
    intro x hx
    simpa using Real.hasDerivAt_exp x
  have hderiv_cont :
      ContinuousOn (fun x : ℝ ↦ Real.exp x) (Set.uIcc (Real.log ε) (Real.log R)) := by
    fun_prop
  have hg : ContinuousOn g (Real.exp '' [[Real.log ε, Real.log R]]) := by
    -- The positive lower edge stays away from the pole at `0`.
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t ht
      rcases ht with ⟨x, hx, rfl⟩
      exact_mod_cast (Real.exp_pos x).ne'
  calc
    (∫ x in Real.log ε..Real.log R, Complex.exp (Complex.I * Complex.exp x))
      = ∫ x in Real.log ε..Real.log R, Real.exp x • g (Real.exp x) := by
          -- Rewrite the integrand into the scalar-action shape expected by change of variables.
          refine intervalIntegral.integral_congr ?_
          intro x hx
          dsimp [g]
          rw [← Complex.ofReal_exp]
          calc
            Complex.exp (Complex.I * (Real.exp x : ℂ))
              = Complex.exp (Complex.I * (Real.exp x : ℂ)) *
                  ((Real.exp x : ℂ) * (Real.exp x : ℂ)⁻¹) := by simp
            _ = (Real.exp x : ℂ) *
                  (Complex.exp (Complex.I * (Real.exp x : ℂ)) / (Real.exp x : ℂ)) := by
                    rw [div_eq_mul_inv]
                    ring
    _ = ∫ t in Real.exp (Real.log ε)..Real.exp (Real.log R), g t := by
          -- Now apply the nonlinear substitution `t = exp x` on the finite interval.
          simpa using
            (intervalIntegral.integral_deriv_smul_comp' (a := Real.log ε) (b := Real.log R)
              (f := Real.exp) (f' := fun x : ℝ ↦ Real.exp x) (g := g)
              hderiv hderiv_cont hg)
    _ = ∫ t in ε..R, Complex.exp (Complex.I * t) / t := by
          simp [g, Real.exp_log, hε, hR]

/-- Helper for Example III.6-extra-3: the upper horizontal edge becomes the negative-frequency
real-axis exponential integral after the `π i` shift and the substitution `t = exp x`. -/
private lemma upper_log_edge_eq_exp_neg_div {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ x in Real.log ε..Real.log R,
      Complex.exp (Complex.I * Complex.exp ((x : ℂ) + Real.pi * Complex.I))) =
      ∫ t in ε..R, Complex.exp (-Complex.I * t) / t := by
  let g : ℝ → ℂ := fun t ↦ Complex.exp (-(Complex.I * t)) / t
  have hR : 0 < R := lt_of_lt_of_le hε hεR
  have hderiv : ∀ x ∈ Set.uIcc (Real.log ε) (Real.log R), HasDerivAt Real.exp (Real.exp x) x := by
    intro x hx
    simpa using Real.hasDerivAt_exp x
  have hderiv_cont :
      ContinuousOn (fun x : ℝ ↦ Real.exp x) (Set.uIcc (Real.log ε) (Real.log R)) := by
    fun_prop
  have hg : ContinuousOn g (Real.exp '' [[Real.log ε, Real.log R]]) := by
    -- The same punctured-interval continuity applies on the top edge.
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t ht
      rcases ht with ⟨x, hx, rfl⟩
      exact_mod_cast (Real.exp_pos x).ne'
  calc
    (∫ x in Real.log ε..Real.log R,
      Complex.exp (Complex.I * Complex.exp ((x : ℂ) + Real.pi * Complex.I)))
      = ∫ x in Real.log ε..Real.log R, Real.exp x • g (Real.exp x) := by
          -- First rewrite `exp (x + π i)` as `-exp x`, then put the integrand in substitution form.
          refine intervalIntegral.integral_congr ?_
          intro x hx
          dsimp [g]
          rw [Complex.exp_add_pi_mul_I, ← Complex.ofReal_exp]
          have hneg : Complex.I * (-(Real.exp x : ℂ)) = -(Complex.I * (Real.exp x : ℂ)) := by
            ring_nf
          rw [hneg]
          calc
            Complex.exp (-(Complex.I * (Real.exp x : ℂ)))
              = Complex.exp (-(Complex.I * (Real.exp x : ℂ))) *
                  ((Real.exp x : ℂ) * (Real.exp x : ℂ)⁻¹) := by simp
            _ = (Real.exp x : ℂ) *
                  (Complex.exp (-(Complex.I * (Real.exp x : ℂ))) / (Real.exp x : ℂ)) := by
                    rw [div_eq_mul_inv]
                    ring
    _ = ∫ t in Real.exp (Real.log ε)..Real.exp (Real.log R), g t := by
          -- Reuse the same `t = exp x` substitution after the `π i` shift rewrite.
          simpa using
            (intervalIntegral.integral_deriv_smul_comp' (a := Real.log ε) (b := Real.log R)
              (f := Real.exp) (f' := fun x : ℝ ↦ Real.exp x) (g := g)
              hderiv hderiv_cont hg)
    _ = ∫ t in ε..R, Complex.exp (-Complex.I * t) / t := by
          simp [g, neg_mul, Real.exp_log, hε, hR]

/-- Helper for Example III.6-extra-3: the two horizontal edges of the logarithmic rectangle match
the difference of the positive and negative real-axis integrals. -/
private lemma log_rectangle_horizontal_edges_eq_real_axis_difference {ε R : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ x in Real.log ε..Real.log R, Complex.exp (Complex.I * Complex.exp x)) -
      (∫ x in Real.log ε..Real.log R,
        Complex.exp (Complex.I * Complex.exp ((x : ℂ) + Real.pi * Complex.I))) =
      (∫ t in ε..R, Complex.exp (Complex.I * t) / t) -
        ∫ t in ε..R, Complex.exp (-Complex.I * t) / t := by
  -- Combine the two edge-by-edge substitution identities into the rectangle's horizontal term.
  rw [positive_log_edge_eq_exp_div hε hεR, upper_log_edge_eq_exp_neg_div hε hεR]

/-- Helper for Example III.6-extra-3: the two vertical edges of the logarithmic rectangle are the
outer and inner upper semicircular sector integrals. -/
private lemma log_rectangle_vertical_edges_eq_sector_arcs {ε R : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) :
    Complex.I • (∫ y in (0 : ℝ)..Real.pi,
      Complex.exp (Complex.I * Complex.exp ((Real.log R : ℂ) + y * Complex.I))) -
      Complex.I • (∫ y in (0 : ℝ)..Real.pi,
        Complex.exp (Complex.I * Complex.exp ((Real.log ε : ℂ) + y * Complex.I))) =
      sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi -
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi := by
  have hR : 0 < R := lt_of_lt_of_le hε hεR
  have houter :
      Complex.I • (∫ y in (0 : ℝ)..Real.pi,
        Complex.exp (Complex.I * Complex.exp ((Real.log R : ℂ) + y * Complex.I))) =
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul, sectorArcIntegral_def]
    refine intervalIntegral.integral_congr ?_
    intro y hy
    have hcircle : circleMap 0 R y ≠ 0 :=
      circleMap_ne_center (c := 0) (R := R) (θ := y) hR.ne'
    have hexp_circle : Complex.exp ((Real.log R : ℂ) + y * Complex.I) = circleMap 0 R y := by
      -- Rewrite the right vertical edge as the radius-`R` semicircle.
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hR, circleMap]
      simp
    calc
      Complex.I * Complex.exp (Complex.I * Complex.exp ((Real.log R : ℂ) + y * Complex.I))
        = Complex.I * Complex.exp (Complex.I * circleMap 0 R y) := by rw [hexp_circle]
      _ = Complex.I * circleMap 0 R y *
            (Complex.exp (Complex.I * circleMap 0 R y) / circleMap 0 R y) :=
          circle_factor_cancel_exp_div hcircle
  have hinner :
      Complex.I • (∫ y in (0 : ℝ)..Real.pi,
        Complex.exp (Complex.I * Complex.exp ((Real.log ε : ℂ) + y * Complex.I))) =
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul, sectorArcIntegral_def]
    refine intervalIntegral.integral_congr ?_
    intro y hy
    have hcircle : circleMap 0 ε y ≠ 0 :=
      circleMap_ne_center (c := 0) (R := ε) (θ := y) hε.ne'
    have hexp_circle : Complex.exp ((Real.log ε : ℂ) + y * Complex.I) = circleMap 0 ε y := by
      -- Rewrite the left vertical edge as the radius-`ε` semicircle.
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hε, circleMap]
      simp
    calc
      Complex.I * Complex.exp (Complex.I * Complex.exp ((Real.log ε : ℂ) + y * Complex.I))
        = Complex.I * Complex.exp (Complex.I * circleMap 0 ε y) := by rw [hexp_circle]
      _ = Complex.I * circleMap 0 ε y *
            (Complex.exp (Complex.I * circleMap 0 ε y) / circleMap 0 ε y) :=
          circle_factor_cancel_exp_div hcircle
  -- Replace the two vertical sides one at a time to obtain the sector-arc difference.
  rw [houter, hinner]

/-- Helper for Example III.6-extra-3: the upper-half semiannulus contour splits into the two real
axis segments and the two semicircular arcs. -/
private lemma semiannulus_boundary_identity {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ t in ε..R, Complex.exp (Complex.I * t) / t) -
        (∫ t in ε..R, Complex.exp (-Complex.I * t) / t) +
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi -
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi =
      0 := by
  -- Route correction: prove the finite log-rectangle identity edge-by-edge, then assemble it.
  let h : ℂ → ℂ := fun w ↦ Complex.exp (Complex.I * Complex.exp w)
  have hd : Differentiable ℂ h := by
    fun_prop
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn h
      ⟨Real.log ε, 0⟩ ⟨Real.log R, Real.pi⟩ hd.differentiableOn
  have hrect' :
      (∫ x : ℝ in Real.log ε..Real.log R, h x) -
          (∫ x : ℝ in Real.log ε..Real.log R, h ((x : ℂ) + Real.pi * Complex.I)) +
          Complex.I • (∫ y : ℝ in (0 : ℝ)..Real.pi, h ((Real.log R : ℂ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (0 : ℝ)..Real.pi, h ((Real.log ε : ℂ) + y * Complex.I)) =
        0 := by
    -- Expose the four rectangle edges in the exact source-proof order.
    simpa [h] using hrect
  rw [log_rectangle_horizontal_edges_eq_real_axis_difference hε hεR] at hrect'
  have hvertical := log_rectangle_vertical_edges_eq_sector_arcs hε hεR
  calc
    ((∫ t in ε..R, Complex.exp (Complex.I * t) / t) -
          ∫ t in ε..R, Complex.exp (-Complex.I * t) / t) +
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi -
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi
      = ((∫ t in ε..R, Complex.exp (Complex.I * t) / t) -
            ∫ t in ε..R, Complex.exp (-Complex.I * t) / t) +
          (Complex.I • (∫ y : ℝ in (0 : ℝ)..Real.pi, h ((Real.log R : ℂ) + y * Complex.I)) -
            Complex.I • (∫ y : ℝ in (0 : ℝ)..Real.pi, h ((Real.log ε : ℂ) + y * Complex.I))) := by
              rw [hvertical]
              ring
    _ = 0 := by
          -- The horizontal adapter and the rectangle theorem now match exactly.
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrect'

/-- Helper for Example III.6-extra-3: for fixed `R > 0`, the truncated `sinc` integral
`∫_ε^R sinc` converges to `∫_0^R sinc` as `ε → 0+`. -/
private lemma cutoff_intervalIntegral_sinc_tendsto_left_endpoint {R : ℝ} :
    Tendsto
      (fun ε : ℝ ↦ ∫ t in ε..R, ((Real.sinc t : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ))) := by
  let f : ℝ → ℂ := fun t ↦ ((Real.sinc t : ℝ) : ℂ)
  have hf_cont : Continuous f := by
    exact Complex.continuous_ofReal.comp Real.continuous_sinc
  have hf_int : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b
    exact hf_cont.intervalIntegrable _ _
  have hcont : Continuous fun ε : ℝ ↦ ∫ t in (0 : ℝ)..ε, f t :=
    intervalIntegral.continuous_primitive hf_int 0
  have hbase :
      Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..ε, f t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hbase0 :
        Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..ε, f t) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ t in (0 : ℝ)..(0 : ℝ), f t)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hbase0
  have hdecomp :
      ∀ ε : ℝ, (∫ t in ε..R, f t) = (∫ t in (0 : ℝ)..R, f t) - ∫ t in (0 : ℝ)..ε, f t := by
    intro ε
    calc
      ∫ t in ε..R, f t = (∫ t in ε..(0 : ℝ), f t) + ∫ t in (0 : ℝ)..R, f t := by
        symm
        have hAdj := intervalIntegral.integral_add_adjacent_intervals (hf_int ε 0) (hf_int 0 R)
        simpa using hAdj
      _ = (∫ t in (0 : ℝ)..R, f t) - ∫ t in (0 : ℝ)..ε, f t := by
        rw [intervalIntegral.integral_symm]
        ring
  have hsub :
      Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..R, f t) - ∫ t in (0 : ℝ)..ε, f t)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((∫ t in (0 : ℝ)..R, f t) - 0)) :=
    tendsto_const_nhds.sub hbase
  have hEq :
      (fun ε : ℝ ↦ ∫ t in ε..R, ((Real.sinc t : ℝ) : ℂ)) =
        (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..R, f t) - ∫ t in (0 : ℝ)..ε, f t) := by
    funext ε
    exact hdecomp ε
  rw [hEq]
  simpa using hsub

/-- Helper for Example III.6-extra-3: near `0+`, the rewritten semiannulus boundary identity is
exactly the constant zero function. -/
private lemma rewritten_boundary_eventually_eq_zero {R : ℝ} (hR : 0 < R) :
    (fun ε : ℝ ↦
      (2 * Complex.I) * (∫ t in ε..R, ((Real.sinc t : ℝ) : ℂ)) +
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi -
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi) =ᶠ[nhdsWithin
          0 (Set.Ioi 0)] fun _ ↦ (0 : ℂ) := by
  -- Near the left endpoint, the semiannulus identity applies with `ε < R`, so the rewritten
  -- boundary expression is literally zero.
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with ε hε hεR
  have hboundary := semiannulus_boundary_identity hε hεR.le
  -- Rewrite the real-axis pair into the `sinc` integral before comparing with the constant zero.
  rw [real_axis_difference_eq_two_I_mul_intervalIntegral_sinc hε hεR.le] at hboundary
  exact hboundary

/-- Helper for Example III.6-extra-3: the rewritten semiannulus boundary expression has the
expected `ε → 0+` limit for fixed outer radius. -/
private lemma fixed_radius_boundary_limit {R : ℝ} :
    Tendsto
      (fun ε : ℝ ↦
        (2 * Complex.I) * (∫ t in ε..R, ((Real.sinc t : ℝ) : ℂ)) +
          sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi -
          sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) ε 0 Real.pi)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)) +
            sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi) -
          Real.pi * Complex.I)) := by
  have hsinc :
      Tendsto
        (fun ε : ℝ ↦ ∫ t in ε..R, ((Real.sinc t : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ))) :=
    cutoff_intervalIntegral_sinc_tendsto_left_endpoint (R := R)
  have hscaled :
      Tendsto
        (fun ε : ℝ ↦ (2 * Complex.I) * (∫ t in ε..R, ((Real.sinc t : ℝ) : ℂ)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)))) :=
    tendsto_const_nhds.mul hsinc
  have hsum :
      Tendsto
        (fun ε : ℝ ↦
          (2 * Complex.I) * (∫ t in ε..R, ((Real.sinc t : ℝ) : ℂ)) +
            sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          ((2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)) +
            sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi)) :=
    hscaled.add tendsto_const_nhds
  -- Package the three source-proof limits into one limit for the rewritten boundary expression.
  simpa using hsum.sub small_semicircle_exp_div_tendsto_pi_I

/-- Helper for Example III.6-extra-3: fixing the outer radius and then sending the inner radius to
`0` yields the stabilized `sinc` identity. -/
private lemma fixed_radius_sinc_identity {R : ℝ} (hR : 0 < R) :
    (2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)) +
        sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi =
      Real.pi * Complex.I := by
  -- Route correction: compare the packaged `ε → 0+` limit with the eventually-zero rewritten
  -- boundary identity instead of redoing the contour algebra inside the closing lemma.
  have hzero :
      (((2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)) +
          sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi) -
        Real.pi * Complex.I) = 0 := by
    -- Uniqueness of limits identifies the packaged boundary limit with the constant zero limit.
    exact tendsto_nhds_unique_of_eventuallyEq
      (fixed_radius_boundary_limit (R := R)) tendsto_const_nhds
      (rewritten_boundary_eventually_eq_zero hR)
  exact sub_eq_zero.mp hzero

/-- Example III.6-extra-3: the improper Dirichlet integral satisfies
`∫_0^∞ (sin x / x) dx = π / 2`. -/
theorem tendsto_intervalIntegral_sin_div_eq_pi_half :
    Tendsto (fun r : ℝ ↦ ∫ x in (0 : ℝ)..r, Real.sin x / x) atTop (nhds (Real.pi / 2)) := by
  have hsinc :
      Tendsto (fun r : ℝ ↦ ∫ x in (0 : ℝ)..r, Real.sinc x) atTop (nhds (Real.pi / 2)) := by
    -- Route correction: isolate the finite-radius contour identity first, then use the already
    -- separated outer-arc decay instead of mixing contour algebra with the final limit extraction.
    have hcomplex :
        Tendsto
          (fun R : ℝ ↦
            (2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)))
          atTop
          (nhds (Real.pi * Complex.I)) := by
      have hrhs :
          Tendsto
            (fun R : ℝ ↦
              Real.pi * Complex.I -
                sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi)
            atTop
            (nhds (Real.pi * Complex.I - 0)) :=
        tendsto_const_nhds.sub outer_semicircle_exp_div_tendsto_zero
      have hcomplex' :
          Tendsto
            (fun R : ℝ ↦
              (2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)))
            atTop
            (nhds (Real.pi * Complex.I - 0)) := by
        refine hrhs.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        calc
          Real.pi * Complex.I -
              sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi
            =
              ((2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)) +
                sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi) -
                sectorArcIntegral (fun z ↦ Complex.exp (Complex.I * z) / z) R 0 Real.pi := by
                  rw [fixed_radius_sinc_identity hR]
          _ = (2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ)) := by
                ring_nf
      simpa using hcomplex'
    have hdouble :
        Tendsto (fun R : ℝ ↦ 2 * ∫ t in (0 : ℝ)..R, Real.sinc t) atTop (nhds Real.pi) := by
      have him :
          Tendsto
            (fun R : ℝ ↦
              Complex.im ((2 * Complex.I) * (∫ t in (0 : ℝ)..R, ((Real.sinc t : ℝ) : ℂ))))
            atTop
            (nhds (Complex.im (Real.pi * Complex.I))) :=
        Complex.continuous_im.continuousAt.tendsto.comp hcomplex
      convert him using 1
      · ext R
        rw [intervalIntegral.integral_ofReal]
        simp
      · simp
    have hhalf :
        Tendsto
          (fun R : ℝ ↦ (1 / 2 : ℝ) * (2 * ∫ t in (0 : ℝ)..R, Real.sinc t))
          atTop
          (nhds ((1 / 2 : ℝ) * Real.pi)) :=
      tendsto_const_nhds.mul hdouble
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hhalf
  have hEq :
      (fun r : ℝ ↦ ∫ x in (0 : ℝ)..r, Real.sin x / x) =ᶠ[atTop]
        fun r ↦ ∫ x in (0 : ℝ)..r, Real.sinc x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact intervalIntegral_sin_div_eq_intervalIntegral_sinc hr
  exact Tendsto.congr' hEq.symm hsinc
