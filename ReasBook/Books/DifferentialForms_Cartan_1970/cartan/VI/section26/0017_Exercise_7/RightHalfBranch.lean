import DifferentialForms_Cartan_1970.cartan.VI.section26.«0017_Exercise_7».CassiniCore

open Metric Set ComplexOrder
open scoped ComplexConjugate

noncomputable section

/-- Helper for Exercise 7: the forward normalized square followed by disc uncentering stays on the
principal square-root slit plane on the right-half Cassini domain. -/
lemma discUncenter_normalized_square_mem_slitPlane_of_mem_rightHalf
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ}
    (hz : z ∈ cassiniOvalRightHalf a r) :
    discUncenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ))
        (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) ∈ Complex.slitPlane := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
  have hr_pos : 0 < r := lt_trans ha har
  have hc_pos : 0 < cR := by
    -- The Cassini center ratio is positive because `0 < a < r`.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- The ratio is strictly less than `1` because `a^2 < r^2`.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by nlinarith
    have hr_sq_pos : 0 < r ^ 2 := by positivity
    exact (div_lt_one hr_sq_pos).2 ha_sq_lt
  have hη_ball : η ∈ ball (0 : ℂ) 1 := by
    simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hz
  by_cases hηim : η.im = 0
  · -- On the real branch, the source route says the normalized coordinate stays to the right of
    -- `-cR`, so the uncentered Möbius image is a positive real.
    obtain ⟨hz_im, hη_re_lt⟩ := normalized_square_real_case_of_mem_rightHalf hz (by simpa [η] using hηim)
    have hnum_pos : 0 < η.re + cR := by
      nlinarith
    have hden_pos : 0 < 1 + cR * η.re := by
      nlinarith [hc_pos, hc_lt, hη_re_lt]
    have hηeq : η = (η.re : ℂ) := by
      apply Complex.ext <;> simp [hηim]
    have hEq :
        discUncenter (cR : ℂ) η = (((η.re + cR) / (1 + cR * η.re) : ℝ) : ℂ) := by
      -- With `Im η = 0`, the Möbius quotient is a positive real number.
      rw [hηeq]
      simp [discUncenter, discCenter, Complex.conj_ofReal, hden_pos.ne', div_eq_mul_inv]
    rw [show (((a ^ 2 / r ^ 2 : ℝ)) : ℂ) = (cR : ℂ) by simp [cR], show (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) = η by rfl]
    rw [hEq]
    exact Complex.ofReal_mem_slitPlane.2 (by exact div_pos hnum_pos hden_pos)
  · -- Off the real axis, the explicit imaginary-part formula keeps the image off the branch cut.
    have hden : 1 + (cR : ℂ) * η ≠ 0 := by
      have hc_norm : ‖(cR : ℂ)‖ < 1 := by
        simpa [abs_of_nonneg hc_pos.le] using hc_lt
      have hc_ball : (-(cR : ℂ)) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        simpa [norm_neg] using hc_norm
      simpa [η, cR, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc, Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hη_ball)
    have him_eq :
        (discUncenter (cR : ℂ) η).im =
          η.im * (1 - cR ^ 2) / ‖1 + (cR : ℂ) * η‖ ^ 2 :=
      discUncenter_im_of_real_center hc_pos hc_lt hη_ball
    have hnum_ne : η.im * (1 - cR ^ 2) ≠ 0 := by
      apply mul_ne_zero hηim
      nlinarith
    have hden_ne : ‖1 + (cR : ℂ) * η‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hden)
    rw [show (((a ^ 2 / r ^ 2 : ℝ)) : ℂ) = (cR : ℂ) by simp [cR], show (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) = η by rfl]
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_eq]
    exact div_ne_zero hnum_ne hden_ne

/-- Helper for Exercise 7: recentering a slit-plane point by a real disc automorphism stays on
the principal branch cut complement. -/
lemma add_real_discCenter_mem_slitPlane_of_mem_ball_and_slitPlane
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1) {Z : ℂ}
    (hZball : Z ∈ ball (0 : ℂ) 1) (hZslit : Z ∈ Complex.slitPlane) :
    ((c : ℂ) + discCenter (c : ℂ) Z) ∈ Complex.slitPlane := by
  by_cases hZim : Z.im = 0
  · -- On the real branch, the recentered point is a positive real.
    rw [Complex.mem_slitPlane_iff] at hZslit
    have hZre_pos : 0 < Z.re := by
      rcases hZslit with hZre | hZim'
      · exact hZre
      · exact False.elim (hZim' hZim)
    have hZnorm : ‖Z‖ < 1 := mem_ball_zero_iff.mp hZball
    have hZeq : Z = (Z.re : ℂ) := by
      apply Complex.ext <;> simp [hZim]
    have hZre_lt : Z.re < 1 := by
      have habs_lt : |Z.re| < 1 := by
        rw [hZeq] at hZnorm
        simpa using hZnorm
      exact (abs_lt.mp habs_lt).2
    have hden_pos : 0 < 1 - c * Z.re := by
      nlinarith [hc_pos, hc_lt, hZre_lt]
    have hnum_pos : 0 < Z.re * (1 - c ^ 2) := by
      have : 0 < 1 - c ^ 2 := by nlinarith
      exact mul_pos hZre_pos this
    have hc_norm : ‖(c : ℂ)‖ < 1 := by
      simpa [abs_of_nonneg hc_pos.le] using hc_lt
    have hden : 1 - (c : ℂ) * Z ≠ 0 := by
      have hc_ball : ((c : ℂ)) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        exact hc_norm
      simpa [Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hZball)
    have hEq :
        ((c : ℂ) + discCenter (c : ℂ) Z) =
          (((Z.re * (1 - c ^ 2) / (1 - c * Z.re) : ℝ)) : ℂ) := by
      -- After exposing the affine factor, everything is real because `Im Z = 0`.
      rw [add_real_discCenter_eq_mul_ofReal_div hden]
      rw [hZeq]
      simp [Complex.conj_ofReal, hden_pos.ne', div_eq_mul_inv]
      ring_nf
    rw [hEq]
    exact Complex.ofReal_mem_slitPlane.2 (by exact div_pos hnum_pos hden_pos)
  · -- Off the real axis, the explicit imaginary-part formula shows the image stays off the cut.
    have him_eq :
        (((c : ℂ) + discCenter (c : ℂ) Z).im) =
          Z.im * (1 - c ^ 2) / ‖1 - (c : ℂ) * Z‖ ^ 2 :=
      add_real_discCenter_im_of_mem_ball hc_pos hc_lt hZball
    have hc_norm : ‖(c : ℂ)‖ < 1 := by
      simpa [abs_of_nonneg hc_pos.le] using hc_lt
    have hc_ball : ((c : ℂ)) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      exact hc_norm
    have hden : 1 - (c : ℂ) * Z ≠ 0 := by
      simpa [Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hZball)
    have hnum_ne : Z.im * (1 - c ^ 2) ≠ 0 := by
      apply mul_ne_zero hZim
      nlinarith
    have hden_ne : ‖1 - (c : ℂ) * Z‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hden)
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_eq]
    exact div_ne_zero hnum_ne hden_ne

/-- Helper for Exercise 7: the principal square root of a slit-plane point has positive real
part. -/
lemma sqrt_re_pos_of_mem_slitPlane
    {Z : ℂ} (hZ : Z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt Z).re := by
  have hsum_pos : 0 < ‖Z‖ + Z.re := by
    -- Either `Re Z > 0`, or the nonzero imaginary part makes the norm strictly larger than
    -- `|Re Z|`.
    rw [Complex.mem_slitPlane_iff] at hZ
    rcases hZ with hZre | hZim
    · nlinarith [norm_nonneg Z, hZre]
    · have hRe_lt : |Z.re| < ‖Z‖ := (Complex.abs_re_lt_norm).2 hZim
      have hleft : -‖Z‖ < Z.re := (abs_lt.mp hRe_lt).1
      nlinarith
  have hRe_sqrt : (Complex.sqrt Z).re = Real.sqrt ((‖Z‖ + Z.re) / 2) := by
    -- The principal branch always takes the nonnegative real square-root formula.
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp
  rw [hRe_sqrt]
  have harg_pos : 0 < (‖Z‖ + Z.re) / 2 := by nlinarith
  exact Real.sqrt_pos.mpr harg_pos

/-- Helper for Exercise 7: a slit-plane-valued analytic map has an analytic principal square
root. -/
lemma analyticOnNhd_sqrt_of_mapsTo_slitPlane
    {s : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s)
    (hslit : Set.MapsTo f s Complex.slitPlane) :
    AnalyticOnNhd ℂ (fun z ↦ Complex.sqrt (f z)) s := by
  -- Rewrite `sqrt` as the principal half-power and use the slit-plane branch condition.
  simpa [Complex.sqrt] using
    hf.cpow (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ (2⁻¹ : ℂ)) s)
      (by
        intro z hz
        exact hslit hz)

/-- Helper for Exercise 7: the forward square-root argument is holomorphic on the right-half
Cassini domain and stays on the principal slit plane there. -/
lemma cassini_forward_argument_analyticOnNhd
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (fun z ↦ cassiniOvalMobius a r (z ^ 2)) (cassiniOvalRightHalf a r) ∧
      Set.MapsTo (fun z ↦ cassiniOvalMobius a r (z ^ 2))
        (cassiniOvalRightHalf a r) Complex.slitPlane := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  have hr_pos : 0 < r := lt_trans ha har
  have hr : r ≠ 0 := ne_of_gt hr_pos
  have hc_pos : 0 < cR := by
    -- The normalized center is positive because `0 < a < r`.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- The same normalization lies strictly inside the unit disc.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by
      nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_norm : ‖c‖ < 1 := by
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hc_norm
  have hη_diff :
      DifferentiableOn ℂ
        (fun z : ℂ ↦ ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)))
        (cassiniOvalRightHalf a r) := by
    intro z hz
    -- The normalized square coordinate is a polynomial divided by a nonzero constant.
    let _ := hz
    fun_prop
  have hη_analytic :
      AnalyticOnNhd ℂ
        (fun z : ℂ ↦ ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)))
        (cassiniOvalRightHalf a r) :=
    (Complex.analyticOnNhd_iff_differentiableOn (isOpen_cassiniOvalRightHalf a r)).2 hη_diff
  have hη_maps :
      Set.MapsTo
        (fun z : ℂ ↦ ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)))
        (cassiniOvalRightHalf a r) (ball (0 : ℂ) 1) := by
    intro z hz
    simpa using normalized_square_mem_unit_ball_of_mem_rightHalf hz
  have hdisc_analytic : AnalyticOnNhd ℂ (discUncenter c) (ball (0 : ℂ) 1) := by
    exact
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
        (disc_uncenter_differentiableOn hc_ball)
  have hraw_analytic :
      AnalyticOnNhd ℂ
        (fun z ↦ discUncenter c (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))))
        (cassiniOvalRightHalf a r) := by
    -- Compose the normalized square coordinate with the disc automorphism.
    exact hdisc_analytic.comp hη_analytic hη_maps
  refine ⟨?_, ?_⟩
  · -- Replace the normalized disc-automorphism expression with the source Möbius formula.
    convert hraw_analytic using 1
    ext z
    simpa [c, cR] using cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)
  · intro z hz
    -- The slit-plane image has already been established for the normalized source route.
    have hEq := cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)
    simpa [hEq, c, cR] using
      (discUncenter_normalized_square_mem_slitPlane_of_mem_rightHalf ha har hz :
        discUncenter c (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) ∈ Complex.slitPlane)

/-- Helper for Exercise 7: the inverse square-root argument is holomorphic on the right half-disc
and stays on the principal slit plane there. -/
lemma cassini_inverse_argument_analyticOnNhd
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc ∧
      Set.MapsTo
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc Complex.slitPlane := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  have hr_pos : 0 < r := lt_trans ha har
  have hr : r ≠ 0 := ne_of_gt hr_pos
  have hc_pos : 0 < cR := by
    -- The normalized center is the same positive ratio as in the forward branch.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- It remains strictly inside the unit disc.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by
      nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_norm : ‖c‖ < 1 := by
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hc_norm
  have hraw_diff :
      DifferentiableOn ℂ
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc := by
    intro w hw
    obtain ⟨hw_sq_ball, _⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
    have hnum_diff :
        DifferentiableAt ℂ (fun w : ℂ ↦ (((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2)) w := by
      fun_prop
    have hden_diff :
        DifferentiableAt ℂ (fun w : ℂ ↦ ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2) w := by
      fun_prop
    have hden_ne :
        ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2 ≠ 0 :=
      unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
    exact (hnum_diff.div hden_diff hden_ne).differentiableWithinAt
  have hraw_analytic :
      AnalyticOnNhd ℂ
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_rightHalfUnitDisc).2 hraw_diff
  refine ⟨hraw_analytic, ?_⟩
  intro w hw
  change
    ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) ∈
      Complex.slitPlane
  obtain ⟨hw_sq_ball, hw_sq_slit⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
  have hcenter_slit : (c + discCenter c (w ^ 2)) ∈ Complex.slitPlane := by
    simpa [c] using
      add_real_discCenter_mem_slitPlane_of_mem_ball_and_slitPlane hc_pos hc_lt
        hw_sq_ball hw_sq_slit
  have hden :
      ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2) ≠ 0 :=
    unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
  have hc_eq : ((r : ℂ) ^ 2) * c = (a : ℂ) ^ 2 := by
    -- The affine source coordinate uses the same disc-center parameter `c`.
    dsimp [c, cR]
    have hr_sq_ne : r ^ 2 ≠ 0 := by
      positivity
    have hreal : r ^ 2 * (a ^ 2 / r ^ 2) = a ^ 2 := by
      field_simp [hr_sq_ne]
    simpa using congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
  have hraw_eq :
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
        ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
    -- Rewrite the raw inverse expression to the affine disc-center form from the source route.
    calc
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
          (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
        simpa [c, cR] using
          unitDiscToCassiniOval_sq_arg_eq_affine_discCenter
            (a := a) (r := r) hr (Z := w ^ 2) hden
      _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
        calc
          (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) =
              ((r : ℂ) ^ 2) * c + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
            rw [hc_eq]
          _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
            ring
  have hscale_slit :
      (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) ∈ Complex.slitPlane :=
    mul_ofReal_mem_slitPlane_of_pos (x := r ^ 2) (by positivity) hcenter_slit
  have hcast :
      ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) =
        (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) := by
    simp
  have hscaled_slit :
      ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) ∈ Complex.slitPlane := by
    simpa [hcast] using hscale_slit
  exact hraw_eq.symm ▸ hscaled_slit

/-- Helper for Exercise 7: on the open right half-plane, equality of squares already determines
the principal square-root branch. -/
lemma eq_of_sq_eq_sq_of_re_pos
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hsq : u ^ 2 = v ^ 2) :
    u = v := by
  -- Factor the difference of squares to reduce to the two possible square roots.
  have hfactor : (u - v) * (u + v) = 0 := by
    calc
      (u - v) * (u + v) = u ^ 2 - v ^ 2 := by ring
      _ = 0 := by rw [hsq, sub_self]
  rcases mul_eq_zero.mp hfactor with hsub | hadd
  · exact sub_eq_zero.mp hsub
  · have hre : u.re + v.re = 0 := by
      simpa using congrArg Complex.re hadd
    linarith

/-- Helper for Exercise 7: the auxiliary Möbius map sends the Cassini imaginary-axis segment to
the real interval `[-1, 0]`. -/
lemma cassiniOvalMobius_mem_nonpos_real_unitSegment_of_mem_imaginaryAxisSegment
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ}
    (hz : z ∈ cassiniOvalImaginaryAxisSegment a r) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ cassiniOvalMobius a r (z ^ 2) = -((t : ℂ)) := by
  rcases mem_cassiniOvalImaginaryAxisSegment.mp hz with ⟨hz_re, hz_bound⟩
  let y : ℝ := z.im
  have hr_pos : 0 < r := lt_trans ha har
  have hz_eq : z = Complex.I * y := by
    -- A point on the imaginary axis is exactly `I * y` with `y = Im z`.
    apply Complex.ext <;> simp [y, hz_re]
  have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hden_pos : 0 < r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := by
    -- The interval hypothesis `y^2 ≤ r^2 - a^2` keeps the Möbius denominator positive.
    have hlower : r ^ 2 * (r ^ 2 - a ^ 2) ≤ r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := by
      nlinarith [hz_bound]
    have hbase : 0 < r ^ 2 * (r ^ 2 - a ^ 2) := by
      have hgap : 0 < r ^ 2 - a ^ 2 := by
        nlinarith [ha, har]
      positivity
    nlinarith
  let t : ℝ := (r ^ 2 * y ^ 2) / (r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2)
  have ht_nonneg : 0 ≤ t := by
    -- Both numerator and denominator are nonnegative, with positive denominator.
    dsimp [t]
    positivity
  have ht_le_one : t ≤ 1 := by
    -- After clearing the positive denominator, this is exactly `y^2 ≤ r^2 - a^2`.
    dsimp [t]
    have hden_nonneg : 0 ≤ r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := le_of_lt hden_pos
    have hmul :
        r ^ 2 * y ^ 2 ≤ r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := by
      nlinarith [hz_bound, hy_sq_nonneg, ha, har]
    exact (div_le_one hden_pos).2 hmul
  refine ⟨t, ht_nonneg, ht_le_one, ?_⟩
  have hz_sq : z ^ 2 = -((y ^ 2 : ℝ) : ℂ) := by
    -- Squaring `I * y` sends the imaginary-axis segment to the negative real axis.
    rw [hz_eq]
    calc
      (Complex.I * (y : ℂ)) ^ 2 = Complex.I ^ 2 * ((y : ℂ) ^ 2) := by
        ring
      _ = -((y ^ 2 : ℝ) : ℂ) := by
        simp [pow_two]
  have hden_ne : (((r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hden_pos
  -- Evaluate the Möbius quotient explicitly on the negative real square.
  calc
    cassiniOvalMobius a r (z ^ 2) =
        ((-((r ^ 2 * y ^ 2 : ℝ) : ℂ)) /
          (((r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 : ℝ) : ℂ))) := by
      rw [cassiniOvalMobius, hz_sq]
      simp [pow_two]
      ring
    _ = -((t : ℂ)) := by
      simp [t, div_eq_mul_inv]

/-- The right-half construction in the source: for `0 < a < r`, the explicit map
`z ↦ sqrt ((r^2 z^2) / (a^2 z^2 + r^4 - a^4))` is a biholomorphic isomorphism from `D⁺` onto
`B⁺`, takes real values on the real axis, and maps the boundary segment `iy`, `y^2 ≤ r^2 - a^2`,
onto the segment `iv`, `|v| ≤ 1`. -/
theorem cassiniOvalToUnitDisc_right_half_isomorphism
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    -- Route correction: the package theorem must follow the source chain `z ↦ z^2`, Möbius
    -- normalization in the `ζ`-plane, then the principal square-root branch on the slit plane.
    AnalyticOnNhd ℂ (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) ∧
      Set.MapsTo (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) rightHalfUnitDisc ∧
      AnalyticOnNhd ℂ (unitDiscToCassiniOval a r) rightHalfUnitDisc ∧
      Set.MapsTo (unitDiscToCassiniOval a r) rightHalfUnitDisc (cassiniOvalRightHalf a r) ∧
      Set.EqOn
        ((unitDiscToCassiniOval a r) ∘ (cassiniOvalToUnitDisc a r))
        id (cassiniOvalRightHalf a r) ∧
      Set.EqOn
        ((cassiniOvalToUnitDisc a r) ∘ (unitDiscToCassiniOval a r))
        id rightHalfUnitDisc ∧
      Set.MapsTo (cassiniOvalToUnitDisc a r)
        {z | z ∈ cassiniOvalRightHalf a r ∧ z.im = 0}
        {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} ∧
      Set.MapsTo (cassiniOvalToUnitDisc a r)
        (cassiniOvalImaginaryAxisSegment a r)
        unitDiscImaginaryAxisSegment := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  have hr_pos : 0 < r := lt_trans ha har
  have hr : r ≠ 0 := ne_of_gt hr_pos
  have hc_pos : 0 < cR := by
    -- The disc-automorphism center is the source ratio `a^2 / r^2`.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- The center lies strictly inside the unit disc because `a < r`.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_norm : ‖c‖ < 1 := by
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hc_norm
  have h_forward_maps :
      Set.MapsTo (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) rightHalfUnitDisc := by
    intro z hz
    let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
    have hη_ball : η ∈ ball (0 : ℂ) 1 := by
      simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hz
    have hmobius_ball : cassiniOvalMobius a r (z ^ 2) ∈ ball (0 : ℂ) 1 := by
      -- The source Möbius normalization is exactly the uncentered disc automorphism on `η`.
      rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)]
      simpa [c, cR, η] using (disc_uncenter_mapsTo_unit_ball hc_ball hη_ball)
    have hmobius_slit : cassiniOvalMobius a r (z ^ 2) ∈ Complex.slitPlane := by
      -- The new forward branch lemma puts the square-root argument on the principal branch.
      rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)]
      simpa [c, cR, η] using
        (discUncenter_normalized_square_mem_slitPlane_of_mem_rightHalf ha har hz)
    exact sqrt_mem_rightHalfUnitDisc_of_mem_ball_and_slitPlane hmobius_ball hmobius_slit
  have h_inverse_maps :
      Set.MapsTo (unitDiscToCassiniOval a r) rightHalfUnitDisc (cassiniOvalRightHalf a r) := by
    intro w hw
    obtain ⟨hw_sq_ball, hw_sq_slit⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
    have hcenter_ball : discCenter c (w ^ 2) ∈ ball (0 : ℂ) 1 :=
      disc_center_mapsTo_unit_ball hc_ball hw_sq_ball
    have hcenter_slit : (c + discCenter c (w ^ 2)) ∈ Complex.slitPlane := by
      simpa [c] using
        (add_real_discCenter_mem_slitPlane_of_mem_ball_and_slitPlane hc_pos hc_lt
          hw_sq_ball hw_sq_slit)
    have hden :
        ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2) ≠ 0 :=
      unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
    have hc_eq : ((r : ℂ) ^ 2) * c = (a : ℂ) ^ 2 := by
      -- This identifies the affine `a^2` term with the same disc center `c`.
      dsimp [c, cR]
      have hr_sq_ne : r ^ 2 ≠ 0 := by positivity
      have hreal : r ^ 2 * (a ^ 2 / r ^ 2) = a ^ 2 := by
        field_simp [hr_sq_ne]
      simpa using congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
    have hraw_eq :
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
          ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
      -- Route correction: rewrite the inverse square-root argument to the affine disc-center form.
      calc
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
            (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
          simpa [c, cR] using
            (unitDiscToCassiniOval_sq_arg_eq_affine_discCenter
              (a := a) (r := r) hr (Z := w ^ 2) hden)
        _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
          calc
            (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) =
                ((r : ℂ) ^ 2) * c + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
              rw [hc_eq]
            _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
              ring
    have hraw_slit :
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) ∈
          Complex.slitPlane := by
      have hscale_slit :
          (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) ∈ Complex.slitPlane :=
        mul_ofReal_mem_slitPlane_of_pos (x := r ^ 2) (by positivity) hcenter_slit
      rw [hraw_eq]
      rw [show ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) =
          (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) by simp]
      exact hscale_slit
    have hre_pos : 0 < (unitDiscToCassiniOval a r w).re := by
      -- The inverse branch keeps positive real part because its square-root argument is on the
      -- slit plane.
      unfold unitDiscToCassiniOval
      simpa using sqrt_re_pos_of_mem_slitPlane hraw_slit
    have hnormalized_ball :
        (((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) ∈ ball (0 : ℂ) 1 := by
      rw [normalized_square_unitDiscToCassiniOval_eq_discCenter_sq ha har hw]
      exact hcenter_ball
    have hCassini : unitDiscToCassiniOval a r w ∈ cassiniOvalInterior a r :=
      mem_cassiniOvalInterior_of_normalized_square_mem_ball hr_pos hnormalized_ball
    exact ⟨hCassini, hre_pos⟩
  refine ⟨?_, h_forward_maps, ?_, h_inverse_maps, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hraw_analytic, hraw_slit⟩ := cassini_forward_argument_analyticOnNhd ha har
    -- Apply the principal square-root branch to the forward slit-plane-valued argument.
    simpa [cassiniOvalToUnitDisc] using
      analyticOnNhd_sqrt_of_mapsTo_slitPlane hraw_analytic hraw_slit
  · obtain ⟨hraw_analytic, hraw_slit⟩ := cassini_inverse_argument_analyticOnNhd ha har
    -- The inverse branch is the same slit-plane square-root package for the solved square.
    change
      AnalyticOnNhd ℂ
        (fun w ↦ Complex.sqrt
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc
    exact analyticOnNhd_sqrt_of_mapsTo_slitPlane hraw_analytic hraw_slit
  · intro z hz
    have hzCassini : z ∈ cassiniOvalInterior a r := (mem_cassiniOvalRightHalf.mp hz).1
    have hw : cassiniOvalToUnitDisc a r z ∈ rightHalfUnitDisc := h_forward_maps hz
    have hu :
        unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z) ∈ cassiniOvalRightHalf a r :=
      h_inverse_maps hw
    let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
    have hη_ball : η ∈ ball (0 : ℂ) 1 := by
      simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hz
    have hnormalized :
        (((unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2) /
            ((r : ℂ) ^ 2)) = η := by
      -- Both branches have the same normalized square coordinate.
      calc
        (((unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2) /
            ((r : ℂ) ^ 2)) =
            discCenter c ((cassiniOvalToUnitDisc a r z) ^ 2) := by
          simpa [c, cR] using normalized_square_unitDiscToCassiniOval_eq_discCenter_sq ha har hw
        _ = discCenter c (cassiniOvalMobius a r (z ^ 2)) := by
          rw [cassiniOvalToUnitDisc_sq hzCassini]
        _ = discCenter c (discUncenter c η) := by
          simpa [η, c, cR] using
            congrArg (fun ξ : ℂ ↦ discCenter c ξ)
              (cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2))
        _ = η := by
          simpa [η] using discCenter_discUncenter_eq_self_on_unit_ball hc_ball hη_ball
    have hR : ((r : ℂ) ^ 2) ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast hr)
    have hsub :
        (unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2 =
          z ^ 2 - (a : ℂ) ^ 2 := by
      calc
        (unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2 =
            ((((unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2) /
                ((r : ℂ) ^ 2)) * ((r : ℂ) ^ 2)) := by
          field_simp [hR]
        _ = η * ((r : ℂ) ^ 2) := by
          exact congrArg (fun x : ℂ ↦ x * ((r : ℂ) ^ 2)) hnormalized
        _ = z ^ 2 - (a : ℂ) ^ 2 := by
          dsimp [η]
          field_simp [hR]
    have hsq :
        (unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 = z ^ 2 := by
      have hadd := congrArg (fun x : ℂ ↦ x + (a : ℂ) ^ 2) hsub
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hadd
    -- Positive real parts force the correct square-root branch.
    exact
      eq_of_sq_eq_sq_of_re_pos
        (mem_cassiniOvalRightHalf.mp hu).2
        (mem_cassiniOvalRightHalf.mp hz).2
        hsq
  · intro w hw
    have hz : unitDiscToCassiniOval a r w ∈ cassiniOvalRightHalf a r := h_inverse_maps hw
    obtain ⟨hw_sq_ball, _⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
    have hsq :
        (cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w)) ^ 2 = w ^ 2 := by
      -- Normalize through the disc automorphism inverse relation on `w^2`.
      calc
        (cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w)) ^ 2 =
            cassiniOvalMobius a r ((unitDiscToCassiniOval a r w) ^ 2) := by
          exact cassiniOvalToUnitDisc_sq (a := a) (r := r) (z := unitDiscToCassiniOval a r w)
            (mem_cassiniOvalRightHalf.mp hz).1
        _ = discUncenter c
              ((((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) := by
          rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr
            ((unitDiscToCassiniOval a r w) ^ 2)]
        _ = discUncenter c (discCenter c (w ^ 2)) := by
          rw [normalized_square_unitDiscToCassiniOval_eq_discCenter_sq ha har hw]
        _ = w ^ 2 := by
          simpa [c, cR] using
            (disc_uncenter_leftInvOn_disc_center (a := c) hc_ball hw_sq_ball)
    have hw_image : cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w) ∈ rightHalfUnitDisc :=
      h_forward_maps hz
    -- Positive real parts again select the principal branch.
    exact
      eq_of_sq_eq_sq_of_re_pos
        (mem_rightHalfUnitDisc.mp hw_image).2
        (mem_rightHalfUnitDisc.mp hw).2
        hsq
  · intro z hz
    rcases hz with ⟨hzRight, hz_im⟩
    have hw : cassiniOvalToUnitDisc a r z ∈ rightHalfUnitDisc := h_forward_maps hzRight
    let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
    have hη_ball : η ∈ ball (0 : ℂ) 1 := by
      simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hzRight
    have hη_im : η.im = 0 := by
      -- On the real slice, the normalized square remains real.
      dsimp [η]
      rw [show ((r : ℂ) ^ 2) = (((r ^ 2 : ℝ) : ℂ)) by simp]
      simp [Complex.div_im, pow_two, hz_im]
    have hmobius_im : (cassiniOvalMobius a r (z ^ 2)).im = 0 := by
      -- The real-center disc automorphism preserves the real axis.
      rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)]
      rw [discUncenter_im_of_real_center hc_pos hc_lt hη_ball, hη_im]
      simp [η, c, cR]
    have hw_sq_im : ((cassiniOvalToUnitDisc a r z) ^ 2).im = 0 := by
      rw [cassiniOvalToUnitDisc_sq (a := a) (r := r) (z := z)
        ((mem_cassiniOvalRightHalf.mp hzRight).1), hmobius_im]
    have hw_re : 0 < (cassiniOvalToUnitDisc a r z).re := (mem_rightHalfUnitDisc.mp hw).2
    have hmul :
        2 * (cassiniOvalToUnitDisc a r z).re * (cassiniOvalToUnitDisc a r z).im = 0 := by
      have hsq_im_formula :
          ((cassiniOvalToUnitDisc a r z) ^ 2).im =
            2 * (cassiniOvalToUnitDisc a r z).re * (cassiniOvalToUnitDisc a r z).im := by
        simp [pow_two]
        ring
      rw [hsq_im_formula] at hw_sq_im
      exact hw_sq_im
    have hfactor : 2 * (cassiniOvalToUnitDisc a r z).re ≠ 0 := by
      nlinarith
    refine ⟨hw, ?_⟩
    exact mul_eq_zero.mp hmul |>.resolve_left hfactor
  · intro z hz
    rcases
      cassiniOvalMobius_mem_nonpos_real_unitSegment_of_mem_imaginaryAxisSegment ha har hz with
      ⟨t, ht_nonneg, ht_le_one, harg⟩
    have hnonneg : 0 ≤ ((t : ℝ) : ℂ) := by
      exact_mod_cast ht_nonneg
    have hsqrt_nonneg : Complex.sqrt ((t : ℝ) : ℂ) = (Real.sqrt t : ℂ) := by
      simpa using Complex.sqrt_of_nonneg hnonneg
    have hw_re_zero : (cassiniOvalToUnitDisc a r z).re = 0 := by
      -- On `[-1, 0]`, the principal square root lands on the imaginary axis.
      unfold cassiniOvalToUnitDisc
      rw [harg, Complex.sqrt_neg_of_nonneg hnonneg, hsqrt_nonneg]
      simp
    have hw_sq : cassiniOvalToUnitDisc a r z ^ 2 = -((t : ℂ)) := by
      -- Squaring the principal square root returns the interval parameter.
      unfold cassiniOvalToUnitDisc
      rw [sq_sqrt_complex, harg]
    have hnorm_sq : ‖cassiniOvalToUnitDisc a r z‖ ^ 2 = t := by
      have hnorm := congrArg norm hw_sq
      simpa [norm_pow, abs_of_nonneg ht_nonneg] using hnorm
    refine ⟨hw_re_zero, ?_⟩
    nlinarith [norm_nonneg (cassiniOvalToUnitDisc a r z), ht_nonneg, ht_le_one, hnorm_sq]

/-- The explicit map and its inverse define the canonical holomorphic isomorphism between the
right half of Cassini's oval and the right half of the unit disc. -/
noncomputable def cassiniOvalRightHalfIso {a r : ℝ} (ha : 0 < a) (har : a < r) :
    HolomorphicIsomorph (cassiniOvalRightHalf a r) rightHalfUnitDisc := by
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨h_toFun, h_mapsTo, h_invFun, h_invMapsTo, h_left, h_right, _, _⟩
  refine ⟨
    { toPartialEquiv :=
        { toFun := cassiniOvalToUnitDisc a r
          invFun := unitDiscToCassiniOval a r
          source := cassiniOvalRightHalf a r
          target := rightHalfUnitDisc
          map_source' := h_mapsTo
          map_target' := h_invMapsTo
          left_inv' := h_left
          right_inv' := h_right }
      open_source := isOpen_cassiniOvalRightHalf a r
      open_target := isOpen_rightHalfUnitDisc
      continuousOn_toFun := h_toFun.continuousOn
      continuousOn_invFun := h_invFun.continuousOn },
    ⟨rfl, rfl, h_toFun, h_invFun⟩⟩

@[simp] theorem cassiniOvalRightHalfIso_toFun {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ((cassiniOvalRightHalfIso ha har).1 : ℂ → ℂ) = cassiniOvalToUnitDisc a r := by
  -- This is the defining `toFun` field of the packaged right-half isomorphism.
  unfold cassiniOvalRightHalfIso
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨h_toFun, h_mapsTo, h_invFun, h_invMapsTo, h_left, h_right, h_real, h_imag⟩
  rfl

/-- On the right-half source, the canonical holomorphic isomorphism sends the real slice to the
real slice of the right half-disc. -/
theorem cassiniOvalRightHalfIso_mapsTo_realSlice
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo ((cassiniOvalRightHalfIso ha har).1 : ℂ → ℂ)
      {z | z ∈ cassiniOvalRightHalf a r ∧ z.im = 0}
      {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} := by
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, h_real, _⟩
  simpa using h_real

/-- On the right-half source, the canonical holomorphic isomorphism sends the Cassini imaginary
axis segment to the unit-disc imaginary axis segment. -/
theorem cassiniOvalRightHalfIso_mapsTo_imaginaryAxis
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo ((cassiniOvalRightHalfIso ha har).1 : ℂ → ℂ)
      (cassiniOvalImaginaryAxisSegment a r)
      unitDiscImaginaryAxisSegment := by
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, _, h_imag⟩
  simpa using h_imag

/-- Exercise 7, explicit branch: for `0 < a < r`, the map
`z ↦ sqrt ((r^2 z^2) / (a^2 z^2 + r^4 - a^4))` is the right-half branch from the source hint.
It is not a global map on the whole Cassini oval, since the displayed formula depends on `z^2`. -/
theorem cassiniOvalToUnitDisc_isomorphism_analytic
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) := by
  -- This is the first component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨h_analytic, _, _, _, _, _, _, _⟩
  exact h_analytic

/-- Exercise 7, explicit branch: the right-half branch maps `D⁺` into `B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_mapsTo
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) rightHalfUnitDisc :=
    by
  -- This is the second component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, h_mapsTo, _, _, _, _, _, _⟩
  exact h_mapsTo

/-- Exercise 7, explicit branch: the right-half inverse is analytic on `B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_inv_analytic
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (unitDiscToCassiniOval a r) rightHalfUnitDisc := by
  -- This is the third component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, h_inv_analytic, _, _, _, _, _⟩
  exact h_inv_analytic

/-- Exercise 7, explicit branch: the right-half inverse maps `B⁺` back into `D⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_inv_mapsTo
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (unitDiscToCassiniOval a r) rightHalfUnitDisc (cassiniOvalRightHalf a r) :=
    by
  -- This is the fourth component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, h_inv_mapsTo, _, _, _, _⟩
  exact h_inv_mapsTo

/-- Exercise 7, explicit branch: composing the inverse with the forward map gives the identity on
the right half `D⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_left_inv
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.EqOn
      ((unitDiscToCassiniOval a r) ∘ (cassiniOvalToUnitDisc a r))
      id (cassiniOvalRightHalf a r) := by
  -- This is the left-inverse component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, h_left, _, _, _⟩
  exact h_left

/-- Exercise 7, explicit branch: composing the forward map with the inverse gives the identity on
the right half-disc `B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_right_inv
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.EqOn
      ((cassiniOvalToUnitDisc a r) ∘ (unitDiscToCassiniOval a r))
      id rightHalfUnitDisc := by
  -- This is the right-inverse component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, h_right, _, _⟩
  exact h_right

/-- The explicit map and its inverse define the canonical holomorphic isomorphism between the
right half of Cassini's oval and the right half of the open unit disc. -/
noncomputable def cassiniOvalIso {a r : ℝ} (ha : 0 < a) (har : a < r) :
    HolomorphicIsomorph (cassiniOvalRightHalf a r) rightHalfUnitDisc := by
  refine ⟨
    { toPartialEquiv :=
        { toFun := cassiniOvalToUnitDisc a r
          invFun := unitDiscToCassiniOval a r
          source := cassiniOvalRightHalf a r
          target := rightHalfUnitDisc
          map_source' := cassiniOvalToUnitDisc_isomorphism_mapsTo ha har
          map_target' := cassiniOvalToUnitDisc_isomorphism_inv_mapsTo ha har
          left_inv' := cassiniOvalToUnitDisc_isomorphism_left_inv ha har
          right_inv' := cassiniOvalToUnitDisc_isomorphism_right_inv ha har }
      open_source := isOpen_cassiniOvalRightHalf a r
      open_target := isOpen_rightHalfUnitDisc
      continuousOn_toFun := (cassiniOvalToUnitDisc_isomorphism_analytic ha har).continuousOn
      continuousOn_invFun := (cassiniOvalToUnitDisc_isomorphism_inv_analytic ha har).continuousOn },
    ⟨rfl, rfl,
      cassiniOvalToUnitDisc_isomorphism_analytic ha har,
      cassiniOvalToUnitDisc_isomorphism_inv_analytic ha har⟩⟩

/-- Exercise 7, explicit branch: the map sends the real slice of `D⁺` into the real slice of
`B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_real_slice
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (cassiniOvalToUnitDisc a r)
      {z | z ∈ cassiniOvalRightHalf a r ∧ z.im = 0}
      {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} := by
  -- This is the real-slice component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, h_real, _⟩
  exact h_real

/-- Exercise 7, explicit branch: the limiting boundary branch sends the Cassini imaginary-axis
segment into the unit-disc imaginary-axis segment. -/
theorem cassiniOvalToUnitDisc_isomorphism_imaginary_axis
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (cassiniOvalToUnitDisc a r)
      (cassiniOvalImaginaryAxisSegment a r)
      unitDiscImaginaryAxisSegment := by
  -- This is the imaginary-axis component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, _, h_imag⟩
  exact h_imag

end
