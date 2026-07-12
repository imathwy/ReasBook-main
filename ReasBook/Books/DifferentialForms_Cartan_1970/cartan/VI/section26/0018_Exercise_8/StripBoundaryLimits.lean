import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».RightTopStripBoundary

open Set
open scoped UpperHalfPlane ComplexOrder

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: dividing a positive-strip point by its real part
sends it to the inner strip with real part `1`, and this normalization tends to the anchor point
`1` along any approach through `Im w > 0` and `1 ≤ Re w`. -/
lemma exercise8_rescaleByRealPart_tendsto_innerOne
    {x : ℝ} {s : Set ℂ} (hx : 1 ≤ x)
    (hs : ∀ ⦃w : ℂ⦄, w ∈ s → 0 < w.im ∧ 1 ≤ w.re) :
    Filter.Tendsto (fun w : ℂ ↦ ((((w.re)⁻¹ : ℝ) : ℂ) * w))
      (nhdsWithin (x : ℂ) s)
      (nhdsWithin (1 : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}) := by
  let g : ℂ → ℂ := fun w ↦ ((((w.re)⁻¹ : ℝ) : ℂ) * w)
  have hx_pos : 0 < x := by
    linarith
  have hg_cont : ContinuousAt g (x : ℂ) := by
    have hre : ContinuousAt (fun w : ℂ ↦ w.re) (x : ℂ) := Complex.continuous_re.continuousAt
    have hre_inv_real : ContinuousAt (fun w : ℂ ↦ (w.re)⁻¹) (x : ℂ) := hre.inv₀ hx_pos.ne'
    have hre_inv : ContinuousAt (fun w : ℂ ↦ (((w.re)⁻¹ : ℝ) : ℂ)) (x : ℂ) :=
      Complex.continuous_ofReal.continuousAt.comp hre_inv_real
    -- The rescaling map is a continuous coefficient times the identity map.
    simpa [g] using hre_inv.mul continuousAt_id
  have hg_tendsto : Filter.Tendsto g (nhdsWithin (x : ℂ) s) (nhds (1 : ℂ)) := by
    have hg_tendsto_center := (hg_cont.continuousWithinAt (s := s)).tendsto
    have hx_eval : g (x : ℂ) = 1 := by
      simp [g, hx_pos.ne']
    -- At the real anchor point `x`, the normalization is exactly `1`.
    simpa [hx_eval] using hg_tendsto_center
  have hg_within :
      ∀ᶠ w in nhdsWithin (x : ℂ) s,
        g w ∈ {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1} := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    rcases hs hw with ⟨hwim, hwre_ge⟩
    have hwre_pos : 0 < w.re := by
      linarith
    constructor
    · have him : (g w).im = w.im * w.re⁻¹ := by
        simp [g, Complex.mul_im, mul_comm]
      -- Positive imaginary part survives the normalization because `Re w > 0`.
      rw [him]
      exact mul_pos hwim (inv_pos.2 hwre_pos)
    · constructor
      · have hre : (g w).re = 1 := by
          simp [g, Complex.mul_re, hwre_pos.ne']
        linarith [hre]
      · have hre : (g w).re = 1 := by
          simp [g, Complex.mul_re, hwre_pos.ne']
        linarith [hre]
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within g hg_tendsto hg_within

/-- Helper for Cartan section26 0018_Exercise_8: the common horizontal anchor segment from
`Im w * I` to `1 + Im w * I` converges to the real period `K`. This is the `x = 1` inner-strip
limit reused by both the right-strip and top-strip assembly proofs. -/
lemma exercise8_anchorHorizontal_tendsto_completeRealPeriod
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
      (fun w : ℂ ↦
        ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) ((1 : ℂ) + (w.im : ℂ) * Complex.I),
          (exercise8_integrand k dz) z)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re})
      (nhds (exercise8_complete_real_period k)) := by
  let strip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re}
  let innerStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}
  let g : ℂ → ℂ := fun w ↦ (1 : ℂ) + (w.im : ℂ) * Complex.I
  have hg_tendsto : Filter.Tendsto g (nhdsWithin (x : ℂ) strip) (nhds (1 : ℂ)) := by
    have hg_cont : Continuous g := by
      simpa [g] using continuous_const.add
        ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)
    have hg_tendsto_center :=
      ((hg_cont.continuousAt : ContinuousAt g (x : ℂ)).continuousWithinAt (s := strip)).tendsto
    -- The anchor map forgets the real coordinate, so it tends to `1 + 0 * I = 1`.
    simpa [g, strip] using hg_tendsto_center
  have hg_within : ∀ᶠ w in nhdsWithin (x : ℂ) strip, g w ∈ innerStrip := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    constructor
    · simpa [g] using hw.1
    · constructor
      · simp [g]
      · simp [g]
  have hg_inner : Filter.Tendsto g (nhdsWithin (x : ℂ) strip) (nhdsWithin (1 : ℂ) innerStrip) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within g hg_tendsto hg_within
  have hinner :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment (((g w).im : ℂ) * Complex.I) (g w), (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) strip)
        (nhds (exercise8_complete_real_period k)) := by
    have hbase :=
      (exercise8_horizontalSegment_tendsto_innerBranch k (x := 1) (by norm_num) le_rfl).comp
        hg_inner
    have htarget : exercise8_boundary_inner_branch k 1 = exercise8_complete_real_period k := by
      calc
        exercise8_boundary_inner_branch k 1 = exercise8_boundary_value k 1 := by
          symm
          simpa [exercise8_boundary_inner_branch] using
            exercise8_boundary_value_eq_inner (k := k) (x := 1) ⟨by norm_num, by norm_num⟩
        _ = exercise8_complete_real_period k := by
          simpa using exercise8_boundary_value_one k
    -- The inner-strip theorem at `x = 1` already gives the desired anchor value `K`.
    simpa [htarget] using hbase
  refine Filter.Tendsto.congr' ?_ hinner
  filter_upwards [self_mem_nhdsWithin] with w hw
  have him : (g w).im = w.im := by
    simp [g]
  -- Rewrite the composed inner-strip segment back to the explicit anchor segment.
  rw [him]

/-- Helper for Cartan section26 0018_Exercise_8: after normalizing a right-strip point by its real
part, the exact scaled-residual identity from the Abel-integral core transports the solved
inner-strip residual limit to the whole closed right strip. -/
lemma exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_rightStrip
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    Filter.Tendsto
      (fun w : ℂ ↦
        exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
      (nhds 0) := by
  let rightStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)}
  let innerStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}
  let g : ℂ → ℂ := fun w ↦ ((((w.re)⁻¹ : ℝ) : ℂ) * w)
  let residual : ℂ → ℂ := fun w ↦
    exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
      ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z
  have hrescale :
      Filter.Tendsto g (nhdsWithin (x : ℂ) rightStrip) (nhdsWithin (1 : ℂ) innerStrip) :=
    exercise8_rescaleByRealPart_tendsto_innerOne hx.1
      (fun hw hs ↦ ⟨hs.1, hs.2.1⟩)
  have hinner :
      Filter.Tendsto (fun w : ℂ ↦ residual (g w))
        (nhdsWithin (x : ℂ) rightStrip) (nhds 0) := by
    -- The inner-strip residual theorem now applies after the `Re w` normalization tends to `1`.
    exact
      (exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_innerStrip
        k (x := 1) ⟨by norm_num, by norm_num⟩).comp hrescale
  refine Filter.Tendsto.congr' ?_ hinner
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwim : 0 < w.im := hw.1
  have hwre_ge : 1 ≤ w.re := hw.2.1
  have hwre_pos : 0 < w.re := by linarith
  have hInv_le_one : w.re⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hwre_ge
  let u : UpperHalfPlane := UpperHalfPlane.ofComplex w
  have hu_coe : ((u : UpperHalfPlane) : ℂ) = w := by
    simpa [u] using
      congrArg (fun z : UpperHalfPlane ↦ (z : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos hwim)
  have hu_coe_im : ((u : UpperHalfPlane) : ℂ).im = w.im := by
    simpa [hu_coe]
  have hu_im : u.im = w.im := by
    simpa using hu_coe_im
  have hg_coe : g w = ((((w.re)⁻¹ : ℝ) : ℂ) * (u : ℂ)) := by
    simp [g, hu_coe]
  have hg_im : (g w).im = w.re⁻¹ * u.im := by
    calc
      (g w).im = (((((w.re)⁻¹ : ℝ) : ℂ) * (u : ℂ))).im := by rw [hg_coe]
      _ = w.re⁻¹ * u.im := by
        simp [Complex.mul_im]
  have hrewrite_raw :=
    exercise8_abel_integral_sub_verticalLift_sub_horizontal_eq_scaledResidual
      k u (r := w.re⁻¹) (inv_pos.2 hwre_pos) hInv_le_one
  -- Rewrite the scaled residual owner to the explicit normalization `g w`.
  convert hrewrite_raw.symm using 1
  · change
      exercise8_abel_integral k (UpperHalfPlane.ofComplex (g w)) -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (((g w).im : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment (((g w).im : ℂ) * Complex.I) (g w), (exercise8_integrand k dz) z =
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((((w.re)⁻¹ : ℝ) : ℂ) * (u : ℂ))) -
          exercise8_abel_integral k
            (UpperHalfPlane.ofComplex ((((w.re⁻¹ * u.im : ℝ) : ℂ) * Complex.I))) -
        ∫ᶜ z in Path.segment ((((w.re⁻¹ * u.im : ℝ) : ℂ) * Complex.I))
            ((((w.re)⁻¹ : ℝ) : ℂ) * (u : ℂ)),
          (exercise8_integrand k dz) z
    rw [hg_im, hg_coe]
  · change
      exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z =
      exercise8_abel_integral k u -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((((u : UpperHalfPlane) : ℂ).im : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment ((((u : UpperHalfPlane) : ℂ).im : ℂ) * Complex.I) (u : ℂ),
          (exercise8_integrand k dz) z
    rw [hu_coe_im, hu_coe]

/-- Helper for Cartan section26 0018_Exercise_8: the same scaled-residual normalization used on
the right strip also pushes the Abel-integral residual to `0` on the whole closed top strip. -/
lemma exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_topStrip
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    Filter.Tendsto
      (fun w : ℂ ↦
        exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
      (nhds 0) := by
  let topStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}
  let innerStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}
  let g : ℂ → ℂ := fun w ↦ ((((w.re)⁻¹ : ℝ) : ℂ) * w)
  let residual : ℂ → ℂ := fun w ↦
    exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
      ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z
  have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using
      (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hx_ge_one : 1 ≤ x := hk_inv_gt_one.le.trans hx
  have hrescale :
      Filter.Tendsto g (nhdsWithin (x : ℂ) topStrip) (nhdsWithin (1 : ℂ) innerStrip) :=
    exercise8_rescaleByRealPart_tendsto_innerOne hx_ge_one
      (fun hw hs ↦ ⟨hs.1, hk_inv_gt_one.le.trans hs.2⟩)
  have hinner :
      Filter.Tendsto (fun w : ℂ ↦ residual (g w))
        (nhdsWithin (x : ℂ) topStrip) (nhds 0) := by
    -- The inner-strip residual theorem applies once `Re w` is normalized to `1`.
    exact
      (exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_innerStrip
        k (x := 1) ⟨by norm_num, by norm_num⟩).comp hrescale
  refine Filter.Tendsto.congr' ?_ hinner
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwim : 0 < w.im := hw.1
  have hwre_ge : 1 ≤ w.re := hk_inv_gt_one.le.trans hw.2
  have hwre_pos : 0 < w.re := by
    linarith
  have hInv_le_one : w.re⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hwre_ge
  let u : UpperHalfPlane := UpperHalfPlane.ofComplex w
  have hu_coe : ((u : UpperHalfPlane) : ℂ) = w := by
    simpa [u] using
      congrArg (fun z : UpperHalfPlane ↦ (z : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos hwim)
  have hu_coe_im : ((u : UpperHalfPlane) : ℂ).im = w.im := by
    simpa [hu_coe]
  have hu_im : u.im = w.im := by
    simpa using hu_coe_im
  have hg_coe : g w = ((((w.re)⁻¹ : ℝ) : ℂ) * (u : ℂ)) := by
    simp [g, hu_coe]
  have hg_im : (g w).im = w.re⁻¹ * u.im := by
    simp [g, hu_coe, hu_im, Complex.mul_im, hwre_pos.ne', mul_comm, mul_left_comm, mul_assoc]
  have hrewrite_raw :=
    exercise8_abel_integral_sub_verticalLift_sub_horizontal_eq_scaledResidual
      k u (r := w.re⁻¹) (inv_pos.2 hwre_pos) hInv_le_one
  -- Rewrite the scaled residual owner back to the explicit normalization `g w`.
  convert hrewrite_raw.symm using 1
  · change
      exercise8_abel_integral k (UpperHalfPlane.ofComplex (g w)) -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (((g w).im : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment (((g w).im : ℂ) * Complex.I) (g w), (exercise8_integrand k dz) z =
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((((w.re)⁻¹ : ℝ) : ℂ) * (u : ℂ))) -
          exercise8_abel_integral k
            (UpperHalfPlane.ofComplex ((((w.re⁻¹ * u.im : ℝ) : ℂ) * Complex.I))) -
        ∫ᶜ z in Path.segment ((((w.re⁻¹ * u.im : ℝ) : ℂ) * Complex.I))
            ((((w.re)⁻¹ : ℝ) : ℂ) * (u : ℂ)),
          (exercise8_integrand k dz) z
    rw [hg_im, hg_coe]
  · change
      exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z =
      exercise8_abel_integral k u -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((((u : UpperHalfPlane) : ℂ).im : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment ((((u : UpperHalfPlane) : ℂ).im : ℂ) * Complex.I) (u : ℂ),
          (exercise8_integrand k dz) z
    rw [hu_coe_im, hu_coe]

/-- Helper for Cartan section26 0018_Exercise_8: the right-edge horizontal tail from
`1 + i Im w` to `Re w + i Im w` is the fixed interval integral on `1..1 / k` with the cutoff
`t ≤ Re w`. -/
lemma exercise8_rightHorizontal_segment_explicit_eq_indicatorIntegral
    (k : Exercise8Modulus) {w : ℂ}
    (hw : w ∈ {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)}) :
    ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
        ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
        if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0 := by
  have hdirect :
      ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
          ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
        ∫ t in (1 : ℝ)..w.re,
          exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) := by
    exact exercise8_horizontal_segment_eq_directIntervalIntegral k 1 w.re w.im
  calc
    ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
        ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ t in (1 : ℝ)..w.re,
        exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) := hdirect
    _ = ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
          if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0 := by
        -- Freeze the moving endpoint on the full right-edge interval `[1, 1 / k]`.
        symm
        simpa [Set.indicator] using
          (intervalIntegral.integral_indicator
            (μ := MeasureTheory.volume)
            (f := fun t : ℝ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I))
            (a₁ := (1 : ℝ)) (a₂ := w.re) (a₃ := (1 / (k : ℝ)))
            ⟨hw.2.1, hw.2.2⟩)

/-- Helper for Cartan section26 0018_Exercise_8: the fixed right-edge cutoff integral already
matches the increment of the boundary branch from `K` to the point over `x`. -/
lemma exercise8_indicatorIntegral_eq_rightBranchIncrement
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
        (if t ≤ x then (((exercise8_imaginary_kernel k t : ℝ) : ℂ) * Complex.I) else 0) =
      exercise8_boundary_right_branch k x - exercise8_complete_real_period k := by
  calc
    ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
        (if t ≤ x then (((exercise8_imaginary_kernel k t : ℝ) : ℂ) * Complex.I) else 0) =
      ∫ t in (1 : ℝ)..x, (((exercise8_imaginary_kernel k t : ℝ) : ℂ) * Complex.I) := by
        simpa [Set.indicator] using
          (intervalIntegral.integral_indicator
            (μ := MeasureTheory.volume)
            (f := fun t : ℝ ↦ (((exercise8_imaginary_kernel k t : ℝ) : ℂ) * Complex.I))
            (a₁ := (1 : ℝ)) (a₂ := x) (a₃ := (1 / (k : ℝ))) hx)
    _ = (exercise8_boundary_right_branch k x - exercise8_complete_real_period k) := by
      -- Rewrite the right branch through its named primitive and pull the constant factor `I`
      -- through the interval integral.
      rw [intervalIntegral.integral_mul_const, ← exercise8_intervalIntegral_ofReal,
        exercise8_boundary_right_branch_eq_right_primitive, exercise8_right_primitive]
      ring

/-- Helper for Cartan section26 0018_Exercise_8: for any horizontal slice with real coordinate
strictly larger than `1`, the translated square `z^2 - 1` stays in the open upper half-plane.
This is the sign input reused by the right-edge proof and by the reciprocal top-edge route. -/
lemma exercise8_square_sub_one_im_pos_of_real_gt_one {t y : ℝ} (ht : 1 < t) (hy : 0 < y) :
    0 < ((((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ) - 1).im) := by
  -- Expanding the square shows the imaginary part is exactly `2 t y`.
  simp [pow_two]
  nlinarith [ht, hy]

/-- Helper for Cartan section26 0018_Exercise_8: along any horizontal slice with real coordinate
`t > 1`, the norm of `z^2 - 1` is bounded below by its positive real-axis value `t^2 - 1`.
This is the branch-stable lower bound needed later for the reciprocal top-edge slice. -/
lemma exercise8_square_sub_one_norm_lower_of_real_gt_one
    {t y : ℝ} (ht : 1 < t) (hy : 0 < y) :
    t ^ (2 : ℕ) - 1 ≤
      ‖(((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ) - 1)‖ := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hfactor_nonneg : 0 ≤ t ^ (2 : ℕ) - 1 := by
    nlinarith [ht]
  have hsq :
      (t ^ (2 : ℕ) - 1) ^ (2 : ℕ) ≤
        Complex.normSq ((z ^ (2 : ℕ)) - 1) := by
    -- Expanding the norm square shows the positive `y`-terms only increase `(t^2 - 1)^2`.
    rw [show
        Complex.normSq ((z ^ (2 : ℕ)) - 1) =
          (t ^ (2 : ℕ) - 1 - y ^ (2 : ℕ)) ^ (2 : ℕ) +
            (2 * t * y) ^ (2 : ℕ) by
      simp [z, Complex.normSq_apply, pow_two]
      ring_nf]
    nlinarith
  have hnorm :
      ‖(z ^ (2 : ℕ)) - 1‖ ^ (2 : ℕ) =
        Complex.normSq ((z ^ (2 : ℕ)) - 1) := by
    simpa using Complex.sq_norm ((z ^ (2 : ℕ)) - 1)
  -- Compare the squared lower bound with the squared norm, then return to norms.
  nlinarith [hfactor_nonneg, norm_nonneg ((z ^ (2 : ℕ)) - 1), hsq, hnorm]

/-- Helper for Cartan section26 0018_Exercise_8: for a fixed right-edge parameter
`t ∈ (1, 1 / k)`, the vertical slice of the integrand tends to the imaginary kernel times `I`. -/
lemma exercise8_rightVerticalSlice_tendsto_imaginaryKernel
    (k : Exercise8Modulus) {t : ℝ} (ht : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ))) :
    Filter.Tendsto
      (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((((exercise8_imaginary_kernel k t : ℝ) : ℂ)) * Complex.I)) := by
  let leftFactor : ℝ → ℂ := fun y ↦ Complex.sqrt ((((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) - 1)
  let rightFactor : ℝ → ℂ := fun y ↦
    Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)))
  let branchProduct : ℝ → ℂ := fun y ↦ (-Complex.I) * leftFactor y * rightFactor y
  have hleft_pos : 0 < t ^ (2 : ℕ) - 1 := by
    nlinarith [ht.1]
  have hright_pos : 0 < 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
    have hkt_lt : (k : ℝ) * t < (k : ℝ) * (1 / (k : ℝ)) := by
      exact mul_lt_mul_of_pos_left ht.2 hk_pos
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    have hkt_lt_one : (k : ℝ) * t < 1 := by
      rw [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp [hk_ne]] at hkt_lt
      exact hkt_lt
    have hkt_nonneg : 0 ≤ (k : ℝ) * t := by
      nlinarith [hk_pos, ht.1]
    have hsq : ((k : ℝ) * t) ^ (2 : ℕ) < 1 := by
      nlinarith [hkt_lt_one, hkt_nonneg]
    have hsq' : (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) < 1 := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    linarith
  have hleft_tendsto :
      Filter.Tendsto leftFactor (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)))) := by
    have hrad_tendsto :
        Filter.Tendsto (fun y : ℝ ↦ (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) - 1)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ))) := by
      have hslice :
          ContinuousAt (fun y : ℝ ↦ (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) - 1) 0 := by
        have hpath : Continuous fun y : ℝ ↦ (t : ℂ) + (y : ℂ) * Complex.I := by
          exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        exact ((hpath.pow 2).sub continuous_const).continuousAt
      simpa [pow_two] using hslice.continuousWithinAt.tendsto
    have hsqrt_cont :
        ContinuousAt Complex.sqrt (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)) := by
      simpa using
        (Complex.continuousAt_sqrt (Or.inl
          (show (0 : ℝ) ≤ ((((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)).re) by
            norm_num [pow_two]
            nlinarith [ht.1])) :
          ContinuousAt Complex.sqrt (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)))
    have hsqrt_raw := hsqrt_cont.tendsto.comp hrad_tendsto
    have htarget :
        Complex.sqrt (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)) =
          (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) := by
      have hnonnegR : 0 ≤ t ^ (2 : ℕ) - 1 := by
        nlinarith [ht.1]
      simpa [pow_two] using
        (Complex.sqrt_of_nonneg
          (show 0 ≤ (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)) by
            exact_mod_cast hnonnegR))
    have hsqrt_raw' :
        Filter.Tendsto leftFactor (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Complex.sqrt (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)))) := by
      simpa [leftFactor, Function.comp] using hsqrt_raw
    exact htarget ▸ hsqrt_raw'
  have hright_tendsto :
      Filter.Tendsto rightFactor (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ)))) := by
    have hrad_tendsto :
        Filter.Tendsto
          (fun y : ℝ ↦
            (1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (((1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) : ℝ) : ℂ))) := by
      have hslice :
          ContinuousAt
            (fun y : ℝ ↦
              (1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ))) 0 := by
        have hpath : Continuous fun y : ℝ ↦ (t : ℂ) + (y : ℂ) * Complex.I := by
          exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        exact (continuous_const.sub (continuous_const.mul (hpath.pow 2))).continuousAt
      simpa [pow_two] using hslice.continuousWithinAt.tendsto
    have hsqrt_cont :
        ContinuousAt Complex.sqrt (((1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) : ℝ) : ℂ)) := by
      simpa using
        (Complex.continuousAt_sqrt (Or.inl
          (show (0 : ℝ) ≤ ((((1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) : ℝ) : ℂ)).re) by
            norm_num [pow_two]
            linarith)) :
          ContinuousAt Complex.sqrt (((1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) : ℝ) : ℂ)))
    have hsqrt_raw := hsqrt_cont.tendsto.comp hrad_tendsto
    have htarget :
        Complex.sqrt (((1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) : ℝ) : ℂ)) =
          (((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ)) := by
      have hnonnegR : 0 ≤ 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
        linarith
      simpa [pow_two] using
        (Complex.sqrt_of_nonneg
          (show 0 ≤ (((1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) : ℝ) : ℂ)) by
            exact_mod_cast hnonnegR))
    have hsqrt_raw' :
        Filter.Tendsto rightFactor (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Complex.sqrt (((1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) : ℝ) : ℂ)))) := by
      simpa [rightFactor, Function.comp] using hsqrt_raw
    exact htarget ▸ hsqrt_raw'
  have hproduct_tendsto :
      Filter.Tendsto branchProduct (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          ((-Complex.I) * (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) *
            (((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ)))) := by
    simpa [branchProduct, mul_assoc] using (tendsto_const_nhds.mul hleft_tendsto).mul hright_tendsto
  have hleft_ne :
      (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 hleft_pos)
  have hright_ne :
      (((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 hright_pos)
  have hproduct_ne :
      (-Complex.I) * (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) *
          (((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hleft_ne) hright_ne
  have hraw_tendsto :
      Filter.Tendsto (fun y : ℝ ↦ (branchProduct y)⁻¹) (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (((-Complex.I) * (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) *
              (((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ)))⁻¹)) := by
    exact Filter.Tendsto.inv₀ hproduct_tendsto hproduct_ne
  have heq :
      (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun y : ℝ ↦ (branchProduct y)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hz_im : 0 < (((t : ℂ) + (y : ℂ) * Complex.I)).im := by
      simpa using hy
    have hw :
        0 < ((((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ) - 1).im) :=
      exercise8_square_sub_one_im_pos_of_real_gt_one (t := t) (y := y) ht.1 hy
    have hneg :
        (1 : ℂ) - (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) =
          -((((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) - 1) := by
      ring
    -- Rewrite the source branch through the principal square-root factorization on the right edge.
    rw [exercise8_integrand, exercise8_simpleSqrtBranch_eq_principalFactorization_on_upper k hz_im,
      hneg, exercise8_sqrt_neg_eq_negI_sqrt_of_im_pos hw]
  have htarget :
      (((-Complex.I) * (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) *
          (((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ)))⁻¹) =
        (((exercise8_imaginary_kernel k t : ℝ) : ℂ)) * Complex.I := by
    let a : ℂ := (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ))
    let b : ℂ := (((Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) : ℝ) : ℂ))
    have ha : a ≠ 0 := by
      dsimp [a]
      exact_mod_cast (Real.sqrt_ne_zero'.2 hleft_pos)
    have hb : b ≠ 0 := by
      dsimp [b]
      exact_mod_cast (Real.sqrt_ne_zero'.2 hright_pos)
    have hInvI : (((-Complex.I) * a * b)⁻¹) = Complex.I * (a * b)⁻¹ := by
      field_simp [ha, hb, Complex.I_ne_zero]
      norm_num
    have hkernel : (((exercise8_imaginary_kernel k t : ℝ) : ℂ)) = (a * b)⁻¹ := by
      dsimp [a, b]
      rw [exercise8_imaginary_kernel]
      have hsqrt :
          Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) =
            Real.sqrt (t ^ (2 : ℕ) - 1) * Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
        rw [Real.sqrt_mul (le_of_lt hleft_pos)]
      rw [hsqrt]
      norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    simpa [a, b, hkernel, mul_comm] using hInvI
  have hraw_tendsto_kernel :
      Filter.Tendsto (fun y : ℝ ↦ (branchProduct y)⁻¹) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((((exercise8_imaginary_kernel k t : ℝ) : ℂ)) * Complex.I)) := by
    exact htarget ▸ hraw_tendsto
  -- The pointwise factorization and the fixed limiting product together identify the right-edge
  -- boundary kernel.
  simpa [branchProduct] using Filter.Tendsto.congr' heq.symm hraw_tendsto_kernel

/-- Helper for Cartan section26 0018_Exercise_8: away from the null endpoint set
`{x, 1, 1 / k}`, the fixed right-edge cutoff integrand has the pointwise boundary limit needed by
dominated convergence. -/
lemma exercise8_rightIndicator_ae_tendsto_limit
    (k : Exercise8Modulus) {x : ℝ} :
    ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (1 : ℝ) (1 / (k : ℝ)) →
        Filter.Tendsto
          (fun w : ℂ ↦
            if t ≤ w.re then
              exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I)
            else 0)
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
          (nhds (if t ≤ x then (((exercise8_imaginary_kernel k t : ℝ)) : ℂ) * Complex.I else 0)) := by
  have htx_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ x := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  have h1_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 : ℝ) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  have hk_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 / (k : ℝ)) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [htx_ae, h1_ae, hk_ae] with t htx h1 hk
  intro ht
  have ht_mem : t ∈ Ioc (1 : ℝ) (1 / (k : ℝ)) := by
    have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
      simpa [one_div] using
        (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
    rw [Set.uIoc_of_le hk_inv_gt_one.le] at ht
    exact ht
  have ht_right : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ)) := ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 hk⟩
  have hIm :
      Filter.Tendsto (fun w : ℂ ↦ w.im)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds 0) := by
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (f := fun w : ℂ ↦ w.im)
        (s := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (Complex.continuous_im.continuousAt.tendsto :
          Filter.Tendsto (fun w : ℂ ↦ w.im) (nhds (x : ℂ)) (nhds ((x : ℂ).im))))
  have hIm_pos :
      ∀ᶠ w in nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)},
        w.im ∈ Set.Ioi 0 := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    exact hw.1
  have hImWithin :
      Filter.Tendsto (fun w : ℂ ↦ w.im)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hIm hIm_pos
  have hslice :
      Filter.Tendsto
        (fun w : ℂ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I))
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds ((((exercise8_imaginary_kernel k t : ℝ) : ℂ)) * Complex.I)) := by
    simpa using (exercise8_rightVerticalSlice_tendsto_imaginaryKernel k ht_right).comp hImWithin
  have hre :
      Filter.Tendsto (fun w : ℂ ↦ w.re)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds x) := by
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (f := fun w : ℂ ↦ w.re)
        (s := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (Complex.continuous_re.continuousAt.tendsto :
          Filter.Tendsto (fun w : ℂ ↦ w.re) (nhds (x : ℂ)) (nhds ((x : ℂ).re))))
  by_cases htx_le : t ≤ x
  · have htx_lt : t < x := lt_of_le_of_ne htx_le htx
    have htrue :
        ∀ᶠ w in nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)},
          t ≤ w.re := by
      have hgt :
          {w : ℂ | t < w.re} ∈
            nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)} := by
        simpa using hre (IsOpen.mem_nhds isOpen_Ioi htx_lt)
      filter_upwards [hgt] with w hw using le_of_lt hw
    have hEq :
        Filter.EventuallyEq
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
          (fun w : ℂ ↦
            if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
          (fun w : ℂ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I)) := by
      filter_upwards [htrue] with w hw
      simp [hw]
    simpa [htx_le] using Filter.Tendsto.congr' hEq.symm hslice
  · have hxt_lt : x < t := lt_of_not_ge htx_le
    have hfalse :
        ∀ᶠ w in nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)},
          ¬ t ≤ w.re := by
      have hlt :
          {w : ℂ | w.re < t} ∈
            nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)} := by
        simpa using hre (IsOpen.mem_nhds isOpen_Iio hxt_lt)
      filter_upwards [hlt] with w hw
      exact not_le_of_gt hw
    have hEq :
        Filter.EventuallyEq
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
          (fun w : ℂ ↦
            if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
          (fun _ : ℂ ↦ (0 : ℂ)) := by
      filter_upwards [hfalse] with w hw
      simp [hw]
    simpa [htx_le] using
      Filter.Tendsto.congr' hEq.symm
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℂ ↦ (0 : ℂ))
            (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
            (nhds (0 : ℂ)))

/-- Helper for Cartan section26 0018_Exercise_8: the fixed right-edge cutoff model converges to
the boundary-branch increment by dominated convergence on the interval `[1, 1 / k]`. -/
lemma exercise8_rightHorizontal_indicator_tendsto
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    Filter.Tendsto
      (fun w : ℂ ↦
        ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
          if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
      (nhds (exercise8_boundary_right_branch k x - exercise8_complete_real_period k)) := by
  let l : Filter ℂ := nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)}
  have hF_meas :
      ∀ᶠ w in l,
        MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ ↦
            if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
          (MeasureTheory.volume.restrict (Set.uIoc (1 : ℝ) (1 / (k : ℝ)))) := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    have hcontOn :
        ContinuousOn
          (fun t : ℝ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I))
          Set.univ := by
      let g : ℝ → ℂ := fun t ↦ (t : ℂ) + (w.im : ℂ) * Complex.I
      have hg : Continuous g := by
        simpa [g] using Complex.continuous_ofReal.add continuous_const
      refine (exercise8_integrand_continuousOn_upper k).comp hg.continuousOn ?_
      intro t ht
      simpa [g] using hw.1
    have hcont :
        Continuous (fun t : ℝ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I)) := by
      rw [← continuousOn_univ]
      simpa using hcontOn
    exact ((hcont.measurable.piecewise measurableSet_Iic measurable_const).aestronglyMeasurable)
  have h_bound :
      ∀ᶠ w in l,
        ∀ᵐ t ∂MeasureTheory.volume,
          t ∈ Set.uIoc (1 : ℝ) (1 / (k : ℝ)) →
            ‖if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0‖ ≤
              exercise8_imaginary_kernel k t := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    have h1_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 : ℝ) := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    have hk_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 / (k : ℝ)) := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [h1_ae, hk_ae] with t h1 hk
    intro ht
    by_cases hcut : t ≤ w.re
    · have ht_mem : t ∈ Ioc (1 : ℝ) (1 / (k : ℝ)) := by
        have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
          simpa [one_div] using
            (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
        rw [Set.uIoc_of_le hk_inv_gt_one.le] at ht
        exact ht
      have ht_right : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ)) := ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 hk⟩
      simpa [hcut] using exercise8_integrand_norm_le_imaginaryKernel_on_right k ht_right hw.1
    · dsimp [exercise8_imaginary_kernel]
      simp [hcut, Real.sqrt_nonneg]
  have h_lim :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (1 : ℝ) (1 / (k : ℝ)) →
          Filter.Tendsto
            (fun w : ℂ ↦
              if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
            l
            (nhds (if t ≤ x then (((exercise8_imaginary_kernel k t : ℝ)) : ℂ) * Complex.I else 0)) :=
    exercise8_rightIndicator_ae_tendsto_limit k
  -- The public right-edge increment is now only the fixed-interval dominated-convergence step.
  have hdc :=
    (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume)
      (bound := exercise8_imaginary_kernel k)
      hF_meas h_bound (exercise8_imaginary_kernel_intervalIntegrable k) h_lim)
  have hlimit_eq :
      (∫ t in (1 : ℝ)..(1 / (k : ℝ)),
          if t ≤ x then (((exercise8_imaginary_kernel k t : ℝ) : ℂ) * Complex.I) else 0) =
        exercise8_boundary_right_branch k x - exercise8_complete_real_period k :=
    exercise8_indicatorIntegral_eq_rightBranchIncrement k hx
  exact hlimit_eq ▸ (by simpa [l] using hdc)

/-- Helper for Cartan section26 0018_Exercise_8: the horizontal tail from `1 + i Im w` to `w`
already converges to the right-edge boundary-branch increment once the moving endpoint is frozen on
the full interval `[1, 1 / k]`. -/
lemma exercise8_rightHorizontal_tendsto_rightBranchIncrement
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    Filter.Tendsto
      (fun w : ℂ ↦
        ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
      (nhds (exercise8_boundary_right_branch k x - exercise8_complete_real_period k)) := by
  -- Route correction: as on the inner strip, isolate the moving endpoint behind one fixed-interval
  -- cutoff theorem and keep the public right-edge limit as a final rewrite.
  refine Filter.Tendsto.congr' ?_ (exercise8_rightHorizontal_indicator_tendsto k hx)
  filter_upwards [self_mem_nhdsWithin] with w hw using
    (calc
      ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z =
          ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
            ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z := by
              exact congrArg
                (fun b : ℂ ↦
                  ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I) b,
                    (exercise8_integrand k dz) z)
                (Complex.re_add_im w).symm
      _ =
          ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
            if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0 := by
              exact exercise8_rightHorizontal_segment_explicit_eq_indicatorIntegral k hw).symm

/-- Helper for Cartan section26 0018_Exercise_8: approaching a point of `[1, 1 / k]` through the
closed right strip should recover the right-edge boundary branch. -/
lemma exercise8_abel_integral_tendsto_right_strip
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
      (nhds (exercise8_boundary_right_branch k x)) := by
  -- Route correction: the common anchor segment and the rescaling-to-`1` map are now isolated.
  -- The rescaled residual now has its own right-strip lemma, so the only remaining blocker is the
  -- horizontal increment `1 + Im w * I -> w`, expressed against
  -- `exercise8_boundary_right_branch`.
  have hresidual :
      Filter.Tendsto
        (fun w : ℂ ↦
          exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds 0) :=
    exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_rightStrip k hx
  have hvertical :
      Filter.Tendsto
        (fun w : ℂ ↦
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)))
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds 0) :=
    exercise8_abel_integral_verticalLift_tendsto_zero_on_rightStrip (k := k) (x := x)
  have hanchor :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) ((1 : ℂ) + (w.im : ℂ) * Complex.I),
            (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds (exercise8_complete_real_period k)) := by
    -- Restricting the common anchor-segment limit from `{Im w > 0, 1 ≤ Re w}` to the closed
    -- right strip is immediate.
    simpa using
      (exercise8_anchorHorizontal_tendsto_completeRealPeriod k hx.1).mono_left
        (nhdsWithin_mono _ (by
          intro w hw
          exact ⟨hw.1, hw.2.1⟩))
  have htail :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds (exercise8_boundary_right_branch k x - exercise8_complete_real_period k)) :=
    exercise8_rightHorizontal_tendsto_rightBranchIncrement k hx
  have hhorizontal :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds (exercise8_boundary_right_branch k x)) := by
    have hsum :
        Filter.Tendsto
          (fun w : ℂ ↦
            (∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I)
                ((1 : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z) +
              ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I) w,
                (exercise8_integrand k dz) z)
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
          (nhds (exercise8_boundary_right_branch k x)) := by
      -- The full horizontal boundary contribution is the anchor segment `0 -> 1` plus the
      -- right-edge tail `1 -> x`.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hanchor.add htail
    refine Filter.Tendsto.congr' ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hadd := exercise8_horizontal_segment_add k 0 1 w.re w.im hw.1
    rw [show (((0 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I) = (w.im : ℂ) * Complex.I by simp,
      show ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w by simpa using (Complex.re_add_im w)] at hadd
    exact hadd
  have hsum :
      Filter.Tendsto
        (fun w : ℂ ↦
          (exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
              exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
              ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z) +
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) +
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
        (nhds (exercise8_boundary_right_branch k x)) := by
    -- The right-strip limit is the same three-term decomposition as on the inner strip:
    -- residual `→ 0`, vertical lift `→ 0`, and horizontal term `→` the boundary branch.
    simpa using (hresidual.add hvertical).add hhorizontal
  -- Collapse the three-term decomposition back to the original Abel integral.
  convert hsum using 1
  ext w
  ring

/-- Helper for Cartan section26 0018_Exercise_8: the remaining top-edge horizontal tail from
`(1 / k) + i Im w` to `w` should converge to the corresponding top-branch increment. -/
lemma exercise8_boundary_right_branch_eq_vertex_inv_k
    (k : Exercise8Modulus) :
    exercise8_boundary_right_branch k (1 / (k : ℝ)) =
      exercise8_complete_real_period k +
        exercise8_complete_imaginary_period k * Complex.I := by
  -- The shared vertex `1 / k` is already identified by the repaired public boundary owner.
  calc
    exercise8_boundary_right_branch k (1 / (k : ℝ)) =
        exercise8_boundary_value k (1 / (k : ℝ)) := by
          symm
          have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
            simpa [one_div] using
              (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
          simpa [exercise8_boundary_right_branch] using
            exercise8_boundary_value_eq_right (k := k) (x := 1 / (k : ℝ))
              hk_inv_gt_one.le le_rfl
    _ =
        exercise8_complete_real_period k +
          exercise8_complete_imaginary_period k * Complex.I := by
            simpa using exercise8_boundary_value_inv_k k

/-- Helper for Cartan section26 0018_Exercise_8: after subtracting the common vertex value
`K + i K'`, the top-edge increment is the bottom-edge branch at the reciprocal source parameter,
shifted by `-K`. -/
lemma exercise8_topBranchIncrement_eq_innerBranch_sub_completeRealPeriod
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    exercise8_boundary_top_branch k x -
        exercise8_boundary_right_branch k (1 / (k : ℝ)) =
      exercise8_boundary_inner_branch k (1 / ((k : ℝ) * x)) -
        exercise8_complete_real_period k := by
  -- Rewrite both owners to the short primitive forms before canceling the common `i K'`.
  calc
    exercise8_boundary_top_branch k x -
        exercise8_boundary_right_branch k (1 / (k : ℝ)) =
      (((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ) -
        exercise8_complete_real_period k) := by
          rw [exercise8_boundary_top_branch_eq_inner_composition,
            exercise8_boundary_right_branch_eq_vertex_inv_k]
          ring
    _ =
        exercise8_boundary_inner_branch k (1 / ((k : ℝ) * x)) -
          exercise8_complete_real_period k := by
            rw [exercise8_boundary_inner_branch_eq_inner_primitive]

/-- Helper for Cartan section26 0018_Exercise_8: the remaining top-edge horizontal tail from
`(1 / k) + i Im w` to `w` should converge to the corresponding top-branch increment. -/
lemma exercise8_topHorizontal_tendsto_topBranchIncrement
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    Filter.Tendsto
      (fun w : ℂ ↦
        ∫ᶜ z in Path.segment (((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I) w,
          (exercise8_integrand k dz) z)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
      (nhds
        (exercise8_boundary_top_branch k x -
          exercise8_boundary_right_branch k (1 / (k : ℝ)))) := by
  -- Route correction: the public theorem now delegates the reciprocal-substitution normalization
  -- to the theorem-local support owner in `RightTopStripBoundary`.
  refine Filter.Tendsto.congr' ?_
    (exercise8_topHorizontal_indicator_tendsto_topBranchIncrement k hx)
  filter_upwards [self_mem_nhdsWithin] with w hw using
    (calc
      ∫ᶜ z in Path.segment (((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I) w,
          (exercise8_integrand k dz) z =
        ∫ᶜ z in Path.segment (((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I)
            ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z := by
              exact congrArg
                (fun b : ℂ ↦
                  ∫ᶜ z in Path.segment (((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I) b,
                    (exercise8_integrand k dz) z)
                (Complex.re_add_im w).symm
      _ =
        ∫ s in (0 : ℝ)..1,
          if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0 := by
            exact exercise8_topHorizontal_segment_eq_reciprocalIndicatorIntegral k hw).symm

/-- Helper for Cartan section26 0018_Exercise_8: approaching a point of `[1 / k, +∞)` through the
top strip should recover the top-edge boundary branch. -/
lemma exercise8_abel_integral_tendsto_top_strip
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
      (nhds (exercise8_boundary_top_branch k x)) := by
  let invK : ℂ := ((1 / (k : ℝ)) : ℂ)
  let topStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}
  let rightStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)}
  have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using
      (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hx_ge_one : 1 ≤ x := hk_inv_gt_one.le.trans hx
  have hresidual :
      Filter.Tendsto
        (fun w : ℂ ↦
          exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) topStrip)
        (nhds 0) :=
    exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_topStrip k hx
  have hvertical :
      Filter.Tendsto
        (fun w : ℂ ↦
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)))
        (nhdsWithin (x : ℂ) topStrip)
        (nhds 0) :=
    exercise8_abel_integral_verticalLift_tendsto_zero_on_topStrip (k := k) (x := x)
  have hanchor :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) ((1 : ℂ) + (w.im : ℂ) * Complex.I),
            (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) topStrip)
        (nhds (exercise8_complete_real_period k)) := by
    have hsubset : topStrip ⊆ {w : ℂ | 0 < w.im ∧ 1 ≤ w.re} := by
      intro w hw
      exact ⟨hw.1, hk_inv_gt_one.le.trans hw.2⟩
    -- The common anchor segment only needs `Im w > 0` and `1 ≤ Re w`, both true on the top strip.
    simpa using
      (exercise8_anchorHorizontal_tendsto_completeRealPeriod k (x := x) hx_ge_one).mono_left
        (nhdsWithin_mono _ hsubset)
  have hmiddle :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
              (invK + (w.im : ℂ) * Complex.I),
            (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) topStrip)
        (nhds
          (exercise8_boundary_right_branch k (1 / (k : ℝ)) -
            exercise8_complete_real_period k)) := by
    let g : ℂ → ℂ := fun w ↦ invK + (w.im : ℂ) * Complex.I
    have hg_tendsto : Filter.Tendsto g (nhdsWithin (x : ℂ) topStrip) (nhds invK) := by
      have hg_cont : Continuous g := by
        simpa [g] using continuous_const.add
          ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)
      have hg_center :=
        ((hg_cont.continuousAt : ContinuousAt g (x : ℂ)).continuousWithinAt (s := topStrip)).tendsto
      -- The lifted endpoint forgets the real coordinate and lands at `(1 / k) + 0 * I`.
      simpa [g] using hg_center
    have hg_within :
        ∀ᶠ w in nhdsWithin (x : ℂ) topStrip, g w ∈ rightStrip := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro w hw
      refine ⟨?_, ?_, ?_⟩
      · simpa [g, invK] using hw.1
      · simpa [g, invK] using hk_inv_gt_one.le
      · simp [g, invK]
    have hg_right :
        Filter.Tendsto g (nhdsWithin (x : ℂ) topStrip)
          (nhdsWithin (((1 / (k : ℝ)) : ℂ)) rightStrip) := by
      simpa [invK] using
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within g hg_tendsto hg_within
    have hg_right' :
        Filter.Tendsto (fun w : ℂ ↦ ((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I)
          (nhdsWithin (x : ℂ) topStrip)
          (nhdsWithin (((1 / (k : ℝ)) : ℂ)) rightStrip) := by
      simpa [g, invK] using hg_right
    have hbaseRaw :
        Filter.Tendsto
          (fun w : ℂ ↦
            ∫ᶜ z in Path.segment ((1 : ℂ) + ((g w).im : ℂ) * Complex.I) (g w),
              (exercise8_integrand k dz) z)
          (nhdsWithin (x : ℂ) topStrip)
          (nhds
            (exercise8_boundary_right_branch k (1 / (k : ℝ)) -
              exercise8_complete_real_period k)) := by
      simpa [g, invK] using
        (exercise8_rightHorizontal_tendsto_rightBranchIncrement k
          (x := 1 / (k : ℝ)) ⟨hk_inv_gt_one.le, le_rfl⟩).comp
            (by simpa [rightStrip] using hg_right')
    have hbase :
        Filter.Tendsto
          (fun w : ℂ ↦
            ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
                (invK + (w.im : ℂ) * Complex.I),
              (exercise8_integrand k dz) z)
          (nhdsWithin (x : ℂ) topStrip)
          (nhds
            (exercise8_boundary_right_branch k (1 / (k : ℝ)) -
              exercise8_complete_real_period k)) := by
      refine Filter.Tendsto.congr' ?_ hbaseRaw
      filter_upwards [self_mem_nhdsWithin] with w hw
      have him : (g w).im = w.im := by
        simp [g, invK]
      rw [him]
    exact hbase
  have htail :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment (invK + (w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) topStrip)
        (nhds
          (exercise8_boundary_top_branch k x -
            exercise8_boundary_right_branch k (1 / (k : ℝ)))) := by
    simpa [invK, topStrip] using exercise8_topHorizontal_tendsto_topBranchIncrement k hx
  have hhorizontal :
      Filter.Tendsto
        (fun w : ℂ ↦
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) topStrip)
        (nhds (exercise8_boundary_top_branch k x)) := by
    have hsum :
        Filter.Tendsto
          (fun w : ℂ ↦
            (∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I)
                ((1 : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z) +
              ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
                (invK + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z +
              ∫ᶜ z in Path.segment (invK + (w.im : ℂ) * Complex.I) w,
                (exercise8_integrand k dz) z)
          (nhdsWithin (x : ℂ) topStrip)
          (nhds (exercise8_boundary_top_branch k x)) := by
      -- The top-strip horizontal term is the anchor `0 -> 1`, the middle edge `1 -> 1 / k`,
      -- and the remaining top-edge tail `1 / k -> x`.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hanchor.add hmiddle).add htail
    refine Filter.Tendsto.congr' ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with w hw
    let z0 : UpperHalfPlane := ⟨((w.im : ℂ) * Complex.I), by simpa using hw.1⟩
    let z1 : UpperHalfPlane := ⟨((1 : ℂ) + (w.im : ℂ) * Complex.I), by simpa using hw.1⟩
    let z2 : UpperHalfPlane := ⟨(invK + (w.im : ℂ) * Complex.I), by simpa [invK] using hw.1⟩
    have haddLeft :
        (∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) ((1 : ℂ) + (w.im : ℂ) * Complex.I),
            (exercise8_integrand k dz) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
            (invK + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
        ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) (invK + (w.im : ℂ) * Complex.I),
          (exercise8_integrand k dz) z := by
      simpa [z0, z1, z2] using exercise8_segment_integral_add k z0 z1 z2
    let z3 : UpperHalfPlane := ⟨w, hw.1⟩
    have haddRight :
        (∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) (invK + (w.im : ℂ) * Complex.I),
            (exercise8_integrand k dz) z) +
          ∫ᶜ z in Path.segment (invK + (w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z =
        ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z := by
      simpa [z0, z2, z3] using exercise8_segment_integral_add k z0 z2 z3
    -- First concatenate `0 -> 1 -> 1 / k`, then concatenate the result with the top-edge tail.
    calc
      (∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) ((1 : ℂ) + (w.im : ℂ) * Complex.I),
            (exercise8_integrand k dz) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + (w.im : ℂ) * Complex.I)
            (invK + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z +
          ∫ᶜ z in Path.segment (invK + (w.im : ℂ) * Complex.I) w,
            (exercise8_integrand k dz) z
          =
          (∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I)
                (invK + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z) +
              ∫ᶜ z in Path.segment (invK + (w.im : ℂ) * Complex.I) w,
                (exercise8_integrand k dz) z := by
            rw [haddLeft]
      _ =
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z := by
            exact haddRight
  have hsum :
      Filter.Tendsto
        (fun w : ℂ ↦
          (exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
              exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
              ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z) +
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) +
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
        (nhdsWithin (x : ℂ) topStrip)
        (nhds (exercise8_boundary_top_branch k x)) := by
    -- As on the right strip, the Abel integral is recovered from residual `→ 0`, vertical lift
    -- `→ 0`, and the horizontal term `→` the top-edge boundary owner.
    simpa using (hresidual.add hvertical).add hhorizontal
  -- Collapse the three-term decomposition back to the original Abel integral.
  convert hsum using 1
  ext w
  ring

