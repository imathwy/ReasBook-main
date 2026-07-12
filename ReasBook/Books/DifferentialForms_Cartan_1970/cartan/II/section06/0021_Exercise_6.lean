import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0027_Remark_II_1_extra_17»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

/-- Rescale the real and imaginary coordinates of a complex number by `a` and `b`. -/
private def ellipseAxisMap (a b : ℝ) : ℂ → ℂ :=
  fun z ↦ a * z.re + (b * z.im) * Complex.I

/-- A concrete parametrization of the axis-scaled unit circle with horizontal parameter `a` and
vertical parameter `b`. -/
def ellipseParam (a b : ℝ) : ℝ → ℂ :=
  ellipseAxisMap a b ∘ circleMap 0 1

private theorem ellipseAxisMap_continuous (a b : ℝ) : Continuous (ellipseAxisMap a b) := by
  simpa [ellipseAxisMap] using
    (by
      fun_prop :
        Continuous fun z : ℂ ↦ a * z.re + (b * z.im) * Complex.I)

@[simp] private theorem ellipseAxisMap_one (a b : ℝ) :
    ellipseAxisMap a b (1 : ℂ) = (a : ℂ) := by
  simp [ellipseAxisMap]

@[simp] theorem ellipseParam_apply (a b t : ℝ) :
    ellipseParam a b t = a * Real.cos t + (b * Real.sin t) * Complex.I := by
  simp [ellipseParam, ellipseAxisMap, circleMap_zero_re, circleMap_zero_im]

/-- The axis-scaled image of the positively oriented unit circle, viewed as a closed path. -/
abbrev ellipsePath (a b : ℝ) : Path (a : ℂ) (a : ℂ) :=
  ((closedDiscBoundaryPath (1 : NNReal)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Metric.closedBall (0 : ℂ) (1 : ℝ), ℂ))).map
      (ellipseAxisMap_continuous a b)).cast
    (ellipseAxisMap_one a b).symm
    (ellipseAxisMap_one a b).symm

@[simp] theorem ellipsePath_apply (a b : ℝ) (t : I) :
    ellipsePath a b t = ellipseParam a b (2 * Real.pi * (t : ℝ)) := by
  simp [ellipsePath, ellipseParam]
  simpa using congrArg (ellipseAxisMap a b)
    (closedDiscBoundaryPath_apply (1 : NNReal)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Metric.closedBall (0 : ℂ) (1 : ℝ), ℂ)) t)

/-- Helper for Cartan section06 0021_Exercise_6: the unit-circle image on `[0, 2π]` already fills
the full range of `circleMap 0 1`. -/
private theorem circleMapImage_eq_range :
    circleMap 0 1 '' Set.Icc (0 : ℝ) (2 * Real.pi) = Set.range (circleMap 0 1) := by
  -- Periodicity identifies one full turn of the unit circle with the entire range.
  simpa using (periodic_circleMap 0 1).image_Icc Real.two_pi_pos (0 : ℝ)

/-- Helper for Cartan section06 0021_Exercise_6: the range of `circleMap 0 1` is the unit circle
in `ℂ`. -/
private theorem range_circleMap_eq_unitSphere :
    Set.range (circleMap 0 1) = Metric.sphere (0 : ℂ) 1 := by
  -- The unit-radius circle map is exactly `θ ↦ exp (θ i)`.
  convert (range_circleMap (0 : ℂ) (1 : ℝ)) using 1
  norm_num

/-- Helper for Cartan section06 0021_Exercise_6: reparameterizing `ellipsePath` by
`θ = 2π t` turns its range into the textbook `ellipseParam` image on `[0, 2π]`. -/
private theorem range_ellipsePath_eq_image_ellipseParamIcc (a b : ℝ) :
    Set.range (ellipsePath a b) = ellipseParam a b '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
  -- The closed path uses the same geometric loop as `ellipseParam`, only with the normalized
  -- parameter `t ∈ I`.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨2 * Real.pi * (t : ℝ), ?_, ?_⟩
    · constructor
      · exact mul_nonneg (by positivity) t.2.1
      · have ht : (t : ℝ) ≤ 1 := t.2.2
        nlinarith [Real.pi_pos, ht]
    · exact ellipsePath_apply a b t
  · rintro ⟨θ, hθ, rfl⟩
    have htwoPi : 0 < 2 * Real.pi := by
      positivity
    refine ⟨⟨θ / (2 * Real.pi), ?_⟩, ?_⟩
    · constructor
      · exact div_nonneg hθ.1 htwoPi.le
      · exact (div_le_one htwoPi).2 (by simpa using hθ.2)
    · have hdiv : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
        field_simp [Real.pi_ne_zero]
      simp [ellipsePath_apply, hdiv]

/-- Helper for Cartan section06 0021_Exercise_6: the parametrized ellipse image is exactly the
quadratic ellipse cut out by `x^2 / a^2 + y^2 / b^2 = 1`. -/
private theorem ellipseParamImage_eq_ellipse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseParam a b '' Set.Icc (0 : ℝ) (2 * Real.pi) =
      {z : ℂ | z.re ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 = 1} := by
  -- Route correction: normalize points on the ellipse to the unit circle and use the full
  -- `circleMap 0 1` image over one period instead of reconstructing an argument witness by hand.
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    -- The forward direction is a direct trigonometric normalization.
    rw [ellipseParam_apply]
    simp [sq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp [ha, hb]
    nlinarith [Real.cos_sq_add_sin_sq t]
  · intro hz
    let w : ℂ := (z.re / a) + (z.im / b) * Complex.I
    have hw_normSq : Complex.normSq w = 1 := by
      -- The ellipse equation says precisely that the rescaled point has norm one.
      simp [w, Complex.normSq_apply, sq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] at hz ⊢
      field_simp [ha, hb] at hz ⊢
      nlinarith
    have hw_sphere : w ∈ Metric.sphere (0 : ℂ) 1 := by
      -- Convert the norm-square identity into sphere membership.
      rw [mem_sphere_iff_norm, sub_zero]
      have hsq : ‖w‖ ^ 2 = 1 := by
        simpa [Complex.sq_norm] using hw_normSq
      nlinarith [norm_nonneg w]
    have hw_image : w ∈ circleMap 0 1 '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
      -- One full period of the unit circle parametrization reaches every point on the unit circle.
      rw [circleMapImage_eq_range, range_circleMap_eq_unitSphere]
      exact hw_sphere
    rcases hw_image with ⟨t, ht, htw⟩
    refine ⟨t, ht, ?_⟩
    change ellipseAxisMap a b (circleMap 0 1 t) = z
    rw [htw]
    apply Complex.ext
    · simp [ellipseAxisMap, w]
      field_simp [ha]
    · simp [ellipseAxisMap, w]
      field_simp [hb]

/-- Helper for Cartan section06 0021_Exercise_6: the ellipse interpolation through positive
semiaxes gives a closed-path homotopy from the standard unit circle to `ellipsePath a b` inside
`ℂ \ {0}`. -/
private theorem ellipsePath_homotopic_standardCircleIn_compl_zero
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ClosedPathHomotopicIn ({0} : Set ℂ)ᶜ (standardCirclePath 1) (ellipsePath a b) := by
  let F : ContinuousMap.Homotopy (standardCirclePath 1 : C(I, ℂ)) (ellipsePath a b : C(I, ℂ)) :=
    { toFun := fun p : I × I ↦
        ellipseParam ((1 - (p.1 : ℝ)) + (p.1 : ℝ) * a) ((1 - (p.1 : ℝ)) + (p.1 : ℝ) * b)
          (2 * Real.pi * (p.2 : ℝ))
      continuous_toFun := by
        simpa [ellipseParam_apply] using
          (by
            fun_prop :
              Continuous fun p : I × I ↦
                (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * a) * Real.cos (2 * Real.pi * (p.2 : ℝ)) : ℂ) +
                  ((((1 - (p.1 : ℝ)) + (p.1 : ℝ) * b) * Real.sin (2 * Real.pi * (p.2 : ℝ))) :
                    ℂ) * Complex.I)
      map_zero_left := by
        intro t
        -- At `s = 0` the interpolated semiaxes are both `1`, so we recover the standard circle.
        have hcircle : ellipseParam 1 1 (2 * Real.pi * (t : ℝ)) = standardCirclePath 1 t := by
          calc
            ellipseParam 1 1 (2 * Real.pi * (t : ℝ)) =
                Real.cos (2 * Real.pi * (t : ℝ)) +
                  Real.sin (2 * Real.pi * (t : ℝ)) * Complex.I := by
                  simp [ellipseParam_apply]
            _ = standardCirclePath 1 t := by
              rw [standardCirclePath_apply, circleMap, Complex.exp_mul_I]
              simp
        simpa using hcircle
      map_one_left := by
        intro t
        -- At `s = 1` the interpolated semiaxes are `a` and `b`, which is exactly `ellipsePath`.
        simp [ellipsePath_apply] }
  refine ⟨{ toHomotopy := F, prop' := ?_ }⟩
  intro s
  rw [isClosedPathIn_compl_iff]
  constructor
  · -- Each horizontal slice closes because `θ = 0` and `θ = 2π` give the same ellipse point.
    simp [IsClosedPath, F, ellipseParam_apply]
  · intro t
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hc : 0 < (1 - (s : ℝ)) + (s : ℝ) * a := by
      by_cases hsEq : (s : ℝ) = 1
      · simp [hsEq, ha]
      · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hsEq
        have h1ms : 0 < 1 - (s : ℝ) := sub_pos.mpr hslt
        have hsa : 0 ≤ (s : ℝ) * a := mul_nonneg hs0 ha.le
        linarith
    have hd : 0 < (1 - (s : ℝ)) + (s : ℝ) * b := by
      by_cases hsEq : (s : ℝ) = 1
      · simp [hsEq, hb]
      · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hsEq
        have h1ms : 0 < 1 - (s : ℝ) := sub_pos.mpr hslt
        have hsb : 0 ≤ (s : ℝ) * b := mul_nonneg hs0 hb.le
        linarith
    -- Positive semiaxes force the real and imaginary coordinates to vanish simultaneously only if
    -- both `cos` and `sin` vanish, which never happens.
    change
      ellipseParam ((1 - (s : ℝ)) + (s : ℝ) * a) ((1 - (s : ℝ)) + (s : ℝ) * b)
        (2 * Real.pi * (t : ℝ)) ≠ 0
    intro hzero
    have hRe0 := congrArg Complex.re hzero
    have hIm0 := congrArg Complex.im hzero
    rw [ellipseParam_apply] at hRe0 hIm0
    have hRe' :
        ((1 - (s : ℝ)) + (s : ℝ) * a) * (Complex.cos (2 * Real.pi * (t : ℝ))).re -
          ((1 - (s : ℝ)) + (s : ℝ) * b) * (Complex.sin (2 * Real.pi * (t : ℝ))).im = 0 := by
      simpa [Complex.add_re, Complex.mul_re] using hRe0
    have hIm' :
        ((1 - (s : ℝ)) + (s : ℝ) * a) * (Complex.cos (2 * Real.pi * (t : ℝ))).im +
          ((1 - (s : ℝ)) + (s : ℝ) * b) * (Complex.sin (2 * Real.pi * (t : ℝ))).re = 0 := by
      simpa [Complex.add_im, Complex.mul_im] using hIm0
    have hsinIm : (Complex.sin (2 * Real.pi * (t : ℝ))).im = 0 := by
      simpa using Complex.sin_ofReal_im (2 * Real.pi * (t : ℝ))
    have hcosIm : (Complex.cos (2 * Real.pi * (t : ℝ))).im = 0 := by
      simpa using Complex.cos_ofReal_im (2 * Real.pi * (t : ℝ))
    have hReEq : ((1 - (s : ℝ)) + (s : ℝ) * a) * (Complex.cos (2 * Real.pi * (t : ℝ))).re = 0 := by
      simpa [hsinIm] using hRe'
    have hImEq : ((1 - (s : ℝ)) + (s : ℝ) * b) * (Complex.sin (2 * Real.pi * (t : ℝ))).re = 0 := by
      simpa [hcosIm] using hIm'
    have hcosRe : (Complex.cos (2 * Real.pi * (t : ℝ))).re = 0 :=
      (mul_eq_zero.mp hReEq).resolve_left hc.ne'
    have hsinRe : (Complex.sin (2 * Real.pi * (t : ℝ))).re = 0 :=
      (mul_eq_zero.mp hImEq).resolve_left hd.ne'
    have harg : (2 * (Real.pi : ℂ) * (t : ℝ)) = (((2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) := by
      norm_num
    have hcos : Real.cos (2 * Real.pi * (t : ℝ)) = 0 := by
      rw [harg, Complex.cos_ofReal_re] at hcosRe
      exact hcosRe
    have hsin : Real.sin (2 * Real.pi * (t : ℝ)) = 0 := by
      rw [harg, Complex.sin_ofReal_re] at hsinRe
      exact hsinRe
    nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * (t : ℝ))]

/-- Helper for Cartan section06 0021_Exercise_6: `ellipseParam` has the expected complex
derivative. -/
private theorem hasDerivAt_ellipseParam (a b t : ℝ) :
    HasDerivAt (ellipseParam a b) (-a * Real.sin t + (b * Real.cos t) * Complex.I) t := by
  -- Rewrite `ellipseParam` through complex sine and cosine so the standard derivative theorems
  -- apply directly.
  have hfun :
      (fun y : ℝ ↦ (a : ℂ) * Complex.cos y + Complex.I * ((b : ℂ) * Complex.sin y)) =
        ellipseParam a b := by
    funext y
    simp [ellipseParam_apply, Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  rw [← hfun]
  simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
    (((Real.hasDerivAt_cos t).ofReal_comp.mul_const (a : ℂ)).add
      (((Real.hasDerivAt_sin t).ofReal_comp.mul_const (b : ℂ)).const_mul Complex.I))

/-- Helper for Cartan section06 0021_Exercise_6: the ellipse parametrization never hits the
origin when `a, b > 0`. -/
private theorem ellipseParam_ne_zero (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseParam a b t ≠ 0 := by
  -- Vanishing would force both rescaled coordinates to vanish, contradicting
  -- `cos^2 t + sin^2 t = 1`.
  rw [ellipseParam_apply]
  intro hzero
  have hRe0 := congrArg Complex.re hzero
  have hIm0 := congrArg Complex.im hzero
  have hRe : a * Real.cos t = 0 := by
    simpa using hRe0
  have hIm : b * Real.sin t = 0 := by
    simpa using hIm0
  have hcos : Real.cos t = 0 := (mul_eq_zero.mp hRe).resolve_left ha.ne'
  have hsin : Real.sin t = 0 := (mul_eq_zero.mp hIm).resolve_left hb.ne'
  nlinarith [Real.cos_sq_add_sin_sq t]

/-- Helper for Cartan section06 0021_Exercise_6: the imaginary part of the logarithmic derivative
of the ellipse parametrization is the reciprocal quadratic integrand up to the factor `ab`. -/
private theorem im_logDeriv_ellipseParam (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Complex.im (logDeriv (ellipseParam a b) t) =
      (a * b) / (a ^ 2 * Real.cos t ^ 2 + b ^ 2 * Real.sin t ^ 2) := by
  have hne : ellipseParam a b t ≠ 0 := ellipseParam_ne_zero a b t ha hb
  -- Expand the logarithmic derivative and use the explicit quotient formula for the imaginary
  -- part of a complex division.
  rw [logDeriv_apply, (hasDerivAt_ellipseParam a b t).deriv, Complex.div_im, ellipseParam_apply]
  simp [Complex.normSq_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re, sq,
    mul_assoc, mul_left_comm, mul_comm]
  ring_nf
  let d : ℝ := a ^ 2 * Real.cos t ^ 2 + b ^ 2 * Real.sin t ^ 2
  calc
    a * b * Real.cos t ^ 2 * d⁻¹ + a * b * Real.sin t ^ 2 * d⁻¹ =
        a * b * (Real.cos t ^ 2 + Real.sin t ^ 2) * d⁻¹ := by
      ring
    _ = a * b * d⁻¹ := by
      rw [Real.cos_sq_add_sin_sq]
      ring
    _ = (a * b) / (a ^ 2 * Real.cos t ^ 2 + b ^ 2 * Real.sin t ^ 2) := by
      rfl

/-- For nonzero axis parameters `a` and `b`, the closed path `ellipsePath a b` traces exactly the
ellipse cut out by the quadratic equation with semiaxes `|a|` and `|b|`. -/
-- Proof sketch: the map `ellipseAxisMap a b` carries the unit circle onto the ellipse whenever
-- `a, b ≠ 0`, and `ellipsePath a b` is that map applied to the standard unit circle
-- path.
theorem range_ellipsePath_eq_ellipse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Set.range (ellipsePath a b) =
      {z : ℂ | z.re ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 = 1} := by
  -- First identify the closed-path range with the textbook parameter image, then invoke the
  -- geometric image computation already proved above.
  rw [range_ellipsePath_eq_image_ellipseParamIcc]
  exact ellipseParamImage_eq_ellipse a b ha hb

/- The parametrization `ellipseParam a b` traces exactly the same ellipse over the interval
`[0, 2π]` when `a` and `b` are nonzero. -/
-- Proof sketch: reparametrize the closed path `ellipsePath a b` by
-- `t = θ / (2π)` and use
-- `range_ellipsePath_eq_ellipse`; only nonvanishing of the semiaxes is needed for the set
-- equality.
theorem image_ellipseParam_eq_ellipse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseParam a b '' Set.Icc (0 : ℝ) (2 * Real.pi) =
      {z : ℂ | z.re ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 = 1} := by
  -- This is exactly the normalized-image helper established for the explicit parametrization.
  exact ellipseParamImage_eq_ellipse a b ha hb

/-- Cartan section06 0021_Exercise_6: integrating `dz / z` along the positively oriented ellipse
gives `2π i`. -/
-- Proof sketch: `ellipsePath a b` is a positively oriented closed loop around the
-- origin when
-- `a, b > 0`; compute its contour integral from the winding index of the ellipse about `0`.
theorem curveIntegral_inv_ellipsePath_eq_two_pi_I (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ᶜ z in ellipsePath a b, indexForm 0 z =
      (2 * Real.pi * Complex.I : ℂ) := by
  -- Compare the ellipse index with the standard circle through the punctured-plane homotopy, then
  -- clear the normalizing factor `2π i`.
  have hHom :
      ClosedPathHomotopicIn ({0} : Set ℂ)ᶜ (standardCirclePath 1) (ellipsePath a b) :=
    ellipsePath_homotopic_standardCircleIn_compl_zero a b ha hb
  have hIndexEq :
      (standardCirclePath 1).closedPathIndexAt 0
          (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hHom) =
        (ellipsePath a b).closedPathIndexAt 0
          (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hHom) :=
    closedPathIndex_eq_of_homotopic_avoiding_point hHom
  have hCircleIndex :
      (standardCirclePath 1).closedPathIndexAt 0
          (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hHom) = 1 := by
    -- Reuse the unit-circle index theorem and then normalize the omitted-point witness.
    have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
      simp [Metric.mem_ball]
    have hCircleIndexBall :
        (standardCirclePath 1).closedPathIndexAt 0
            (standardCirclePath_not_mem_range_of_mem_ball 1 hzero_mem) = 1 :=
      closedPathIndex_standardCircle_eq_one_of_mem_ball 1 0 hzero_mem
    simpa [Path.closedPathIndexAt_def] using hCircleIndexBall
  have hEllipseIndex :
      (ellipsePath a b).closedPathIndexAt 0
          (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hHom) = 1 := by
    exact hIndexEq.symm.trans hCircleIndex
  have hIntegralDiv :
      (∫ᶜ z in ellipsePath a b, indexForm 0 z) / (((2 * Real.pi : ℂ) * Complex.I)) = 1 := by
    simpa [closedPathIndex_def, Path.closedPathIndexAt_def] using hEllipseIndex
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (div_eq_iff Complex.two_pi_I_ne_zero).1 hIntegralDiv

/-- Integrating the logarithmic derivative of the ellipse parametrization once around the ellipse
returns `2π i`. -/
-- Proof sketch: reparametrize the contour integral on `ellipsePath a b` by
-- `θ = 2π t`, then rewrite the integrand with mathlib's canonical `logDeriv`.
theorem integral_logDeriv_ellipseParam (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), logDeriv (ellipseParam a b) t =
      (2 * Real.pi * Complex.I : ℂ) := by
  let h : ℝ → ℂ := fun θ ↦ logDeriv (ellipseParam a b) θ
  let g : ℝ → ℂ := fun s ↦ ellipseParam a b (s * (2 * Real.pi))
  have hbridge :
      ∫ᶜ z in ellipsePath a b, indexForm 0 z =
        ∫ t in (0 : ℝ)..(2 * Real.pi), logDeriv (ellipseParam a b) t := by
    have hcongr_ae :
        (fun t ↦ indexForm 0 ((ellipsePath a b).extend t) (deriv ((ellipsePath a b).extend) t))
          =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
            (fun t ↦ (2 * Real.pi : ℝ) • h (t * (2 * Real.pi))) := by
      rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hlocal : (ellipsePath a b).extend =ᶠ[nhds t] g := by
        have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
        filter_upwards [hIoo] with s hs
        rw [Path.extend_apply (ellipsePath a b) ⟨hs.1.le, hs.2.le⟩, ellipsePath_apply]
        simp [g, mul_comm]
      have hgDeriv :
          HasDerivAt g
            (-(2 * Real.pi * a * Real.sin (t * (2 * Real.pi))) +
              ((2 * Real.pi * b * Real.cos (t * (2 * Real.pi)))) * Complex.I) t := by
        change HasDerivAt (ellipseParam a b ∘ fun x ↦ x * (2 * Real.pi))
          (-(2 * Real.pi * a * Real.sin (t * (2 * Real.pi))) +
            ((2 * Real.pi * b * Real.cos (t * (2 * Real.pi)))) * Complex.I) t
        simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_ellipseParam a b (t * (2 * Real.pi))).scomp t
            (hasDerivAt_mul_const (2 * Real.pi : ℝ)))
      have hderiv :
          deriv (ellipsePath a b).extend t =
            -(2 * Real.pi * a * Real.sin (t * (2 * Real.pi))) +
              ((2 * Real.pi * b * Real.cos (t * (2 * Real.pi)))) * Complex.I := by
        rw [Filter.EventuallyEq.deriv_eq hlocal]
        simpa using hgDeriv.deriv
      have hext : (ellipsePath a b).extend t = g t :=
        Filter.EventuallyEq.eq_of_nhds hlocal
      calc
        indexForm 0 ((ellipsePath a b).extend t) (deriv ((ellipsePath a b).extend) t) =
            indexForm 0 (g t)
              (-(2 * Real.pi * a * Real.sin (t * (2 * Real.pi))) +
                ((2 * Real.pi * b * Real.cos (t * (2 * Real.pi)))) * Complex.I) := by
          rw [hext, hderiv]
        _ = (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
          change
            indexForm 0 (g t)
                (-(2 * Real.pi * a * Real.sin (t * (2 * Real.pi))) +
                  ((2 * Real.pi * b * Real.cos (t * (2 * Real.pi)))) * Complex.I) =
              (2 * Real.pi : ℝ) • logDeriv (ellipseParam a b) (t * (2 * Real.pi))
          rw [logDeriv_apply, (hasDerivAt_ellipseParam a b (t * (2 * Real.pi))).deriv]
          simp [g, indexForm, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_comm]
          ring
    have hcongr :
        ∫ t in (0 : ℝ)..1,
            indexForm 0 ((ellipsePath a b).extend t) (deriv ((ellipsePath a b).extend) t) =
          ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) :=
      intervalIntegral.integral_congr_ae_restrict hcongr_ae
    have hsmul :
        ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) =
          (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := by
      exact intervalIntegral.integral_smul (a := (0 : ℝ)) (b := 1)
        (r := (2 * Real.pi : ℝ)) (f := fun t ↦ h (t * (2 * Real.pi)))
    -- Rewrite the contour integral as an interval integral on `[0,1]`, then perform the
    -- `θ = 2π t` change of variables.
    rw [curveIntegral_eq_intervalIntegral_deriv]
    calc
      ∫ t in (0 : ℝ)..1,
          indexForm 0 ((ellipsePath a b).extend t) (deriv ((ellipsePath a b).extend) t) =
        ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := hcongr
      _ = (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := hsmul
      _ = ∫ θ in (0 : ℝ) * (2 * Real.pi)..1 * (2 * Real.pi), h θ := by
        simpa using
          (intervalIntegral.smul_integral_comp_mul_right
            (f := h) (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi))
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, h θ := by
        simp
      _ = ∫ t in (0 : ℝ)..(2 * Real.pi), logDeriv (ellipseParam a b) t := by
        rfl
  -- The contour integral was already computed from the winding number of the ellipse.
  exact hbridge.symm.trans (curveIntegral_inv_ellipsePath_eq_two_pi_I a b ha hb)

/-- Helper for Cartan section06 0021_Exercise_6: for positive semiaxes `a` and `b`, the standard
ellipse parametrization yields
`∫_0^{2π} dt / (a^2 cos^2 t + b^2 sin^2 t) = 2π / (ab)`. -/
-- Proof sketch: expand `logDeriv (ellipseParam a b) t`, isolate its imaginary part as
-- `ab / (a^2 cos^2 t + b^2 sin^2 t)`, and compare the resulting integral with
-- `integral_logDeriv_ellipseParam`.
theorem ellipse_reciprocal_quadratic_integral_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), 1 / (a ^ 2 * Real.cos t ^ 2 + b ^ 2 * Real.sin t ^ 2) =
      2 * Real.pi / (a * b) := by
  let f : ℝ → ℂ := fun t ↦ logDeriv (ellipseParam a b) t
  let q : ℝ → ℝ := fun t ↦ a ^ 2 * Real.cos t ^ 2 + b ^ 2 * Real.sin t ^ 2
  have hlogEq :
      f =
        fun t ↦
          (-a * Real.sin t + (b * Real.cos t) * Complex.I) /
            (a * Real.cos t + (b * Real.sin t) * Complex.I) := by
    funext t
    simp [f, logDeriv_apply, (hasDerivAt_ellipseParam a b t).deriv, ellipseParam_apply]
  have hcont : Continuous f := by
    rw [hlogEq]
    refine Continuous.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t
      simpa [ellipseParam_apply] using ellipseParam_ne_zero a b t ha hb
  have hInt : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable hcont 0 (2 * Real.pi)
  have himComm :
      ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.imCLM (f t) =
        Complex.im (∫ t in (0 : ℝ)..(2 * Real.pi), f t) := by
    simpa [Function.comp, f] using
      Complex.imCLM.intervalIntegral_comp_comm (f := f) hInt
  have himValue :
      Complex.im (∫ t in (0 : ℝ)..(2 * Real.pi), f t) = 2 * Real.pi := by
    simpa [f, Complex.mul_I_im] using
      congrArg Complex.im (integral_logDeriv_ellipseParam a b ha hb)
  have hweighted :
      ∫ t in (0 : ℝ)..(2 * Real.pi), (a * b) / q t = 2 * Real.pi := by
    calc
      ∫ t in (0 : ℝ)..(2 * Real.pi), (a * b) / q t =
        ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.imCLM (f t) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [] with t
          simp [f, q, im_logDeriv_ellipseParam a b t ha hb]
      _ = Complex.im (∫ t in (0 : ℝ)..(2 * Real.pi), f t) := himComm
      _ = 2 * Real.pi := himValue
  have hscale :
      ∫ t in (0 : ℝ)..(2 * Real.pi), (a * b) / q t =
        (a * b) * ∫ t in (0 : ℝ)..(2 * Real.pi), 1 / q t := by
    calc
      ∫ t in (0 : ℝ)..(2 * Real.pi), (a * b) / q t =
          ∫ t in (0 : ℝ)..(2 * Real.pi), (a * b) * (1 / q t) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            simp [div_eq_mul_inv]
      _ = (a * b) * ∫ t in (0 : ℝ)..(2 * Real.pi), 1 / q t := by
            exact intervalIntegral.integral_const_mul (a * b) (fun t ↦ 1 / q t)
              (a := (0 : ℝ)) (b := 2 * Real.pi)
  have hscaled :
      (a * b) * ∫ t in (0 : ℝ)..(2 * Real.pi), 1 / q t = 2 * Real.pi :=
    hscale.symm.trans hweighted
  have hab_ne : a * b ≠ 0 := mul_ne_zero ha.ne' hb.ne'
  exact (eq_div_iff hab_ne).2 <| by
    simpa [q, mul_assoc, mul_left_comm, mul_comm] using hscaled
