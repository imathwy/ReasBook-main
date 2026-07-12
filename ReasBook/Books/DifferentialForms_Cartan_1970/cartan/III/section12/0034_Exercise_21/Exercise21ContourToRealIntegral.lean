import DifferentialForms_Cartan_1970.III.section12.SectorArc
import DifferentialForms_Cartan_1970.III.section12.«0034_Exercise_21».NegativeAxisKeyholeBranchGeometry

noncomputable section

open Complex MeasureTheory
open scoped Real

/-- Helper for Cartan section12 0034_Exercise_21: the real kernel appearing in the improper
integral on `(0, ∞)`. -/
def exercise21TargetKernel (a x : ℝ) : ℝ :=
  1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2))

/-- Helper for Cartan section12 0034_Exercise_21: after the reciprocal change of variables
`x = 1 / t`, the lower truncated tail of `exercise21TargetKernel` becomes this kernel on
`[1, ∞)`. -/
def exercise21ReciprocalTailKernel (a t : ℝ) : ℝ :=
  1 / ((1 + a ^ 2 * t ^ 2) * ((Real.log t) ^ 2 + Real.pi ^ 2))

/-- Helper for Cartan section12 0034_Exercise_21: the paired upper-minus-lower slit-lip kernel at
branch angle `α`. -/
def exercise21LipPairKernel (a α x : ℝ) : ℂ :=
  Complex.exp (-α * Complex.I) /
      ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
        (Real.log x - α * Complex.I)) -
    Complex.exp (α * Complex.I) /
      ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
        (Real.log x + α * Complex.I))

/-- Helper for Cartan section12 0034_Exercise_21: the reciprocal substitution `x = 1 / t`
transforms the target kernel with its Jacobian factor into the explicit upper-tail kernel. -/
lemma exercise21TargetKernel_comp_inv_mul_invSq
    (a t : ℝ) (ht : 0 < t) :
    exercise21TargetKernel a (t⁻¹) * (t ^ 2)⁻¹ = exercise21ReciprocalTailKernel a t := by
  -- Rewrite `log (t⁻¹)` as `-log t`; the remaining identity is pure rational simplification.
  simp [exercise21TargetKernel, exercise21ReciprocalTailKernel, Real.log_inv, pow_two]
  field_simp [ht.ne']

/-- Helper for Cartan section12 0034_Exercise_21: at the limiting angle `α = π`, the paired
slit-lip kernel collapses exactly to `-(2π i)` times the real target kernel. -/
lemma exercise21LipPairKernel_pi
    (a x : ℝ) (hx : 0 < x) :
    exercise21LipPairKernel a Real.pi x =
      (-(2 * Real.pi * Complex.I : ℂ)) * (exercise21TargetKernel a x : ℂ) := by
  have hnegpi : Complex.exp (-Real.pi * Complex.I) = (-1 : ℂ) := by
    -- The negative branch angle is the inverse of `exp (π i) = -1`, hence also `-1`.
    simpa [Complex.exp_pi_mul_I] using (Complex.exp_neg (Real.pi * Complex.I))
  -- At angle `π`, both rotated slit points are just `-x`, so only the conjugate logarithmic
  -- denominators remain.
  rw [exercise21LipPairKernel, exercise21TargetKernel, Complex.exp_pi_mul_I, hnegpi]
  rw [Complex.ext_iff]
  constructor
  · -- The real parts cancel, leaving only the purely imaginary target contribution.
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re,
      Complex.add_im, Complex.sub_im, Complex.normSq, pow_two]
  · -- The imaginary parts add to `-2`, which produces the factor `-(2π i)`.
    simp [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re,
      Complex.add_im, Complex.sub_im, Complex.normSq, pow_two]
    field_simp [Real.pi_ne_zero]
    ring

/-- Helper for Cartan section12 0034_Exercise_21: along a positive ray with admissible angle, the
principal logarithm splits into the real logarithm of the radius plus the angular term. -/
lemma exercise21_log_circleMap_of_pos
    {x α : ℝ} (hx : 0 < x) (hα : α ∈ Set.Ioo (-Real.pi) Real.pi) :
    Complex.log (circleMap 0 x α) = Real.log x + α * Complex.I := by
  -- Factor the ray point as a positive real scalar times `exp (α i)`, then evaluate the branch
  -- logarithm of that exponential in the principal strip.
  rw [circleMap_zero, Complex.log_ofReal_mul hx (Complex.exp_ne_zero _)]
  simpa using
    (Complex.log_exp (x := (α : ℂ) * Complex.I) (by simpa using hα.1) (by simpa using hα.2.le))

/-- Helper for Cartan section12 0034_Exercise_21: a fixed-angle radial segment already carries the
radius as its integration variable, so its curve integral is exactly the corresponding interval
integral in that radius. -/
lemma exercise21RadialLip_curveIntegral_eq_intervalIntegral
    (a ρ₀ ρ₁ α : ℝ)
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (hα : α ∈ Set.Ioo (-Real.pi) Real.pi) :
    ∫ᶜ z in Path.segment (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α),
      (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
      ∫ x in ρ₀..ρ₁,
        Complex.exp (α * Complex.I) /
          ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x + α * Complex.I)) := by
  let g : ℝ → ℂ := fun x ↦
    Complex.exp (α * Complex.I) /
      ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
        (Real.log x + α * Complex.I))
  -- Route correction: rewrite the segment directly with `curveIntegral_segment`, then transport
  -- the affine radius parameter to the interval `ρ₀..ρ₁`.
  rw [curveIntegral_segment]
  have hcongr :
      ∫ t in (0 : ℝ)..1,
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
            (AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t))
            (circleMap 0 ρ₁ α - circleMap 0 ρ₀ α) =
        ∫ t in (0 : ℝ)..1, (ρ₁ - ρ₀ : ℝ) • g (AffineMap.lineMap ρ₀ ρ₁ t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using ht
    have hρmem : AffineMap.lineMap ρ₀ ρ₁ t ∈ Set.uIcc ρ₀ ρ₁ := by
      simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ ρ₀ ρ₁ htI
    have hρpos : 0 < AffineMap.lineMap ρ₀ ρ₁ t := by
      have hmin : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
      exact lt_of_lt_of_le hmin hρmem.1
    have hline :
        AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t =
          circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ t) α :=
      exercise21_lineMap_circleMap_same_angle ρ₀ ρ₁ α t
    have hdir :
        circleMap 0 ρ₁ α - circleMap 0 ρ₀ α =
          ((ρ₁ - ρ₀ : ℝ) : ℂ) * Complex.exp (α * Complex.I) := by
      rw [circleMap_zero, circleMap_zero]
      calc
        (ρ₁ : ℂ) * Complex.exp (α * Complex.I) - (ρ₀ : ℂ) * Complex.exp (α * Complex.I) =
            (((ρ₁ : ℂ) - (ρ₀ : ℂ)) * Complex.exp (α * Complex.I)) := by
              ring
        _ = (((ρ₁ - ρ₀ : ℝ) : ℂ) * Complex.exp (α * Complex.I)) := by
              simp
    have hlog :
        Complex.log ((((AffineMap.lineMap ρ₀ ρ₁ t : ℝ) : ℂ) * Complex.exp (α * Complex.I))) =
          Real.log (AffineMap.lineMap ρ₀ ρ₁ t) + α * Complex.I := by
      simpa [circleMap_zero] using
        (exercise21_log_circleMap_of_pos
          (x := AffineMap.lineMap ρ₀ ρ₁ t) (α := α) hρpos hα)
    -- Evaluate the scalar one-form on the ray tangent and then normalize the logarithm.
    have hpoint :
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
            (AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t))
            (circleMap 0 ρ₁ α - circleMap 0 ρ₀ α) =
          (ρ₁ - ρ₀ : ℝ) • g (AffineMap.lineMap ρ₀ ρ₁ t) := by
      rw [Complex.scalarOneForm_apply, hline, hdir, circleMap_zero, hlog]
      simp [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    simpa using hpoint
  calc
    ∫ t in (0 : ℝ)..1,
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
          (AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t))
          (circleMap 0 ρ₁ α - circleMap 0 ρ₀ α) =
      ∫ t in (0 : ℝ)..1, (ρ₁ - ρ₀ : ℝ) • g (AffineMap.lineMap ρ₀ ρ₁ t) := hcongr
    _ = ∫ x in (ρ₁ - ρ₀) * (0 : ℝ) + ρ₀..(ρ₁ - ρ₀) * 1 + ρ₀, g x := by
          simpa [AffineMap.lineMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm] using
            (intervalIntegral.smul_integral_comp_mul_add
              (f := g) (a := (0 : ℝ)) (b := 1) (c := ρ₁ - ρ₀) (d := ρ₀))
    _ = ∫ x in ρ₀..ρ₁, g x := by
          simp
    _ = ∫ x in ρ₀..ρ₁,
          Complex.exp (α * Complex.I) /
            ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x + α * Complex.I)) := by
          rfl

/-- Helper for Cartan section12 0034_Exercise_21: the upper slit lip traverses the radial window in
the reverse direction, so rewriting it in the common variable contributes the negative of the
forward interval integral. -/
lemma exercise21UpperLip_curveIntegral_eq_intervalIntegral
    (a R α : ℝ) (hR : 0 < R) (hα : α ∈ Set.Ioo (-Real.pi) Real.pi) :
    ∫ᶜ z in Path.segment (circleMap 0 R α) (circleMap 0 (1 / R) α),
      (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
      -∫ x in (1 / R)..R,
        Complex.exp (α * Complex.I) /
          ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x + α * Complex.I)) := by
  -- Reverse the interval orientation so the two slit lips share the same truncation interval.
  rw [exercise21RadialLip_curveIntegral_eq_intervalIntegral a R (1 / R) α hR
    (one_div_pos.mpr hR) hα, intervalIntegral.integral_symm]

/-- Helper for Cartan section12 0034_Exercise_21: the lower slit lip already runs along the common
radial interval in the forward direction, and only the branch angle changes sign. -/
lemma exercise21LowerLip_curveIntegral_eq_intervalIntegral
    (a R α : ℝ) (hR : 0 < R) (hα : α ∈ Set.Ioo (-Real.pi) Real.pi) :
    ∫ᶜ z in Path.segment (circleMap 0 (1 / R) (-α)) (circleMap 0 R (-α)),
      (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
      ∫ x in (1 / R)..R,
        Complex.exp (-α * Complex.I) /
          ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x - α * Complex.I)) := by
  -- This is the same radial rewrite specialized to the lower branch angle `-α`.
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
    exercise21RadialLip_curveIntegral_eq_intervalIntegral a (1 / R) R (-α)
      (one_div_pos.mpr hR) hR ⟨by simpa using neg_lt_neg hα.2, by simpa using neg_lt_neg hα.1⟩

/-- Helper for Cartan section12 0034_Exercise_21: a circle segment obtained by mapping an angular
segment through `circleMap` is exactly the corresponding chapter-local sector-arc integral. -/
lemma exercise21CircleArc_curveIntegral_eq_sectorArcIntegral
    (g : ℂ → ℂ) (ρ α β : ℝ) :
    ∫ᶜ z in ((Path.segment α β).map (continuous_circleMap 0 ρ)), (g dz) z =
      sectorArcIntegral g ρ α β := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (g dz) z
  let h : ℝ → ℂ := fun θ ↦ ω (circleMap 0 ρ θ) (deriv (circleMap 0 ρ) θ)
  have hcongr_ae :
      (fun t : ℝ ↦
        ω ((((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t))
          (deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t))
        =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
          (fun t ↦ (β - α : ℝ) • h ((β - α) * t + α)) := by
    rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hlocal :
        (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) =ᶠ[nhds t]
          fun s : ℝ ↦ circleMap 0 ρ (((β - α) * s + α)) := by
      have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [hIoo] with s hs
      rw [Path.extend_apply (((Path.segment α β).map (continuous_circleMap 0 ρ)))
        ⟨hs.1.le, hs.2.le⟩]
      simp [Path.map_coe, Path.segment_apply, AffineMap.lineMap_apply_module, sub_eq_add_neg]
      ring_nf
    have hderiv :
        deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t =
          ((β - α : ℝ) : ℂ) * deriv (circleMap 0 ρ) (((β - α) * t + α)) := by
      rw [Filter.EventuallyEq.deriv_eq hlocal]
      simpa using
        (((hasDerivAt_circleMap 0 ρ (((β - α) * t + α))).scomp t
          (((hasDerivAt_id t).const_mul (β - α)).add_const α)).deriv)
    have hext :
        (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t) =
          circleMap 0 ρ (((β - α) * t + α)) :=
      Filter.EventuallyEq.eq_of_nhds hlocal
    -- Evaluate the complex scalar one-form against the chain-rule tangent of the angular segment.
    calc
      ω ((((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t))
          (deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t) =
        ω (circleMap 0 ρ (((β - α) * t + α)))
          (((β - α : ℝ) : ℂ) * deriv (circleMap 0 ρ) (((β - α) * t + α))) := by
            rw [hext, hderiv]
      _ = (β - α : ℝ) • h (((β - α) * t + α)) := by
            simp [h, ω, smul_eq_mul, mul_comm, mul_left_comm]
  -- Route correction: rewrite the path integral by `curveIntegral_eq_intervalIntegral_deriv`,
  -- then transport the affine angle parameter directly to the sector-arc owner.
  rw [curveIntegral_eq_intervalIntegral_deriv, sectorArcIntegral]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t))
          (deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t) =
      ∫ t in (0 : ℝ)..1, (β - α : ℝ) • h ((β - α) * t + α) := by
        exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
    _ = (β - α : ℝ) • ∫ t in (0 : ℝ)..1, h ((β - α) * t + α) := by
        rw [intervalIntegral.integral_smul]
    _ = ∫ θ in (β - α) * (0 : ℝ) + α..(β - α) * 1 + α, h θ := by
        simpa using
          (intervalIntegral.smul_integral_comp_mul_add
            (f := h) (a := (0 : ℝ)) (b := 1) (c := β - α) (d := α))
    _ = ∫ θ in α..β, h θ := by
        simp

/-- Helper for Cartan section12 0034_Exercise_21: the real target kernel is continuous on the
positive half-line, where neither factor in the denominator vanishes. -/
lemma exercise21TargetKernel_continuousOn
    (a : ℝ) :
    ContinuousOn (exercise21TargetKernel a) (Set.Ioi (0 : ℝ)) := by
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · have hlog : ContinuousOn Real.log (Set.Ioi (0 : ℝ)) := by
      intro x hx
      exact (Real.continuousAt_log (show x ≠ 0 from hx.ne')).continuousWithinAt
    have hquad :
        ContinuousOn (fun x : ℝ ↦ x ^ 2 + a ^ 2) (Set.Ioi (0 : ℝ)) := by
      fun_prop
    have hlogSq :
        ContinuousOn (fun x : ℝ ↦ (Real.log x) ^ 2 + Real.pi ^ 2) (Set.Ioi (0 : ℝ)) := by
      exact (hlog.pow 2).add continuousOn_const
    simpa [exercise21TargetKernel] using hquad.mul hlogSq
  · intro x hx
    have hxpos : 0 < x := hx
    have hquadPos : 0 < x ^ 2 + a ^ 2 := by
      nlinarith [sq_pos_of_pos hxpos, sq_nonneg a]
    have hlogSqPos : 0 < (Real.log x) ^ 2 + Real.pi ^ 2 := by
      nlinarith [sq_nonneg (Real.log x), sq_pos_of_pos Real.pi_pos]
    exact mul_ne_zero hquadPos.ne' hlogSqPos.ne'

/-- Helper for Cartan section12 0034_Exercise_21: the real target kernel is absolutely integrable
on `(0, ∞)` because it is bounded near `0` and decays like `x⁻²` for `x ≥ 1`. -/
lemma exercise21TargetKernel_integrableOnIoi
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (exercise21TargetKernel a) (Set.Ioi (0 : ℝ)) volume := by
  let f : ℝ → ℝ := exercise21TargetKernel a
  have hcont : ContinuousOn f (Set.Ioi (0 : ℝ)) := exercise21TargetKernel_continuousOn a
  have hlowDom :
      IntegrableOn (fun _ : ℝ ↦ (1 / (a ^ 2 * Real.pi ^ 2) : ℝ)) (Set.Ioc (0 : ℝ) 1) volume := by
    exact
      (MeasureTheory.integrableOn_const
        (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
        (C := (1 / (a ^ 2 * Real.pi ^ 2) : ℝ))
        (hs := by simp))
  have hlow :
      IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume := by
    refine Integrable.mono' hlowDom
      ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hdenLower :
        a ^ 2 * Real.pi ^ 2 ≤
          (x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2) := by
      nlinarith [sq_nonneg x, sq_nonneg (Real.log x), sq_nonneg a, sq_pos_of_pos Real.pi_pos]
    have hdenPos :
        0 < (x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2) := by
      have hquadPos : 0 < x ^ 2 + a ^ 2 := by
        nlinarith [sq_pos_of_pos hx.1, sq_nonneg a]
      have hlogSqPos : 0 < (Real.log x) ^ 2 + Real.pi ^ 2 := by
        nlinarith [sq_nonneg (Real.log x), sq_pos_of_pos Real.pi_pos]
      exact mul_pos hquadPos hlogSqPos
    have hconstPos : 0 < a ^ 2 * Real.pi ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos Real.pi_pos]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact one_div_le_one_div_of_le hconstPos hdenLower
    · exact one_div_nonneg.mpr hdenPos.le
  have hpow :
      IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) volume := by
    simpa using
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := (1 : ℝ)) (by norm_num) zero_lt_one)
  have hhighDom :
      IntegrableOn (fun x : ℝ ↦ 1 / (x ^ 2 * Real.pi ^ 2)) (Set.Ioi (1 : ℝ)) volume := by
    have hpowZ :
        IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℤ)) (Set.Ioi (1 : ℝ)) volume := by
      simpa using hpow
    have hscaled :
        IntegrableOn (fun x : ℝ ↦ (1 / Real.pi ^ 2) * x ^ (-2 : ℤ)) (Set.Ioi (1 : ℝ)) volume :=
      hpowZ.const_mul (1 / Real.pi ^ 2)
    exact (MeasureTheory.integrableOn_congr_fun
      (s := Set.Ioi (1 : ℝ))
      (f := fun x : ℝ ↦ (1 / Real.pi ^ 2) * x ^ (-2 : ℤ))
      (g := fun x : ℝ ↦ 1 / (x ^ 2 * Real.pi ^ 2))
      (by
        intro x hx
        have hxpos : 0 < x := lt_trans zero_lt_one hx
        field_simp [hxpos.ne', Real.pi_ne_zero]
      )
      measurableSet_Ioi).1 hscaled
  have hhigh :
      IntegrableOn f (Set.Ioi (1 : ℝ)) volume := by
    refine Integrable.mono' hhighDom
      ((hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hxgt1 : 1 < x := hx
    have hxpos : 0 < x := lt_trans zero_lt_one hxgt1
    have hdenLower :
        x ^ 2 * Real.pi ^ 2 ≤
          (x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2) := by
      nlinarith [sq_nonneg a, sq_nonneg (Real.log x), sq_nonneg x]
    have hdenPos :
        0 < (x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2) := by
      have hquadPos : 0 < x ^ 2 + a ^ 2 := by
        nlinarith [sq_pos_of_pos hxpos, sq_nonneg a]
      have hlogSqPos : 0 < (Real.log x) ^ 2 + Real.pi ^ 2 := by
        nlinarith [sq_nonneg (Real.log x), sq_pos_of_pos Real.pi_pos]
      exact mul_pos hquadPos hlogSqPos
    have htarget :
        1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) ≤
          1 / (x ^ 2 * Real.pi ^ 2) := by
      have hxpiPos : 0 < x ^ 2 * Real.pi ^ 2 := by
        nlinarith [sq_pos_of_pos hxpos, sq_pos_of_pos Real.pi_pos]
      exact one_div_le_one_div_of_le hxpiPos hdenLower
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact htarget
    · exact one_div_nonneg.mpr hdenPos.le
  -- Split `(0, ∞)` at `1`; both pieces are integrable by the bounds above.
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hlow.union hhigh

/-- Helper for Cartan section12 0034_Exercise_21: if `cos σ` is nonnegative, then translating the
unit complex number `exp (σ i)` by a nonnegative real scalar keeps the norm at least `1`. -/
lemma exercise21_one_le_norm_exp_add_of_cos_nonneg
    (c σ : ℝ) (hc : 0 ≤ c) (hcos : 0 ≤ Real.cos σ) :
    1 ≤ ‖Complex.exp ((σ : ℂ) * Complex.I) + c‖ := by
  have hre :
      (Complex.exp ((σ : ℂ) * Complex.I) + c).re = Real.cos σ + c := by
    -- Read off the real part of the translated unit-circle point.
    simp [Complex.exp_ofReal_mul_I_re]
  have him :
      (Complex.exp ((σ : ℂ) * Complex.I) + c).im = Real.sin σ := by
    -- The imaginary part is unchanged by a real translation.
    simp [Complex.exp_ofReal_mul_I_im]
  have hsq : 1 ≤ ‖Complex.exp ((σ : ℂ) * Complex.I) + c‖ ^ 2 := by
    -- Expand the squared norm and use `sin^2 + cos^2 = 1`.
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith [sq_nonneg c, hcos, Real.sin_sq_add_cos_sq σ]
  have hnn : 0 ≤ ‖Complex.exp ((σ : ℂ) * Complex.I) + c‖ := norm_nonneg _
  nlinarith

/-- Helper for Cartan section12 0034_Exercise_21: if `cos σ` is nonnegative, then the affine
combination `1 + c * exp (σ i)` also has norm at least `1` for every nonnegative `c`. -/
lemma exercise21_one_le_norm_one_add_mul_exp_of_cos_nonneg
    (c σ : ℝ) (hc : 0 ≤ c) (hcos : 0 ≤ Real.cos σ) :
    1 ≤ ‖(1 : ℂ) + (c : ℂ) * Complex.exp ((σ : ℂ) * Complex.I)‖ := by
  have hre :
      (((1 : ℂ) + (c : ℂ) * Complex.exp ((σ : ℂ) * Complex.I))).re =
        1 + c * Real.cos σ := by
    -- Compute the real part of the affine combination explicitly.
    rw [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp
  have him :
      (((1 : ℂ) + (c : ℂ) * Complex.exp ((σ : ℂ) * Complex.I))).im =
        c * Real.sin σ := by
    -- The imaginary part is exactly the scaled sine term.
    rw [Complex.add_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp
  have hsq : 1 ≤ ‖(1 : ℂ) + (c : ℂ) * Complex.exp ((σ : ℂ) * Complex.I)‖ ^ 2 := by
    -- Expanding the squared norm leaves only nonnegative correction terms beyond `1`.
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith [sq_nonneg c, hcos, Real.sin_sq_add_cos_sq σ]
  have hnn : 0 ≤ ‖(1 : ℂ) + (c : ℂ) * Complex.exp ((σ : ℂ) * Complex.I)‖ := norm_nonneg _
  nlinarith

/-- Helper for Cartan section12 0034_Exercise_21: angles in `[3π/4, π]` have nonnegative doubled
cosine, which is the exact trigonometric regime needed for the near-`π` slit bounds. -/
lemma exercise21_cos_two_nonneg_of_threeQuarterPi_le
    {α : ℝ} (hαlower : 3 * Real.pi / 4 ≤ α) (hαupper : α ≤ Real.pi) :
    0 ≤ Real.cos (2 * α) := by
  -- Shift by `2π` so the doubled angle lands in `[-π/2, π/2]`, where `cos` is nonnegative.
  have hmem : 2 * α - 2 * Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [hαlower, Real.pi_pos]
    · nlinarith [hαupper, Real.pi_pos]
  have hcos' : 0 ≤ Real.cos (2 * α - 2 * Real.pi) := Real.cos_nonneg_of_mem_Icc hmem
  simpa [Real.cos_sub_two_pi] using hcos'

/-- Helper for Cartan section12 0034_Exercise_21: when `a ≠ 0`, the rotated quadratic denominator
factors out `a²` on the lower branch. -/
lemma exercise21_rotatedQuadratic_factor_left
    (a x σ : ℝ) (ha0 : a ≠ 0) :
    (((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2) =
      (a : ℂ) ^ 2 * ((1 : ℂ) + ((x / a) ^ 2 : ℝ) * Complex.exp ((2 * σ) * Complex.I)) := by
  -- Rewrite the exponential square as a doubled angle, then factor out `a²`.
  have hdiv : ((x / a) ^ 2 : ℝ) = x ^ 2 * a⁻¹ ^ 2 := by
    field_simp [ha0]
  have hcast :
      ((((x ^ 2 * a⁻¹ ^ 2 : ℝ)) : ℂ)) = (x : ℂ) ^ 2 * (a : ℂ)⁻¹ ^ 2 := by
    norm_num [pow_two]
  have haInv : (a : ℂ) ^ 2 * (a : ℂ)⁻¹ ^ 2 = 1 := by
    field_simp [ha0]
  calc
    (((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2) =
        (x : ℂ) ^ 2 * (Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2 := by
          ring
    _ = (x : ℂ) ^ 2 * Complex.exp ((2 * σ) * Complex.I) + (a : ℂ) ^ 2 := by
          rw [← Complex.exp_nat_mul]
          congr 1
          ring
    _ = (a : ℂ) ^ 2 * (((x : ℂ) ^ 2 * (a : ℂ)⁻¹ ^ 2) * Complex.exp ((2 * σ) * Complex.I) + 1) := by
          calc
            (x : ℂ) ^ 2 * Complex.exp ((2 * σ) * Complex.I) + (a : ℂ) ^ 2 =
                (x : ℂ) ^ 2 * Complex.exp ((2 * σ) * Complex.I) *
                    ((a : ℂ) ^ 2 * (a : ℂ)⁻¹ ^ 2) + (a : ℂ) ^ 2 := by
                      rw [haInv, mul_one]
            _ = (a : ℂ) ^ 2 * (((x : ℂ) ^ 2 * (a : ℂ)⁻¹ ^ 2) *
                  Complex.exp ((2 * σ) * Complex.I)) + (a : ℂ) ^ 2 := by
                    ring
            _ = (a : ℂ) ^ 2 * (((x : ℂ) ^ 2 * (a : ℂ)⁻¹ ^ 2) *
                  Complex.exp ((2 * σ) * Complex.I) + 1) := by
                    ring
    _ = (a : ℂ) ^ 2 * ((((x ^ 2 * a⁻¹ ^ 2 : ℝ)) : ℂ) * Complex.exp ((2 * σ) * Complex.I) + 1) := by
          rw [← hcast]
    _ = (a : ℂ) ^ 2 * ((((x / a) ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * σ) * Complex.I) + 1) := by
          rw [hdiv]
    _ = (a : ℂ) ^ 2 * ((1 : ℂ) + ((x / a) ^ 2 : ℝ) * Complex.exp ((2 * σ) * Complex.I)) := by
          ring

/-- Helper for Cartan section12 0034_Exercise_21: when `x ≠ 0`, the rotated quadratic denominator
factors out `x²` on the upper branch. -/
lemma exercise21_rotatedQuadratic_factor_right
    (a x σ : ℝ) (hx0 : x ≠ 0) :
    (((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2) =
      ((x : ℂ) ^ 2) * (Complex.exp ((2 * σ) * Complex.I) + (((a / x) ^ 2 : ℝ) : ℂ)) := by
  -- Rewrite the exponential square as a doubled angle, then factor out `x²`.
  have hdiv : ((a / x) ^ 2 : ℝ) = a ^ 2 * x⁻¹ ^ 2 := by
    field_simp [hx0]
  have hcast :
      ((((a ^ 2 * x⁻¹ ^ 2 : ℝ)) : ℂ)) = (a : ℂ) ^ 2 * (x : ℂ)⁻¹ ^ 2 := by
    norm_num [pow_two]
  have hxInv : (x : ℂ) ^ 2 * (x : ℂ)⁻¹ ^ 2 = 1 := by
    field_simp [hx0]
  calc
    (((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2) =
        (x : ℂ) ^ 2 * (Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2 := by
          ring
    _ = (x : ℂ) ^ 2 * Complex.exp ((2 * σ) * Complex.I) + (a : ℂ) ^ 2 := by
          rw [← Complex.exp_nat_mul]
          congr 1
          ring
    _ = ((x : ℂ) ^ 2) * (Complex.exp ((2 * σ) * Complex.I) + ((a : ℂ) ^ 2 * (x : ℂ)⁻¹ ^ 2)) := by
          calc
            (x : ℂ) ^ 2 * Complex.exp ((2 * σ) * Complex.I) + (a : ℂ) ^ 2 =
                (x : ℂ) ^ 2 * Complex.exp ((2 * σ) * Complex.I) +
                  ((x : ℂ) ^ 2 * (x : ℂ)⁻¹ ^ 2) * (a : ℂ) ^ 2 := by
                    rw [hxInv, one_mul]
            _ = ((x : ℂ) ^ 2) * (Complex.exp ((2 * σ) * Complex.I) + ((a : ℂ) ^ 2 * (x : ℂ)⁻¹ ^ 2)) := by
                    ring
    _ = ((x : ℂ) ^ 2) * (Complex.exp ((2 * σ) * Complex.I) + (((a ^ 2 * x⁻¹ ^ 2 : ℝ)) : ℂ)) := by
          rw [← hcast]
    _ = ((x : ℂ) ^ 2) * (Complex.exp ((2 * σ) * Complex.I) + (((a / x) ^ 2 : ℝ) : ℂ)) := by
          rw [hdiv]

/-- Helper for Cartan section12 0034_Exercise_21: if `cos (2σ)` is nonnegative, then the rotated
quadratic denominator dominates `a²` on `(0, 1]` and `x²` on `[1, ∞)`. -/
lemma exercise21_rotatedQuadratic_norm_lower
    (a x σ : ℝ) (hσcos : 0 ≤ Real.cos (2 * σ)) :
    (if x ≤ 1 then a ^ 2 else x ^ 2) ≤
      ‖(((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
  by_cases hx : x ≤ 1
  · by_cases ha0 : a = 0
    · -- If `a = 0`, the lower branch asks only for the trivial nonnegativity bound.
      simp [hx, ha0, sq_nonneg x]
    · -- Factor out `a²` and use the unit-plus-rotation norm bound.
      have hfactor :
          (((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2) =
            (a : ℂ) ^ 2 * ((1 : ℂ) + ((x / a) ^ 2 : ℝ) * Complex.exp ((2 * σ) * Complex.I)) :=
        exercise21_rotatedQuadratic_factor_left a x σ ha0
      have hone :
          1 ≤ ‖(1 : ℂ) + (((x / a) ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * σ) * Complex.I)‖ := by
        simpa using
          exercise21_one_le_norm_one_add_mul_exp_of_cos_nonneg ((x / a) ^ 2) (2 * σ)
            (sq_nonneg (x / a)) hσcos
      calc
        (if x ≤ 1 then a ^ 2 else x ^ 2) = a ^ 2 := by simp [hx]
        _ = ‖(a : ℂ) ^ 2‖ := by simp [pow_two]
        _ ≤ ‖(((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
              rw [hfactor, norm_mul]
              have hmul :
                  a ^ 2 * 1 ≤ a ^ 2 *
                    ‖(1 : ℂ) + (((x / a) ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * σ) * Complex.I)‖ :=
                mul_le_mul_of_nonneg_left hone (sq_nonneg a)
              simpa [one_mul, pow_two] using hmul
  · have hx0 : x ≠ 0 := by linarith
    -- Factor out `x²` on the upper branch and use the translated-unit-circle norm bound.
    have hfactor :
        (((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2) =
          ((x : ℂ) ^ 2) * (Complex.exp ((2 * σ) * Complex.I) + (((a / x) ^ 2 : ℝ) : ℂ)) :=
      exercise21_rotatedQuadratic_factor_right a x σ hx0
    have hone :
        1 ≤ ‖Complex.exp ((2 * σ) * Complex.I) + (((a / x) ^ 2 : ℝ) : ℂ)‖ := by
      simpa [add_comm] using
        exercise21_one_le_norm_exp_add_of_cos_nonneg ((a / x) ^ 2) (2 * σ)
          (sq_nonneg (a / x)) hσcos
    calc
      (if x ≤ 1 then a ^ 2 else x ^ 2) = x ^ 2 := by simp [hx]
      _ = ‖(x : ℂ) ^ 2‖ := by simp [pow_two]
      _ ≤ ‖(((x : ℂ) * Complex.exp (σ * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
            rw [hfactor, norm_mul]
            have hmul :
                x ^ 2 * 1 ≤ x ^ 2 *
                  ‖Complex.exp ((2 * σ) * Complex.I) + (((a / x) ^ 2 : ℝ) : ℂ)‖ :=
              mul_le_mul_of_nonneg_left hone (sq_nonneg x)
            simpa [one_mul, pow_two] using hmul

/-- Helper for Cartan section12 0034_Exercise_21: the logarithmic denominator keeps at least the
size of its imaginary part. -/
lemma exercise21_logImag_norm_lower
    (x α : ℝ) :
    α ≤ ‖Real.log x + α * Complex.I‖ := by
  -- Expanding the squared norm shows the imaginary contribution `α²` sits inside it.
  have hsq : α ^ 2 ≤ ‖Real.log x + α * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith [sq_nonneg (Real.log x)]
  have hnn : 0 ≤ ‖Real.log x + α * Complex.I‖ := norm_nonneg _
  nlinarith

/-- Helper for Cartan section12 0034_Exercise_21: the conjugate logarithmic denominator obeys the
same lower bound by the imaginary part. -/
lemma exercise21_logImag_neg_norm_lower
    (x α : ℝ) :
    α ≤ ‖Real.log x - α * Complex.I‖ := by
  -- The negative imaginary shift contributes the same squared magnitude.
  have hsq : α ^ 2 ≤ ‖Real.log x - α * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith [sq_nonneg (Real.log x)]
  have hnn : 0 ≤ ‖Real.log x - α * Complex.I‖ := norm_nonneg _
  nlinarith

/-- Helper for Cartan section12 0034_Exercise_21: near the limiting angle `π`, the paired slit-lip
kernel is dominated by an integrable piecewise majorant independent of the truncation parameter. -/
lemma exercise21LipPairKernel_nearPi_norm_le
    (a α x : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hαlower : 3 * Real.pi / 4 ≤ α) (hαupper : α ≤ Real.pi) :
    ‖exercise21LipPairKernel a α x‖ ≤
      if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ) := by
  have hcos : 0 ≤ Real.cos (2 * α) :=
    exercise21_cos_two_nonneg_of_threeQuarterPi_le hαlower hαupper
  have hαpos : 0 < α := by
    -- The near-`π` window stays strictly away from the branch singularity at `0`.
    linarith [Real.pi_pos]
  have hαhalf : Real.pi / 2 ≤ α := by
    -- The lower bound `3π / 4 ≤ α` is more than enough for the later reciprocal estimate.
    linarith [hαlower]
  let m : ℝ := if x ≤ 1 then a ^ 2 else x ^ 2
  have hm_pos : 0 < m := by
    by_cases hx1 : x ≤ 1
    · -- On the lower branch the uniform denominator scale is `a²`.
      simp [m, hx1, ha.ne', sq_pos_of_ne_zero]
    · -- On the upper branch the denominator scale is `x²`.
      simp [m, hx1, hx.ne', sq_pos_of_ne_zero]
  have hm_nonneg : 0 ≤ m := hm_pos.le
  have hquadNeg :
      m ≤ ‖(((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
    -- Route correction: use the owner-side rotated-quadratic lower bound directly at angle `-α`
    -- instead of trying to normalize the denominator again inside the kernel estimate.
    simpa [m, neg_mul, mul_comm, mul_left_comm, mul_assoc, Real.cos_neg] using
      (exercise21_rotatedQuadratic_norm_lower a x (-α) (by simpa [neg_mul, mul_comm] using hcos))
  have hquadPos :
      m ≤ ‖(((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
    -- The positive-angle denominator is the same lower-bound regime with no extra transport.
    simpa [m] using (exercise21_rotatedQuadratic_norm_lower a x α hcos)
  have hlogNeg : α ≤ ‖Real.log x - α * Complex.I‖ :=
    exercise21_logImag_neg_norm_lower x α
  have hlogPos : α ≤ ‖Real.log x + α * Complex.I‖ :=
    exercise21_logImag_norm_lower x α
  have hdenNeg :
      m * α ≤ ‖((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
        (Real.log x - α * Complex.I))‖ := by
    -- Multiply the separate quadratic and logarithmic lower bounds.
    rw [norm_mul]
    nlinarith [hquadNeg, hlogNeg, hm_nonneg, hαpos.le]
  have hdenPos :
      m * α ≤ ‖((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
        (Real.log x + α * Complex.I))‖ := by
    -- The conjugate branch obeys the same product lower bound.
    rw [norm_mul]
    nlinarith [hquadPos, hlogPos, hm_nonneg, hαpos.le]
  have htermNeg :
      ‖Complex.exp (-α * Complex.I) /
          ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x - α * Complex.I))‖ ≤
        1 / (m * α) := by
    -- The numerator has unit norm, so the denominator lower bound controls the whole fraction.
    rw [norm_div]
    rw [show ‖Complex.exp (-α * Complex.I)‖ = 1 by
      simpa using Complex.norm_exp_ofReal_mul_I (-α)]
    simpa using one_div_le_one_div_of_le (mul_pos hm_pos hαpos) hdenNeg
  have htermPos :
      ‖Complex.exp (α * Complex.I) /
          ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x + α * Complex.I))‖ ≤
        1 / (m * α) := by
    -- The second slit-lip term is estimated in exactly the same way.
    rw [norm_div]
    rw [show ‖Complex.exp (α * Complex.I)‖ = 1 by
      simpa using Complex.norm_exp_ofReal_mul_I α]
    simpa using one_div_le_one_div_of_le (mul_pos hm_pos hαpos) hdenPos
  have hsum : ‖exercise21LipPairKernel a α x‖ ≤ 2 / (m * α) := by
    -- Sum the two one-sided bounds with the triangle inequality for the paired kernel.
    rw [exercise21LipPairKernel]
    calc
      ‖Complex.exp (-α * Complex.I) /
            ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x - α * Complex.I)) -
          Complex.exp (α * Complex.I) /
            ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x + α * Complex.I))‖
          ≤
            ‖Complex.exp (-α * Complex.I) /
                ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
                  (Real.log x - α * Complex.I))‖ +
              ‖Complex.exp (α * Complex.I) /
                ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
                  (Real.log x + α * Complex.I))‖ := norm_sub_le _ _
      _ ≤ 1 / (m * α) + 1 / (m * α) := add_le_add htermNeg htermPos
      _ = 2 / (m * α) := by ring
  have hαbound : 2 / (m * α) ≤ 4 / (Real.pi * m) := by
    -- Since `α ≥ π / 2`, the remaining scalar factor is uniformly bounded by `4 / π`.
    field_simp [hm_pos.ne', hαpos.ne', Real.pi_ne_zero]
    nlinarith [hm_pos.le, hαhalf, Real.pi_pos]
  by_cases hx1 : x ≤ 1
  · have hm_eq : m = a ^ 2 := by simp [m, hx1]
    calc
      ‖exercise21LipPairKernel a α x‖ ≤ 2 / (m * α) := hsum
      _ ≤ 4 / (Real.pi * m) := hαbound
      _ = 4 / (a ^ 2 * Real.pi) := by
            rw [hm_eq]
            ring_nf
      _ = if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ) := by
            simp [hx1]
  · have hm_eq : m = x ^ 2 := by simp [m, hx1]
    calc
      ‖exercise21LipPairKernel a α x‖ ≤ 2 / (m * α) := hsum
      _ ≤ 4 / (Real.pi * m) := hαbound
      _ = (4 / Real.pi) * x ^ (-2 : ℤ) := by
            rw [hm_eq]
            field_simp [Real.pi_ne_zero, hx.ne']
      _ = if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ) := by
            simp [hx1]

/-- Helper for Cartan section12 0034_Exercise_21: for each fixed positive radius, the paired
slit-lip kernel depends continuously on the branch angle at the limiting value `π`. -/
lemma exercise21LipPairKernel_continuousAt_pi
    (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    ContinuousAt (fun α : ℝ ↦ exercise21LipPairKernel a α x) Real.pi := by
  have hcosNeg : 0 ≤ Real.cos (2 * (-Real.pi)) := by
    simp
  have hquadNeg :
      0 < ‖(((x : ℂ) * Complex.exp (-Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
    have hbase := exercise21_rotatedQuadratic_norm_lower a x (-Real.pi) hcosNeg
    by_cases hx1 : x ≤ 1
    · -- The lower-branch denominator stays uniformly away from `0` by the `a²` lower bound.
      have hapos : 0 < a ^ 2 := sq_pos_of_pos ha
      have hbound :
          a ^ 2 ≤ ‖(((x : ℂ) * Complex.exp (-Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
        simpa [hx1] using hbase
      exact lt_of_lt_of_le hapos hbound
    · -- On the upper branch, the same lower-bound API gives a positive `x²` control.
      have hxsq : 0 < x ^ 2 := sq_pos_of_pos hx
      have hbound :
          x ^ 2 ≤ ‖(((x : ℂ) * Complex.exp (-Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
        simpa [hx1] using hbase
      exact lt_of_lt_of_le hxsq hbound
  have hquadNeg_ne :
      (((x : ℂ) * Complex.exp (-Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2) ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt hquadNeg)
  have hlogNeg :
      0 < ‖Real.log x - Real.pi * Complex.I‖ := by
    -- The logarithmic factor keeps a full `π` of imaginary size at the limiting angle.
    have hbound : Real.pi ≤ ‖Real.log x - Real.pi * Complex.I‖ :=
      exercise21_logImag_neg_norm_lower x Real.pi
    exact lt_of_lt_of_le Real.pi_pos hbound
  have hlogNeg_ne : (Real.log x - Real.pi * Complex.I) ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt hlogNeg)
  have hquadNeg_ne' :
      (((x : ℂ) * Complex.exp (-((Real.pi : ℂ) * Complex.I))) ^ 2 + (a : ℂ) ^ 2) ≠ 0 := by
    simpa using hquadNeg_ne
  have hdenNeg_ne :
      ((((x : ℂ) * Complex.exp (-((Real.pi : ℂ) * Complex.I))) ^ 2 + (a : ℂ) ^ 2) *
        (Real.log x - (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    simpa using mul_ne_zero hquadNeg_ne' hlogNeg_ne
  have hcosPos : 0 ≤ Real.cos (2 * Real.pi) := by
    simp
  have hquadPos :
      0 < ‖(((x : ℂ) * Complex.exp (Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
    have hbase := exercise21_rotatedQuadratic_norm_lower a x Real.pi hcosPos
    by_cases hx1 : x ≤ 1
    · -- The positive-angle quadratic denominator has the same uniform `a²` lower bound.
      have hapos : 0 < a ^ 2 := sq_pos_of_pos ha
      have hbound :
          a ^ 2 ≤ ‖(((x : ℂ) * Complex.exp (Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
        simpa [hx1] using hbase
      exact lt_of_lt_of_le hapos hbound
    · -- And on the complementary branch it is bounded below by the positive `x²`.
      have hxsq : 0 < x ^ 2 := sq_pos_of_pos hx
      have hbound :
          x ^ 2 ≤ ‖(((x : ℂ) * Complex.exp (Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2)‖ := by
        simpa [hx1] using hbase
      exact lt_of_lt_of_le hxsq hbound
  have hquadPos_ne :
      (((x : ℂ) * Complex.exp (Real.pi * Complex.I)) ^ 2 + (a : ℂ) ^ 2) ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt hquadPos)
  have hlogPos :
      0 < ‖Real.log x + Real.pi * Complex.I‖ := by
    -- The conjugate logarithmic factor has the same `π`-sized imaginary part.
    have hbound : Real.pi ≤ ‖Real.log x + Real.pi * Complex.I‖ :=
      exercise21_logImag_norm_lower x Real.pi
    exact lt_of_lt_of_le Real.pi_pos hbound
  have hlogPos_ne : (Real.log x + Real.pi * Complex.I) ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt hlogPos)
  have hdenPos_ne :
      ((((x : ℂ) * Complex.exp ((Real.pi : ℂ) * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
        (Real.log x + (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    exact mul_ne_zero hquadPos_ne hlogPos_ne
  have hExpNeg :
      ContinuousAt (fun α : ℝ ↦ Complex.exp (-((α : ℂ) * Complex.I))) Real.pi := by
    exact Complex.continuous_exp.continuousAt.comp
      ((Complex.continuous_ofReal.continuousAt.mul_const Complex.I).neg)
  have hExpPos :
      ContinuousAt (fun α : ℝ ↦ Complex.exp ((α : ℂ) * Complex.I)) Real.pi := by
    exact Complex.continuous_exp.continuousAt.comp
      (Complex.continuous_ofReal.continuousAt.mul_const Complex.I)
  have hDenNeg :
      ContinuousAt
        (fun α : ℝ ↦
          ((((x : ℂ) * Complex.exp (-((α : ℂ) * Complex.I))) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x - (α : ℂ) * Complex.I)))
        Real.pi := by
    -- The negative-branch denominator is a product of continuous quadratic and logarithmic terms.
    refine ContinuousAt.mul ?_ ?_
    · exact ((hExpNeg.const_mul (x : ℂ)).pow 2).add continuousAt_const
    · exact continuousAt_const.sub (Complex.continuous_ofReal.continuousAt.mul_const Complex.I)
  have hDenPos :
      ContinuousAt
        (fun α : ℝ ↦
          ((((x : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x + (α : ℂ) * Complex.I)))
        Real.pi := by
    -- The positive-branch denominator is handled by the same continuity decomposition.
    refine ContinuousAt.mul ?_ ?_
    · exact ((hExpPos.const_mul (x : ℂ)).pow 2).add continuousAt_const
    · exact continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul_const Complex.I)
  have hTermNeg :
      ContinuousAt
        (fun α : ℝ ↦
          Complex.exp (-((α : ℂ) * Complex.I)) /
            ((((x : ℂ) * Complex.exp (-((α : ℂ) * Complex.I))) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x - (α : ℂ) * Complex.I)))
        Real.pi := by
    -- Divide the continuous numerator by the already-separated nonvanishing denominator.
    exact hExpNeg.div hDenNeg hdenNeg_ne
  have hTermPos :
      ContinuousAt
        (fun α : ℝ ↦
          Complex.exp ((α : ℂ) * Complex.I) /
            ((((x : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x + (α : ℂ) * Complex.I)))
        Real.pi := by
    -- The conjugate branch is continuous by the same numerator/denominator split.
    exact hExpPos.div hDenPos hdenPos_ne
  -- Assemble the two continuous branches back into the paired slit-lip kernel.
  simpa [exercise21LipPairKernel] using hTermNeg.sub hTermPos

/-- Helper for Cartan section12 0034_Exercise_21: the near-`π` majorant also controls the
difference between the truncation kernel and its limiting `π`-kernel. -/
lemma exercise21LipPairKernel_nearPi_sub_pi_norm_le
    (a α x : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hαlower : 3 * Real.pi / 4 ≤ α) (hαupper : α ≤ Real.pi) :
    ‖exercise21LipPairKernel a α x - exercise21LipPairKernel a Real.pi x‖ ≤
      2 * (if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ)) := by
  have hαbound :
      ‖exercise21LipPairKernel a α x‖ ≤
        if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ) :=
    exercise21LipPairKernel_nearPi_norm_le a α x ha hx hαlower hαupper
  have hπbound :
      ‖exercise21LipPairKernel a Real.pi x‖ ≤
        if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ) :=
    exercise21LipPairKernel_nearPi_norm_le a Real.pi x ha hx
      (by nlinarith [Real.pi_pos]) le_rfl
  -- Route correction: keep the established near-`π` bound and only add the triangle inequality.
  calc
    ‖exercise21LipPairKernel a α x - exercise21LipPairKernel a Real.pi x‖
        ≤ ‖exercise21LipPairKernel a α x‖ + ‖exercise21LipPairKernel a Real.pi x‖ :=
      norm_sub_le _ _
    _ ≤
        (if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ)) +
          (if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ)) :=
      add_le_add hαbound hπbound
    _ = 2 * (if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ)) := by
      ring

/-- Helper for Cartan section12 0034_Exercise_21: the piecewise majorant used for the near-`π`
dominated-convergence argument is integrable on the positive half-line. -/
lemma exercise21LipPairKernel_nearPi_sub_pi_bound_integrableOnIoi
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ ↦
        2 * (if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ)))
      (Set.Ioi (0 : ℝ)) volume := by
  let g : ℝ → ℝ := fun x ↦
    2 * (if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ))
  have hconstPos : 0 < a ^ 2 * Real.pi := by
    nlinarith [sq_pos_of_pos ha, Real.pi_pos]
  have hlowConst :
      IntegrableOn (fun _ : ℝ ↦ 2 * (4 / (a ^ 2 * Real.pi) : ℝ)) (Set.Ioc (0 : ℝ) 1) volume := by
    exact MeasureTheory.integrableOn_const
      (s := Set.Ioc (0 : ℝ) 1)
      (C := 2 * (4 / (a ^ 2 * Real.pi) : ℝ))
      (hs := by simp)
  have hlow : IntegrableOn g (Set.Ioc (0 : ℝ) 1) volume := by
    -- On `(0, 1]`, the majorant is the constant branch of the piecewise definition.
    refine MeasureTheory.IntegrableOn.congr_fun hlowConst ?_ measurableSet_Ioc
    intro x hx
    simp [g, hx.2]
  have hpow :
      IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) volume := by
    simpa using
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := (1 : ℝ)) (by norm_num) zero_lt_one)
  have hpowZ :
      IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℤ)) (Set.Ioi (1 : ℝ)) volume := by
    simpa using hpow
  have hhighScaled :
      IntegrableOn (fun x : ℝ ↦ (2 * (4 / Real.pi : ℝ)) * x ^ (-2 : ℤ)) (Set.Ioi (1 : ℝ)) volume := by
    simpa [mul_assoc] using hpowZ.const_mul (2 * (4 / Real.pi : ℝ))
  have hhigh : IntegrableOn g (Set.Ioi (1 : ℝ)) volume := by
    -- On `[1, ∞)`, only the `x⁻²` branch remains, which is already integrable.
    refine MeasureTheory.IntegrableOn.congr_fun hhighScaled ?_ measurableSet_Ioi
    intro x hx
    have hxgt1 : 1 < x := hx
    simp [g, not_le_of_gt hxgt1, mul_left_comm, mul_comm]
  -- Split the positive half-line at `1` and combine the low and high integrable pieces.
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hlow.union hhigh

/-- Helper for Cartan section12 0034_Exercise_21: after rewriting the two slit lips against the
common truncation interval, the remaining angle defect `arctan ((1 / R) / R)` contributes a
vanishing error. -/
lemma exercise21LipPair_intervalIntegral_sub_pi_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ ↦
        ∫ x in (1 / R)..R,
          (exercise21LipPairKernel a (Real.pi - Real.arctan ((1 / R) / R)) x -
            exercise21LipPairKernel a Real.pi x))
      Filter.atTop
      (nhds 0) := by
  let α : ℝ → ℝ := fun R ↦ Real.pi - Real.arctan ((1 / R) / R)
  let φ : ℝ → Set ℝ := fun R ↦ Set.Ioi (1 / R) ∩ Set.Iic R
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let G : ℝ → ℝ → ℂ := fun R x ↦
    exercise21LipPairKernel a (α R) x - exercise21LipPairKernel a Real.pi x
  let F : ℝ → ℝ → ℂ := fun R x ↦ Set.indicator (φ R) (G R) x
  let bound : ℝ → ℝ := fun x ↦
    2 * (if x ≤ 1 then 4 / (a ^ 2 * Real.pi) else (4 / Real.pi) * x ^ (-2 : ℤ))
  have hInv :
      Filter.Tendsto (fun R : ℝ ↦ R⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero
  have hArg :
      Filter.Tendsto (fun R : ℝ ↦ ((1 / R) / R : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hInv.mul hInv
  have hAlpha :
      Filter.Tendsto α Filter.atTop (nhds Real.pi) := by
    have hArctan :
        Filter.Tendsto (fun R : ℝ ↦ Real.arctan ((1 / R) / R)) Filter.atTop (nhds (0 : ℝ)) := by
      simpa [Function.comp, Real.arctan_zero] using
        Real.continuousAt_arctan.tendsto.comp hArg
    simpa [α] using Filter.Tendsto.const_sub Real.pi hArctan
  have hmeasKernel :
      ∀ β : ℝ, Measurable (fun x : ℝ ↦ exercise21LipPairKernel a β x) := by
    intro β
    -- Expand the kernel once so `fun_prop` can certify measurability of the algebraic formula.
    have hmeas :
        Measurable
          (fun x : ℝ ↦
            Complex.exp (-β * Complex.I) /
                ((((x : ℂ) * Complex.exp (-β * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
                  (Real.log x - β * Complex.I)) -
              Complex.exp (β * Complex.I) /
                ((((x : ℂ) * Complex.exp (β * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
                  (Real.log x + β * Complex.I))) := by
      fun_prop
    simpa [exercise21LipPairKernel, sub_eq_add_neg] using hmeas
  have hBoundIntegrable : Integrable bound μ := by
    simpa [μ, bound] using exercise21LipPairKernel_nearPi_sub_pi_bound_integrableOnIoi a ha
  have hFMeas : ∀ᶠ R : ℝ in Filter.atTop, AEStronglyMeasurable (F R) μ := by
    refine Filter.Eventually.of_forall ?_
    intro R
    have hGMeas : AEStronglyMeasurable (G R) μ := by
      exact (hmeasKernel (α R)).aestronglyMeasurable.sub
        ((hmeasKernel Real.pi).aestronglyMeasurable)
    exact hGMeas.indicator (measurableSet_Ioi.inter measurableSet_Iic)
  have hBound :
      ∀ᶠ R : ℝ in Filter.atTop, ∀ᵐ x : ℝ ∂μ, ‖F R x‖ ≤ bound x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with R hR
    have hRpos : 0 < R := lt_trans zero_lt_one hR
    have hratioNonneg : 0 ≤ ((1 / R) / R : ℝ) := by
      positivity
    have hratioLeOne : ((1 / R) / R : ℝ) ≤ 1 := by
      field_simp [hRpos.ne']
      nlinarith
    have hArctanLeQuarter :
        Real.arctan ((1 / R) / R) ≤ Real.pi / 4 := by
      have hmono := Real.arctan_mono hratioLeOne
      simpa [Real.arctan_one] using hmono
    have hAlphaLower : 3 * Real.pi / 4 ≤ α R := by
      dsimp [α]
      nlinarith [hArctanLeQuarter]
    have hAlphaUpper : α R ≤ Real.pi := by
      have hArctanNonneg : 0 ≤ Real.arctan ((1 / R) / R) := by
        exact (Real.arctan_nonneg).2 hratioNonneg
      dsimp [α]
      nlinarith
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hBoundNonneg : 0 ≤ bound x := by
      dsimp [bound]
      by_cases hx1 : x ≤ 1
      · positivity
      · have hxpow : 0 ≤ x ^ (-2 : ℤ) := by
          exact zpow_nonneg (le_of_lt hx) (-2)
        positivity
    by_cases hxφ : x ∈ φ R
    · -- Inside the truncation window, the kernel difference is bounded by the near-`π` majorant.
      have hestimate :=
        exercise21LipPairKernel_nearPi_sub_pi_norm_le a (α R) x ha hx hAlphaLower hAlphaUpper
      simpa [F, G, bound, hxφ] using hestimate
    · -- Outside the truncation window, the indicator turns the family into `0`.
      simp [F, hxφ, hBoundNonneg]
  have hEventuallyMem :
      ∀ {x : ℝ}, 0 < x → ∀ᶠ R : ℝ in Filter.atTop, x ∈ φ R := by
    intro x hx
    filter_upwards [Filter.eventually_gt_atTop (max x (1 / x))] with R hR
    have hxLeR : x ≤ R := le_of_lt (lt_of_le_of_lt (le_max_left x (1 / x)) hR)
    have hRpos : 0 < R := lt_trans (lt_of_lt_of_le hx (le_max_left x (1 / x))) hR
    have hxInvLtR : 1 / x < R := lt_of_le_of_lt (le_max_right x (1 / x)) hR
    have hLower : 1 / R < x := (one_div_lt hRpos hx).2 hxInvLtR
    exact ⟨hLower, hxLeR⟩
  have hLim :
      ∀ᵐ x : ℝ ∂μ, Filter.Tendsto (fun R : ℝ ↦ F R x) Filter.atTop (nhds (0 : ℂ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hMem : ∀ᶠ R : ℝ in Filter.atTop, x ∈ φ R := hEventuallyMem hx
    have hKernel :
        Filter.Tendsto (fun R : ℝ ↦ exercise21LipPairKernel a (α R) x)
          Filter.atTop (nhds (exercise21LipPairKernel a Real.pi x)) := by
      exact (exercise21LipPairKernel_continuousAt_pi a x ha hx).tendsto.comp hAlpha
    have hDiff :
        Filter.Tendsto (fun R : ℝ ↦ G R x) Filter.atTop (nhds (0 : ℂ)) := by
      simpa [G] using hKernel.sub_const (exercise21LipPairKernel a Real.pi x)
    -- Once `x` stays in every truncation window, the indicator family agrees with the raw kernel
    -- difference and inherits its limit `0`.
    refine Filter.Tendsto.congr' ?_ hDiff
    filter_upwards [hMem] with R hRmem
    simp [F, G, hRmem]
  have hRestricted :
      Filter.Tendsto (fun R : ℝ ↦ ∫ x, F R x ∂μ) Filter.atTop (nhds (0 : ℂ)) := by
    -- Route correction: use a single restricted-measure DCT instead of reopening the old
    -- split-at-`1` and reciprocal-tail normalization.
    simpa using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        bound hFMeas hBound hBoundIntegrable hLim)
  have hEvent :
      ∀ᶠ R : ℝ in Filter.atTop,
        (∫ x, F R x ∂μ) =
          ∫ x in (1 / R)..R,
            (exercise21LipPairKernel a (α R) x - exercise21LipPairKernel a Real.pi x) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with R hR
    have hRpos : 0 < R := lt_trans zero_lt_one hR
    have hsubset : Set.Ioc (1 / R) R ⊆ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact lt_trans (one_div_pos.mpr hRpos) hx.1
    have hInter :
        Set.Ioc (1 / R) R ∩ Set.Ioi (0 : ℝ) = Set.Ioc (1 / R) R := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, hsubset hx⟩
    have hle : 1 / R ≤ R := by
      field_simp [hRpos.ne']
      nlinarith
    have hMeasPhi : MeasurableSet (φ R) := measurableSet_Ioi.inter measurableSet_Iic
    have hμ : μ = volume.restrict (Set.Ioi (0 : ℝ)) := rfl
    rw [MeasureTheory.integral_indicator hMeasPhi]
    rw [hμ]
    rw [show φ R = Set.Ioc (1 / R) R by rfl]
    rw [Measure.restrict_restrict measurableSet_Ioc, hInter]
    simpa [G, α] using
      (intervalIntegral.integral_of_le hle (f := G R) (μ := volume)).symm
  exact Filter.Tendsto.congr' hEvent hRestricted

/-- Helper for Cartan section12 0034_Exercise_21: the symmetric truncations `(1 / R)..R` of the
real target kernel converge to the improper integral on `(0, ∞)`. -/
lemma exercise21TargetKernel_truncatedIntegral_tendsto
    (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ ↦
        ∫ x in (1 / R)..R, exercise21TargetKernel a x)
      Filter.atTop
      (nhds
        (∫ x in Set.Ioi (0 : ℝ),
          exercise21TargetKernel a x ∂MeasureTheory.volume)) := by
  let f : ℝ → ℝ := exercise21TargetKernel a
  have hfi : IntegrableOn f (Set.Ioi (0 : ℝ)) volume :=
    exercise21TargetKernel_integrableOnIoi a ha
  have hLower :
      Filter.Tendsto (fun R : ℝ ↦ 1 / R) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero
  let φ : ℝ → Set ℝ := fun R ↦ Set.Ioi (1 / R) ∩ Set.Iic R
  have hcover :
      MeasureTheory.AECover (volume.restrict <| Set.Ioi (0 : ℝ)) Filter.atTop φ :=
    (MeasureTheory.aecover_Ioi_of_Ioi
      (μ := volume) (l := Filter.atTop) (A := (0 : ℝ))
      (a := fun R : ℝ ↦ 1 / R) hLower).inter
      (MeasureTheory.aecover_Iic
        (μ := volume.restrict <| Set.Ioi (0 : ℝ))
        (l := Filter.atTop) (b := fun R : ℝ ↦ R) Filter.tendsto_id)
  have hlimit :
      Filter.Tendsto
        (fun R : ℝ ↦ ∫ x in φ R, f x ∂(volume.restrict <| Set.Ioi (0 : ℝ)))
        Filter.atTop
        (nhds (∫ x in Set.Ioi (0 : ℝ), f x ∂volume)) := by
    simpa [f] using
      (hcover.integral_tendsto_of_countably_generated
        (show Integrable f (volume.restrict <| Set.Ioi (0 : ℝ)) from hfi))
  have hevent :
      ∀ᶠ R : ℝ in Filter.atTop,
        (∫ x in φ R, f x ∂(volume.restrict <| Set.Ioi (0 : ℝ))) =
          ∫ x in (1 / R)..R, f x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with R hR
    have hRpos : 0 < R := lt_trans zero_lt_one hR
    have hsubset : Set.Ioc (1 / R) R ⊆ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact lt_trans (one_div_pos.mpr hRpos) hx.1
    have hle : 1 / R ≤ R := by
      field_simp [hRpos.ne']
      nlinarith
    have hinter :
        Set.Ioc (1 / R) R ∩ Set.Ioi (0 : ℝ) = Set.Ioc (1 / R) R := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, hsubset hx⟩
    rw [show φ R = Set.Ioc (1 / R) R by rfl]
    rw [Measure.restrict_restrict measurableSet_Ioc, hinter]
    simpa [f] using (intervalIntegral.integral_of_le hle (f := f) (μ := volume)).symm
  -- The truncated intervals cover `(0, ∞)` inside the restricted positive-half-line measure.
  exact Filter.Tendsto.congr' hevent hlimit

/-- Helper for Cartan section12 0034_Exercise_21: once `ε = 1 / R`, the inner and outer circle
branches contribute a vanishing remainder as `R → ∞`. -/
lemma exercise21Delta_circleBranchIntegrals_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ ↦
        let θ := Real.arctan ((1 / R) / R)
        let inner :
            Path (circleMap 0 (1 / R) (Real.pi - θ))
              (circleMap 0 (1 / R) (-Real.pi + θ)) :=
          (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R))
        let outer :
            Path (circleMap 0 R (-Real.pi + θ))
              (circleMap 0 R (Real.pi - θ)) :=
          (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R)
        (∫ᶜ z in inner, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in outer, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)))
      Filter.atTop
      (nhds 0) := by
  let f : ℂ → ℂ := fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹
  let G : ℝ → ℂ := fun R ↦
    let θ := Real.arctan ((1 / R) / R)
    let inner :
        Path (circleMap 0 (1 / R) (Real.pi - θ))
          (circleMap 0 (1 / R) (-Real.pi + θ)) :=
      (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R))
    let outer :
        Path (circleMap 0 R (-Real.pi + θ))
          (circleMap 0 R (Real.pi - θ)) :=
      (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R)
    (∫ᶜ z in inner, ((f dz) z)) + (∫ᶜ z in outer, ((f dz) z))
  let C : ℝ := 4 * Real.pi / a ^ 2 + 4 * Real.pi
  have hbound :
      ∀ᶠ R : ℝ in Filter.atTop, ‖G R‖ ≤ C / R := by
    let B : ℝ := Real.exp 1 + 2 + 2 / a + 2 * a
    filter_upwards [Filter.eventually_gt_atTop B] with R hR
    have hRpos : 0 < R := by
      have hBpos : 0 < B := by
        dsimp [B]
        positivity
      exact lt_trans hBpos hR
    have hRgt2 : 2 < R := by
      have hBge : 2 ≤ B := by
        dsimp [B]
        have hnonneg : 0 ≤ Real.exp 1 + 2 / a + 2 * a := by
          positivity
        linarith
      exact lt_of_le_of_lt hBge hR
    have hRgtExp : Real.exp 1 < R := by
      have hBge : Real.exp 1 ≤ B := by
        dsimp [B]
        have hnonneg : 0 ≤ 2 + 2 / a + 2 * a := by
          positivity
        linarith
      exact lt_of_le_of_lt hBge hR
    have hRgtTwoDiv : 2 / a < R := by
      have hBge : 2 / a ≤ B := by
        dsimp [B]
        have hnonneg : 0 ≤ Real.exp 1 + 2 + 2 * a := by
          positivity
        linarith
      exact lt_of_le_of_lt hBge hR
    have hRgtTwoMul : 2 * a < R := by
      have hBge : 2 * a ≤ B := by
        dsimp [B]
        have hnonneg : 0 ≤ Real.exp 1 + 2 + 2 / a := by
          positivity
        linarith
      exact lt_of_le_of_lt hBge hR
    let θ : ℝ := Real.arctan ((1 / R) / R)
    have hεr : 1 / R < R := by
      field_simp [hRpos.ne']
      nlinarith
    have hθ_bounds :=
      exercise21_keyhole_angle_bounds (r := R) (ε := 1 / R) (one_div_pos.mpr hRpos) hεr
    have hθ_nonneg : 0 ≤ θ := hθ_bounds.1.le
    have hθ_lt_pi : θ < Real.pi := by
      linarith [hθ_bounds.2, Real.pi_pos]
    have hangle :
        |(-Real.pi + θ) - (Real.pi - θ)| ≤ 2 * Real.pi := by
      have hnonneg : 0 ≤ 2 * Real.pi - 2 * θ := by
        linarith [hθ_nonneg]
      have habs : |(-Real.pi + θ) - (Real.pi - θ)| = 2 * Real.pi - 2 * θ := by
        rw [show (-Real.pi + θ) - (Real.pi - θ) = -(2 * Real.pi - 2 * θ) by ring]
        rw [abs_neg, abs_of_nonneg hnonneg]
      rw [habs]
      linarith [hθ_nonneg]
    have hangle' :
        |(Real.pi - θ) - (-Real.pi + θ)| ≤ 2 * Real.pi := by
      have hnonneg : 0 ≤ 2 * Real.pi - 2 * θ := by
        linarith [hθ_nonneg]
      have habs : |(Real.pi - θ) - (-Real.pi + θ)| = 2 * Real.pi - 2 * θ := by
        rw [show (Real.pi - θ) - (-Real.pi + θ) = 2 * Real.pi - 2 * θ by ring]
        rw [abs_of_nonneg hnonneg]
      rw [habs]
      linarith [hθ_nonneg]
    have hinnerEq :
        ∫ᶜ z in
          (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R)),
          ((f dz) z) =
          sectorArcIntegral f (1 / R) (Real.pi - θ) (-Real.pi + θ) := by
      -- Rewrite the inner circular branch through the chapter-local sector-arc owner.
      simpa using
        exercise21CircleArc_curveIntegral_eq_sectorArcIntegral
          f (1 / R) (Real.pi - θ) (-Real.pi + θ)
    have houterEq :
        ∫ᶜ z in
          (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R),
          ((f dz) z) =
          sectorArcIntegral f R (-Real.pi + θ) (Real.pi - θ) := by
      -- The same owner rewrite applies to the outer circular branch.
      simpa using
        exercise21CircleArc_curveIntegral_eq_sectorArcIntegral
          f R (-Real.pi + θ) (Real.pi - θ)
    have hinnerNorm :
        ‖sectorArcIntegral f (1 / R) (Real.pi - θ) (-Real.pi + θ)‖ ≤
          (4 * Real.pi / a ^ 2) / R := by
      rw [sectorArcIntegral_def]
      have hbasic :
          ‖∫ φ in (Real.pi - θ)..(-Real.pi + θ),
              Complex.I * circleMap 0 (1 / R) φ * f (circleMap 0 (1 / R) φ)‖ ≤
            (2 / (a ^ 2 * R)) * |(-Real.pi + θ) - (Real.pi - θ)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro φ hφ
        have hφLower : -Real.pi + θ < φ := by
          rcases Set.mem_uIoc.mp hφ with h | h
          · exfalso
            linarith [h.1, h.2, hθ_nonneg]
          · exact h.1
        have hφUpper : φ ≤ Real.pi - θ := by
          rcases Set.mem_uIoc.mp hφ with h | h
          · exfalso
            linarith [h.1, h.2, hθ_nonneg]
          · exact h.2
        have hφStrip : φ ∈ Set.Ioo (-Real.pi) Real.pi := by
          constructor
          · linarith [hφLower, hθ_nonneg]
          · linarith [hφUpper, hθ_nonneg]
        have hlog :
            Complex.log (circleMap 0 (1 / R) φ) =
              Real.log (1 / R) + φ * Complex.I :=
          exercise21_log_circleMap_of_pos (x := 1 / R) (α := φ)
            (one_div_pos.mpr hRpos) hφStrip
        have hlogNorm :
            1 ≤ ‖Complex.log (circleMap 0 (1 / R) φ)‖ := by
          have hRge1 : 1 ≤ R := by
            linarith [hRgt2]
          have hre :
              |Real.log (1 / R)| ≤ ‖Real.log (1 / R) + φ * Complex.I‖ := by
            simpa using Complex.abs_re_le_norm (Real.log (1 / R) + φ * Complex.I)
          have hlogAbs :
              |Real.log (1 / R)| = Real.log R := by
            rw [show (1 / R : ℝ) = R⁻¹ by simp, Real.log_inv]
            simpa [abs_of_nonneg (Real.log_nonneg hRge1)]
          have hlogRge :
              1 ≤ Real.log R := by
            exact (Real.le_log_iff_exp_le hRpos).2 (by simpa using le_of_lt hRgtExp)
          have hlogRnonneg : 0 ≤ Real.log R := le_trans zero_le_one hlogRge
          have hlogOfReal :
              (Real.log (1 / R) : ℂ) = (-Real.log R : ℂ) := by
            rw [show (1 / R : ℝ) = R⁻¹ by simp, Real.log_inv]
            simp
          have hlogRewrite :
              Complex.log (circleMap 0 (1 / R) φ) = (-Real.log R : ℂ) + φ * Complex.I := by
            rw [hlog, hlogOfReal]
          have hbound' :
              Real.log R ≤ ‖Complex.log (circleMap 0 (1 / R) φ)‖ := by
            have htmp :
                Real.log R ≤ ‖(-Real.log R : ℂ) + φ * Complex.I‖ := by
              simpa [abs_of_nonneg hlogRnonneg, show (1 / R : ℝ) = R⁻¹ by simp,
                Real.log_inv, hlogOfReal] using hre
            rw [hlogRewrite]
            exact htmp
          exact le_trans hlogRge hbound'
        let z : ℂ := circleMap 0 (1 / R) φ
        have hzNorm : ‖z‖ = 1 / R := by
          dsimp [z]
          rw [norm_circleMap_zero, abs_of_pos (one_div_pos.mpr hRpos)]
        have hsmall : (1 / R) ^ 2 ≤ a ^ 2 / 2 := by
          field_simp [hRpos.ne', ha.ne'] at hRgtTwoDiv ⊢
          nlinarith
        have hquad :
            a ^ 2 / 2 ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ := by
          have htri :
              ‖(a : ℂ) ^ 2‖ ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ + ‖z ^ 2‖ := by
            have := norm_add_le (z ^ 2 + (a : ℂ) ^ 2) (-z ^ 2)
            simpa [z, add_assoc, add_left_comm, add_comm] using this
          have hzSq : ‖z ^ 2‖ = (1 / R) ^ 2 := by
            calc
              ‖z ^ 2‖ = ‖z‖ ^ 2 := by rw [norm_pow]
              _ = (1 / R) ^ 2 := by rw [hzNorm]
          have haSq : ‖(a : ℂ) ^ 2‖ = a ^ 2 := by
            simp
          nlinarith [htri, hsmall]
        have hquadPos : 0 < ‖z ^ 2 + (a : ℂ) ^ 2‖ := by
          have : 0 < a ^ 2 / 2 := by positivity
          exact lt_of_lt_of_le this hquad
        have hmulLower :
            a ^ 2 / 2 ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖ := by
          have : a ^ 2 / 2 * 1 ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖ := by
            nlinarith [hquad, hlogNorm, norm_nonneg (Complex.log z)]
          simpa using this
        have hmulInv :
            (‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖)⁻¹ ≤ (a ^ 2 / 2)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le (by positivity) hmulLower
        have hRinvPos : 0 ≤ 1 / R := by positivity
        -- Control the inner-arc integrand by the geometric `1 / R` factor and the lower
        -- bounds on the quadratic and logarithmic denominators.
        calc
          ‖Complex.I * circleMap 0 (1 / R) φ * f (circleMap 0 (1 / R) φ)‖ =
              (1 / R) * (‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖)⁻¹ := by
                dsimp [f, z]
                rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_inv, norm_mul, hzNorm]
          _ ≤ (1 / R) * (a ^ 2 / 2)⁻¹ := by
                exact mul_le_mul_of_nonneg_left hmulInv hRinvPos
          _ = 2 / (a ^ 2 * R) := by
                field_simp [ha.ne', hRpos.ne']
      calc
        ‖∫ φ in (Real.pi - θ)..(-Real.pi + θ),
            Complex.I * circleMap 0 (1 / R) φ * f (circleMap 0 (1 / R) φ)‖ ≤
          (2 / (a ^ 2 * R)) * |(-Real.pi + θ) - (Real.pi - θ)| := hbasic
        _ ≤ (2 / (a ^ 2 * R)) * (2 * Real.pi) := by
          gcongr
        _ = (4 * Real.pi / a ^ 2) / R := by
          field_simp [ha.ne', hRpos.ne']
          ring
    have houterNorm :
        ‖sectorArcIntegral f R (-Real.pi + θ) (Real.pi - θ)‖ ≤
          (4 * Real.pi) / R := by
      rw [sectorArcIntegral_def]
      have hbasic :
          ‖∫ φ in (-Real.pi + θ)..(Real.pi - θ),
              Complex.I * circleMap 0 R φ * f (circleMap 0 R φ)‖ ≤
            (2 / R) * |(Real.pi - θ) - (-Real.pi + θ)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro φ hφ
        have hφLower : -Real.pi + θ < φ := by
          rcases Set.mem_uIoc.mp hφ with h | h
          · exact h.1
          · exfalso
            linarith [h.1, h.2, hθ_nonneg]
        have hφUpper : φ ≤ Real.pi - θ := by
          rcases Set.mem_uIoc.mp hφ with h | h
          · exact h.2
          · exfalso
            linarith [h.1, h.2, hθ_nonneg]
        have hφStrip : φ ∈ Set.Ioo (-Real.pi) Real.pi := by
          constructor
          · linarith [hφLower, hθ_nonneg]
          · linarith [hφUpper, hθ_nonneg]
        have hlog :
            Complex.log (circleMap 0 R φ) = Real.log R + φ * Complex.I :=
          exercise21_log_circleMap_of_pos (x := R) (α := φ) hRpos hφStrip
        have hlogNorm :
            1 ≤ ‖Complex.log (circleMap 0 R φ)‖ := by
          have hre :
              |Real.log R| ≤ ‖Real.log R + φ * Complex.I‖ := by
            simpa using Complex.abs_re_le_norm (Real.log R + φ * Complex.I)
          have hlogRge :
              1 ≤ Real.log R := by
            exact (Real.le_log_iff_exp_le hRpos).2 (by simpa using le_of_lt hRgtExp)
          have hlogRnonneg : 0 ≤ Real.log R := le_trans zero_le_one hlogRge
          have hbound' :
              Real.log R ≤ ‖Complex.log (circleMap 0 R φ)‖ := by
            have htmp : Real.log R ≤ ‖Real.log R + φ * Complex.I‖ := by
              simpa [abs_of_nonneg hlogRnonneg] using hre
            simpa [hlog] using htmp
          exact le_trans hlogRge hbound'
        let z : ℂ := circleMap 0 R φ
        have hzNorm : ‖z‖ = R := by
          dsimp [z]
          rw [norm_circleMap_zero, abs_of_pos hRpos]
        have hlarge : a ^ 2 ≤ R ^ 2 / 2 := by
          field_simp [ha.ne'] at hRgtTwoMul ⊢
          nlinarith
        have hquad :
            R ^ 2 / 2 ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ := by
          have htri :
              ‖z ^ 2‖ ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ + ‖(a : ℂ) ^ 2‖ := by
            have := norm_add_le (z ^ 2 + (a : ℂ) ^ 2) (-(a : ℂ) ^ 2)
            simpa [z, add_assoc, add_left_comm, add_comm] using this
          have hzSq : ‖z ^ 2‖ = R ^ 2 := by
            calc
              ‖z ^ 2‖ = ‖z‖ ^ 2 := by rw [norm_pow]
              _ = R ^ 2 := by rw [hzNorm]
          have haSq : ‖(a : ℂ) ^ 2‖ = a ^ 2 := by
            simp
          nlinarith [htri, hlarge]
        have hmulLower :
            R ^ 2 / 2 ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖ := by
          have : R ^ 2 / 2 * 1 ≤ ‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖ := by
            nlinarith [hquad, hlogNorm, norm_nonneg (Complex.log z)]
          simpa using this
        have hmulInv :
            (‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖)⁻¹ ≤ (R ^ 2 / 2)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le (by positivity) hmulLower
        have hRnonneg : 0 ≤ R := hRpos.le
        -- On the outer arc, the numerator contributes `R` while the quadratic denominator gives
        -- an `R²` gain, so the whole integrand is uniformly `O(R⁻¹)`.
        calc
          ‖Complex.I * circleMap 0 R φ * f (circleMap 0 R φ)‖ =
              R * (‖z ^ 2 + (a : ℂ) ^ 2‖ * ‖Complex.log z‖)⁻¹ := by
                dsimp [f, z]
                rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_inv, norm_mul, hzNorm]
          _ ≤ R * (R ^ 2 / 2)⁻¹ := by
                exact mul_le_mul_of_nonneg_left hmulInv hRnonneg
          _ = 2 / R := by
                field_simp [hRpos.ne']
      calc
        ‖∫ φ in (-Real.pi + θ)..(Real.pi - θ),
            Complex.I * circleMap 0 R φ * f (circleMap 0 R φ)‖ ≤
          (2 / R) * |(Real.pi - θ) - (-Real.pi + θ)| := hbasic
        _ ≤ (2 / R) * (2 * Real.pi) := by
          gcongr
        _ = (4 * Real.pi) / R := by
          field_simp [hRpos.ne']
          ring
    -- Combine the inner and outer `O(R⁻¹)` bounds into one eventual majorant.
    calc
      ‖G R‖ ≤
        ‖sectorArcIntegral f (1 / R) (Real.pi - θ) (-Real.pi + θ)‖ +
          ‖sectorArcIntegral f R (-Real.pi + θ) (Real.pi - θ)‖ := by
            simp [G, θ, hinnerEq, houterEq, norm_add_le]
      _ ≤ (4 * Real.pi / a ^ 2) / R + (4 * Real.pi) / R := by
            gcongr
      _ = C / R := by
            dsimp [C]
            ring
  have hdecay : Filter.Tendsto (fun R : ℝ ↦ C / R) Filter.atTop (nhds 0) := by
    -- The explicit `O(R⁻¹)` scalar majorant tends to zero.
    simpa [C, div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Filter.Tendsto (fun R : ℝ ↦ C * R⁻¹) Filter.atTop (nhds (C * 0)))
  simpa [G, f, mul_assoc, mul_left_comm, mul_comm] using squeeze_zero_norm' hbound hdecay
