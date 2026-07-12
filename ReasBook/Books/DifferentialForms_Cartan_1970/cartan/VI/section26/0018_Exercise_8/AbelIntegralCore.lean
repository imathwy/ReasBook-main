import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».ClosedExtensionCore

open Set
open scoped UpperHalfPlane

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: the source integrand is continuous on the strict
upper half-plane because the chosen square-root branch is continuous and nonvanishing there. -/
lemma exercise8_integrand_continuousOn_upper (k : Exercise8Modulus) :
    ContinuousOn (exercise8_integrand k) {z : ℂ | 0 < z.im} := by
  -- The integrand is the reciprocal of the source branch, so continuity reduces to the branch
  -- continuity plus its nonvanishing on `Im z > 0`.
  simpa [exercise8_integrand] using
    (exercise8_simple_sqrt_branch_continuousOn_upper k).inv₀
      (fun z hz ↦ exercise8_simple_sqrt_branch_ne_zero_on_upper hz)

/-- Helper for Cartan section26 0018_Exercise_8: the source integrand is holomorphic on the strict
upper half-plane because it is the reciprocal of the holomorphic simple square-root branch. -/
lemma exercise8_integrand_differentiableOn_upper (k : Exercise8Modulus) :
    DifferentiableOn ℂ (exercise8_integrand k) {z : ℂ | 0 < z.im} := by
  -- Once the branch is holomorphic and nowhere zero on `Im z > 0`, its reciprocal is holomorphic
  -- on the same domain.
  simpa [exercise8_integrand] using
    (exercise8_simple_sqrt_branch_differentiableOn_upper k).inv
      (fun z hz ↦ exercise8_simple_sqrt_branch_ne_zero_on_upper hz)

/-- Helper for Cartan section26 0018_Exercise_8: the strict upper half-plane is convex, so
segment-additivity and local primitive arguments may be run there without leaving the source
domain. -/
lemma exercise8_convex_upperHalfPlaneSet :
    Convex ℝ UpperHalfPlane.upperHalfPlaneSet := by
  -- This is the standard open half-space `{z : ℂ | 0 < Im z}`.
  simpa [UpperHalfPlane.upperHalfPlaneSet] using (convex_halfSpace_im_gt (0 : ℝ))

/-- Helper for Cartan section26 0018_Exercise_8: the radicand is a polynomial expression in `z`,
so it is continuous on the whole complex plane. -/
lemma exercise8_radicand_continuous (k : Exercise8Modulus) :
    Continuous (exercise8_radicand k) := by
  -- Continuity is purely algebraic: both factors are polynomial in `z`.
  have hpow : Continuous (fun z : ℂ ↦ z ^ (2 : ℕ)) := by
    simpa using (continuous_id.pow 2)
  simpa [exercise8_radicand] using
    (continuous_const.sub hpow).mul
      (continuous_const.sub
        (((continuous_const : Continuous fun _ : ℂ ↦ (k : ℂ) ^ (2 : ℕ)).mul hpow)))

/-- Helper for Cartan section26 0018_Exercise_8: although the source branch API only records
holomorphy on `Im z > 0`, the integrand is still uniformly bounded on a sufficiently small
upper-half-plane neighborhood of `0` because its square equals the radicand, which stays close to
`1` there. -/
lemma exercise8_integrand_bounded_near_zero (k : Exercise8Modulus) :
    ∃ r > 0, ∀ z : ℂ, ‖z‖ < r → 0 < z.im → ‖exercise8_integrand k z‖ ≤ 2 := by
  -- Route correction: this bound is the input needed for the dyadic splitting of the
  -- `0`-anchored Abel integral, so we avoid asking again for a global primitive at the boundary.
  have hcont : ContinuousAt (exercise8_radicand k) 0 :=
    (exercise8_radicand_continuous k).continuousAt
  have hnhds :
      {z : ℂ | ‖exercise8_radicand k z - 1‖ < (3 / 4 : ℝ)} ∈ nhds (0 : ℂ) := by
    -- Continuity of the radicand at `0` keeps it inside the disk of radius `3/4` around `1`.
    have hball :
        Metric.ball (exercise8_radicand k 0) (3 / 4 : ℝ) ∈
          nhds (exercise8_radicand k 0) := Metric.ball_mem_nhds _ (by norm_num)
    simpa [Metric.ball, dist_eq_norm, exercise8_radicand] using hcont.preimage_mem_nhds hball
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r, hr_pos, ?_⟩
  intro z hz hzIm
  have hzball : z ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.ball, dist_eq_norm] using hz
  have hclose : ‖exercise8_radicand k z - 1‖ < (3 / 4 : ℝ) := hr_sub hzball
  have hrev : ‖1 - exercise8_radicand k z‖ = ‖exercise8_radicand k z - 1‖ := by
    simpa [sub_eq_add_neg, add_comm] using
      (norm_sub_rev (1 : ℂ) (exercise8_radicand k z))
  have htri' : ‖(1 : ℂ)‖ ≤ ‖exercise8_radicand k z‖ + ‖1 - exercise8_radicand k z‖ := by
    -- Triangle inequality for `1 = radicand + (1 - radicand)`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (exercise8_radicand k z) (1 - exercise8_radicand k z))
  have htri : ‖(1 : ℂ)‖ ≤ ‖exercise8_radicand k z‖ + ‖exercise8_radicand k z - 1‖ := by
    simpa [hrev] using htri'
  have hnorm_rad : (1 / 4 : ℝ) ≤ ‖exercise8_radicand k z‖ := by
    have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    linarith
  have hsq : ‖exercise8_simple_sqrt_branch k z‖ ^ (2 : ℕ) = ‖exercise8_radicand k z‖ := by
    -- The branch squares to the radicand on `Im z > 0`, so its norm is bounded away from zero.
    calc
      ‖exercise8_simple_sqrt_branch k z‖ ^ (2 : ℕ) =
          ‖exercise8_simple_sqrt_branch k z ^ (2 : ℕ)‖ := by
            simp [sq]
      _ = ‖exercise8_radicand k z‖ := by
            rw [exercise8_simple_sqrt_branch_sq_eq_on_upper hzIm]
  have hbranch_half : (1 / 2 : ℝ) ≤ ‖exercise8_simple_sqrt_branch k z‖ := by
    have hnonneg : 0 ≤ ‖exercise8_simple_sqrt_branch k z‖ := norm_nonneg _
    nlinarith [hsq, hnorm_rad]
  have hnonzero :
      exercise8_simple_sqrt_branch k z ≠ 0 :=
    exercise8_simple_sqrt_branch_ne_zero_on_upper hzIm
  have hnorm_inv : ‖exercise8_integrand k z‖ = ‖exercise8_simple_sqrt_branch k z‖⁻¹ := by
    -- The integrand is the reciprocal of the branch.
    simp [exercise8_integrand]
  rw [hnorm_inv]
  have hpos : 0 < ‖exercise8_simple_sqrt_branch k z‖ := norm_pos_iff.mpr hnonzero
  have hhalfpos : 0 < (1 / 2 : ℝ) := by norm_num
  have hinv : ‖exercise8_simple_sqrt_branch k z‖⁻¹ ≤ 2 := by
    have := (inv_le_inv₀ hpos hhalfpos).2 hbranch_half
    simpa using this
  exact hinv

/-- Helper for Cartan section26 0018_Exercise_8: multiplying an upper-half-plane point by a
positive real scalar keeps it in the strict upper half-plane. -/
lemma exercise8_im_pos_mul_of_upper {z : UpperHalfPlane} {r : ℝ} (hr : 0 < r) :
    0 < (((r : ℂ) * (z : ℂ)).im) := by
  -- The imaginary part scales by the positive real factor `r`.
  simpa [Complex.mul_im, mul_comm] using mul_pos hr z.im_pos

/-- Helper for Cartan section26 0018_Exercise_8: along a fixed upper-half-plane ray, the source
integrand is continuous for every positive real parameter. -/
lemma exercise8_ray_integrand_continuousOn_Ioi
    (k : Exercise8Modulus) (z : UpperHalfPlane) :
    ContinuousOn
      (fun s : ℝ ↦ exercise8_integrand k ((s : ℂ) * (z : ℂ)))
      (Set.Ioi 0) := by
  have hmul : Continuous fun s : ℝ ↦ ((s : ℂ) * (z : ℂ)) := by
    exact Complex.continuous_ofReal.mul continuous_const
  -- Every positive parameter stays inside the strict upper half-plane on the same ray.
  refine (exercise8_integrand_continuousOn_upper k).comp hmul.continuousOn ?_
  intro s hs
  exact exercise8_im_pos_mul_of_upper (z := z) hs

/-- Helper for Cartan section26 0018_Exercise_8: the source ray kernel is interval integrable on
every compact interval `[0, b]` with `b > 0`. The proof combines the near-zero bound with
continuity away from the boundary base point. -/
lemma exercise8_ray_integrand_intervalIntegrable
    (k : Exercise8Modulus) (z : UpperHalfPlane) {b : ℝ} (hb : 0 < b) :
    IntervalIntegrable
      (fun s : ℝ ↦ exercise8_integrand k ((s : ℂ) * (z : ℂ)))
      MeasureTheory.volume 0 b := by
  let g : ℝ → ℂ := fun s ↦ exercise8_integrand k ((s : ℂ) * (z : ℂ))
  rcases exercise8_integrand_bounded_near_zero k with ⟨R, hR_pos, hR_bound⟩
  have hz_norm_pos : 0 < ‖(z : ℂ)‖ := by
    exact norm_pos_iff.mpr z.ne_zero
  let δ : ℝ := min b (R / (2 * ‖(z : ℂ)‖))
  have hδ_pos : 0 < δ := by
    refine lt_min hb ?_
    exact div_pos hR_pos (by positivity)
  have hδ_le_b : δ ≤ b := min_le_left _ _
  have hsmall :
      ∀ s ∈ Ioc (0 : ℝ) δ, ‖g s‖ ≤ 2 := by
    intro s hs
    have hs_pos : 0 < s := hs.1
    have hs_le : s ≤ δ := hs.2
    have hs_norm : ‖((s : ℂ) * (z : ℂ))‖ < R := by
      calc
        ‖((s : ℂ) * (z : ℂ))‖ = |s| * ‖(z : ℂ)‖ := by
          simpa using norm_mul (s : ℂ) (z : ℂ)
        _ = s * ‖(z : ℂ)‖ := by
          rw [abs_of_pos hs_pos]
        _ ≤ δ * ‖(z : ℂ)‖ := by
          gcongr
        _ ≤ (R / (2 * ‖(z : ℂ)‖)) * ‖(z : ℂ)‖ := by
          gcongr
          exact min_le_right _ _
        _ = R / 2 := by
          field_simp [hz_norm_pos.ne']
        _ < R := by
          linarith
    have hs_im : 0 < (((s : ℂ) * (z : ℂ)).im) := by
      exact exercise8_im_pos_mul_of_upper (z := z) hs_pos
    -- Near the boundary base point, the previously proved uniform estimate applies directly.
    exact hR_bound (((s : ℂ) * (z : ℂ))) hs_norm hs_im
  have hsmall_meas :
      MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.volume.restrict (Ioc (0 : ℝ) δ)) := by
    exact
      (exercise8_ray_integrand_continuousOn_Ioi k z).mono
        (fun _ hx ↦ hx.1) |>.aestronglyMeasurable measurableSet_Ioc
  have hsmall_int : MeasureTheory.IntegrableOn g (Ioc (0 : ℝ) δ) MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.of_bound (by simp) hsmall_meas 2 ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall hsmall
  have hrest_int : IntervalIntegrable g MeasureTheory.volume δ b := by
    refine ContinuousOn.intervalIntegrable
      ((exercise8_ray_integrand_continuousOn_Ioi k z).mono ?_)
    intro x hx
    have hx' : x ∈ Icc δ b := by
      simpa [Set.uIcc_of_le hδ_le_b] using hx
    exact lt_of_lt_of_le hδ_pos hx'.1
  have hsmall_int' : IntervalIntegrable g MeasureTheory.volume 0 δ := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ_pos.le).2 hsmall_int
  -- Split the source interval into a bounded near-zero piece and a continuous away-from-zero
  -- piece.
  exact hsmall_int'.trans hrest_int

/-- Helper for Cartan section26 0018_Exercise_8: along a fixed upper-half-plane ray and away from
the boundary basepoint, the integrand is continuous as a real parameter function. -/
lemma exercise8_ray_integrand_continuousOn_Icc
    (k : Exercise8Modulus) (z : UpperHalfPlane) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun s : ℝ ↦ exercise8_integrand k ((s : ℂ) * (z : ℂ)))
      (Icc a b) := by
  have hmul : Continuous fun s : ℝ ↦ ((s : ℂ) * (z : ℂ)) := by
    exact Complex.continuous_ofReal.mul continuous_const
  -- Every point on the closed interval stays on the same strict upper-half-plane ray.
  refine (exercise8_ray_integrand_continuousOn_Ioi k z).mono ?_
  intro s hs
  exact lt_of_lt_of_le ha hs.1

/-- Helper for Cartan section26 0018_Exercise_8: the initial segment from `0` to `r z` is the ray
integral with velocity `(r z)`. This is the reparametrization used in the missing `0`-anchored
split. -/
lemma exercise8_initial_ray_segment_eq_intervalIntegral
    (k : Exercise8Modulus) (z : UpperHalfPlane) (r : ℝ) :
    ∫ᶜ w in Path.segment (0 : ℂ) ((r : ℂ) * (z : ℂ)), (exercise8_integrand k dz) w =
      (((r : ℂ) * (z : ℂ)) : ℂ) *
        ∫ s in (0 : ℝ)..1, exercise8_integrand k (((s : ℂ) * ((r : ℂ) * (z : ℂ)))) := by
  -- This is just `curveIntegral_segment` written in the source ray coordinates.
  rw [curveIntegral_segment]
  simp [AffineMap.lineMap_apply, mul_comm]

/-- Helper for Cartan section26 0018_Exercise_8: the tail segment from `r z` to `z` is the
interval integral of the same ray parametrized by the affine map `s ↦ (1 - s) r z + s z`. -/
lemma exercise8_tail_ray_segment_eq_intervalIntegral
    (k : Exercise8Modulus) (z : UpperHalfPlane) (r : ℝ) :
    ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w =
      (((z : ℂ) - (r : ℂ) * (z : ℂ)) : ℂ) *
        ∫ s in (0 : ℝ)..1,
          exercise8_integrand k ((AffineMap.lineMap ((r : ℂ) * (z : ℂ)) (z : ℂ)) s) := by
  -- This is the same segment formula, now for the affine tail from `r z` to `z`.
  rw [curveIntegral_segment]
  simp [AffineMap.lineMap_apply, mul_comm]

/-- Helper for Cartan section26 0018_Exercise_8: the initial segment from `0` to `r z` can be
rewritten directly as the normalized ray integral on `[0, r]`. -/
lemma exercise8_initial_ray_segment_eq_rayIntervalIntegral
    (k : Exercise8Modulus) (z : UpperHalfPlane) {r : ℝ} (hr0 : 0 < r) :
    ∫ᶜ w in Path.segment (0 : ℂ) ((r : ℂ) * (z : ℂ)), (exercise8_integrand k dz) w =
      (z : ℂ) * ∫ s in (0 : ℝ)..r, exercise8_integrand k ((s : ℂ) * (z : ℂ)) := by
  -- Route correction: package the `s ↦ s * r` change of variables once so later proofs only see
  -- the single ray kernel `s ↦ exercise8_integrand k ((s : ℂ) * z)`.
  rw [exercise8_initial_ray_segment_eq_intervalIntegral]
  rw [show
      (fun s : ℝ ↦ exercise8_integrand k ((s : ℂ) * ((r : ℂ) * (z : ℂ)))) =
        fun s : ℝ ↦ exercise8_integrand k ((((s * r : ℝ) : ℂ) * (z : ℂ))) by
      funext s
      simp [mul_left_comm, mul_comm]]
  rw [intervalIntegral.integral_comp_mul_right
    (a := (0 : ℝ)) (b := 1) (c := r)
    (fun s : ℝ ↦ exercise8_integrand k ((s : ℂ) * (z : ℂ))) hr0.ne']
  rw [show
      ((r⁻¹ : ℝ) • ∫ x in 0 * r..1 * r, exercise8_integrand k ((x : ℂ) * (z : ℂ)) : ℂ) =
        ((((r⁻¹ : ℝ) : ℂ) *
          ∫ x in 0 * r..1 * r, exercise8_integrand k ((x : ℂ) * (z : ℂ))) : ℂ) by
      rfl]
  have hmul : (((r : ℂ) * (((r⁻¹ : ℝ) : ℂ))) : ℂ) = 1 := by
    exact_mod_cast mul_inv_cancel₀ hr0.ne'
  -- The exposed statement now has no inverse factors left.
  calc
    ((r : ℂ) * (z : ℂ)) *
        ((((r⁻¹ : ℝ) : ℂ) *
          ∫ x in 0 * r..1 * r, exercise8_integrand k ((x : ℂ) * (z : ℂ))) : ℂ) =
      ((((r : ℂ) * (((r⁻¹ : ℝ) : ℂ))) * (z : ℂ)) *
          ∫ x in 0 * r..1 * r, exercise8_integrand k ((x : ℂ) * (z : ℂ))) := by
        ring
    _ = (z : ℂ) * ∫ x in 0 * r..1 * r, exercise8_integrand k ((x : ℂ) * (z : ℂ)) := by
        rw [hmul, one_mul]
    _ = (z : ℂ) * ∫ x in (0 : ℝ)..r, exercise8_integrand k ((x : ℂ) * (z : ℂ)) := by
        simp

/-- Helper for Cartan section26 0018_Exercise_8: the tail segment from `r z` to `z` can be
rewritten directly as the normalized ray integral on `[r, 1]`. -/
lemma exercise8_tail_ray_segment_eq_rayIntervalIntegral
    (k : Exercise8Modulus) (z : UpperHalfPlane) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w =
      (z : ℂ) * ∫ s in r..(1 : ℝ), exercise8_integrand k ((s : ℂ) * (z : ℂ)) := by
  by_cases hrEq : r = 1
  · -- At the endpoint `r = 1`, the tail segment is degenerate and the interval integral vanishes.
    subst hrEq
    rw [exercise8_tail_ray_segment_eq_intervalIntegral]
    simp
  · -- Otherwise the affine change of variables uses the nonzero scale `1 - r`.
    rw [exercise8_tail_ray_segment_eq_intervalIntegral]
    rw [show
        (fun s : ℝ ↦
          exercise8_integrand k ((AffineMap.lineMap ((r : ℂ) * (z : ℂ)) (z : ℂ)) s)) =
          fun s : ℝ ↦ exercise8_integrand k ((((r + (1 - r) * s : ℝ) : ℂ) * (z : ℂ))) by
        funext s
        simp [AffineMap.lineMap_apply]
        ring]
    have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrEq)
    rw [intervalIntegral.integral_comp_add_mul
      (a := (0 : ℝ)) (b := 1) (c := 1 - r) (d := r)
      (fun s : ℝ ↦ exercise8_integrand k ((s : ℂ) * (z : ℂ))) h1r]
    have hzfac : ((z : ℂ) - (r : ℂ) * (z : ℂ)) = (((1 - r : ℝ) : ℂ) * (z : ℂ)) := by
      calc
        (z : ℂ) - (r : ℂ) * (z : ℂ) = (z : ℂ) * (1 - (r : ℂ)) := by ring
        _ = (((1 - r : ℝ) : ℂ) * (z : ℂ)) := by
            have hcast : (1 - (r : ℂ)) = (((1 - r : ℝ) : ℂ)) := by simp
            rw [hcast, mul_comm]
    rw [hzfac]
    let I : ℂ :=
      ∫ x in r + (1 - r) * 0..r + (1 - r) * 1,
        exercise8_integrand k ((x : ℂ) * (z : ℂ))
    have hsmul : ((1 - r)⁻¹ • I : ℂ) = ((((1 - r)⁻¹ : ℝ) : ℂ) * I) := rfl
    rw [show
        ((1 - r)⁻¹ •
            ∫ x in r + (1 - r) * 0..r + (1 - r) * 1,
              exercise8_integrand k ((x : ℂ) * (z : ℂ)) : ℂ) =
          ((((1 - r)⁻¹ : ℝ) : ℂ) * I) by
        simpa [I] using hsmul]
    have hmul : ((((1 - r : ℝ) : ℂ) * (((1 - r)⁻¹ : ℝ) : ℂ)) : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ h1r
    -- The Jacobian factor is now cancelled once and for all inside this adapter.
    calc
      (((1 - r : ℝ) : ℂ) * (z : ℂ)) *
          ((((1 - r)⁻¹ : ℝ) : ℂ) * I) =
        ((((1 - r : ℝ) : ℂ) * (((1 - r)⁻¹ : ℝ) : ℂ)) * (z : ℂ)) * I := by
          ring
      _ = (z : ℂ) * I := by
          rw [hmul, one_mul]
      _ = (z : ℂ) * ∫ x in r..(1 : ℝ), exercise8_integrand k ((x : ℂ) * (z : ℂ)) := by
          simp [I]

/-- Helper for Cartan section26 0018_Exercise_8: on the convex strict upper half-plane, Exercise 8
segment integrals are additive along broken segments because the integrand defines a closed
holomorphic `1`-form there. This early copy breaks the local forward-reference cycle in the
scaled-residual package. -/
lemma exercise8_segment_integral_add_aux
    (k : Exercise8Modulus) (a b c : UpperHalfPlane) :
    (∫ᶜ w in Path.segment (a : ℂ) (b : ℂ), (exercise8_integrand k dz) w) +
        ∫ᶜ w in Path.segment (b : ℂ) (c : ℂ), (exercise8_integrand k dz) w =
      ∫ᶜ w in Path.segment (a : ℂ) (c : ℂ), (exercise8_integrand k dz) w := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (exercise8_integrand k dz) z
  have hωEq : (fun z : ℂ ↦ exercise8_integrand k z • (1 : ℂ →L[ℂ] ℂ)) = ω := by
    funext z
    ext
    simp [ω, mul_comm]
  let dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ := fun x ↦
    ContinuousLinearMap.smulRight
      (ContinuousLinearMap.restrictScalars (R := ℝ)
        (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
      (1 : ℂ →L[ℂ] ℂ)
  have hω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        HasFDerivWithinAt ω (dω x) UpperHalfPlane.upperHalfPlaneSet x := by
    intro x hx
    -- The closed-form theorem needs the derivative of the `dz`-valued integrand on `Im z > 0`.
    have hscalar :
        DifferentiableWithinAt ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x :=
      exercise8_integrand_differentiableOn_upper k x
        (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hx)
    have hscalarDeriv :
        HasFDerivWithinAt (exercise8_integrand k)
          (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x)
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalar.hasFDerivWithinAt
    have hscalarDerivR :
        HasFDerivWithinAt (exercise8_integrand k)
          (ContinuousLinearMap.restrictScalars (R := ℝ)
            (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalarDeriv.restrictScalars ℝ
    simpa [hωEq, dω] using hscalarDerivR.smul_const (1 : ℂ →L[ℂ] ℂ)
  have hdω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        ∀ u ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
          ∀ v ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
            dω x u v = dω x v u := by
    intro x hx u _ v _
    -- In one complex dimension, the bilinear derivative is symmetric by commutativity.
    let L := fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x
    have hu : L u = u * L 1 := by
      calc
        L u = L (u * (1 : ℂ)) := by simp
        _ = u * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    have hv : L v = v * L 1 := by
      calc
        L v = L (v * (1 : ℂ)) := by simp
        _ = v * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    simp [dω, L, hu, hv, mul_left_comm, mul_comm]
  -- Route correction: this is the reusable closed-form API that replaces the failed local
  -- primitive-through-`0` route.
  simpa [ω, dω] using
    Convex.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
      (s := UpperHalfPlane.upperHalfPlaneSet) (ω := ω) (dω := dω)
      exercise8_convex_upperHalfPlaneSet hω hdω a.2 b.2 c.2

/-- Helper for Cartan section26 0018_Exercise_8: the Abel integral splits exactly at any interior
point of the same upper-half-plane ray. -/
lemma exercise8_abel_integral_eq_scaled_add_tail
    (k : Exercise8Modulus) (z : UpperHalfPlane) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    exercise8_abel_integral k z =
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ))) +
        ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w := by
  let f : ℝ → ℂ := fun s ↦ exercise8_integrand k ((s : ℂ) * (z : ℂ))
  have hscaled_im : 0 < (((r : ℂ) * (z : ℂ)).im) :=
    exercise8_im_pos_mul_of_upper (z := z) hr0
  have hscaled_coe :
      (((UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ)) : UpperHalfPlane) : ℂ)) =
        ((r : ℂ) * (z : ℂ)) := by
    simpa using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos hscaled_im)
  have hfull :
      exercise8_abel_integral k z = (z : ℂ) * ∫ s in (0 : ℝ)..1, f s := by
    -- Normalize the full Abel integral to the ray parameter on `[0, 1]`.
    rw [exercise8_abel_integral_def]
    calc
      ∫ᶜ w in Path.segment (0 : ℂ) (z : ℂ), (exercise8_integrand k dz) w =
          ∫ᶜ w in Path.segment (0 : ℂ) (((1 : ℂ) * (z : ℂ))), (exercise8_integrand k dz) w := by
            rw [one_mul]
      _ = (z : ℂ) * ∫ s in (0 : ℝ)..1, f s := by
            simpa [f] using
              (exercise8_initial_ray_segment_eq_rayIntervalIntegral k z (r := 1) zero_lt_one)
  have hprefix :
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ))) =
        (z : ℂ) * ∫ s in (0 : ℝ)..r, f s := by
    -- The scaled prefix is the same ray integral, now truncated at `r`.
    rw [exercise8_abel_integral_def, hscaled_coe]
    simpa [f] using
      (exercise8_initial_ray_segment_eq_rayIntervalIntegral k z (r := r) hr0)
  have htail :
      ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w =
        (z : ℂ) * ∫ s in r..(1 : ℝ), f s := by
    -- The remaining connector is the normalized tail ray integral on `[r, 1]`.
    simpa [f] using
      (exercise8_tail_ray_segment_eq_rayIntervalIntegral k z (r := r) hr0 hr1)
  have hInt0r : IntervalIntegrable f MeasureTheory.volume 0 r := by
    -- The near-zero ray integrability lemma covers the truncated prefix.
    simpa [f] using
      (exercise8_ray_integrand_intervalIntegrable k z (b := r) hr0)
  have hIntr1 : IntervalIntegrable f MeasureTheory.volume r 1 := by
    -- Away from `0`, continuity on the closed interval `[r, 1]` gives the tail integrability.
    refine ContinuousOn.intervalIntegrable ?_
    simpa [Set.uIcc_of_le hr1, f] using
      (exercise8_ray_integrand_continuousOn_Icc k z (a := r) (b := 1) hr0)
  let A : ℂ := ∫ s in (0 : ℝ)..r, f s
  let B : ℂ := ∫ s in r..(1 : ℝ), f s
  calc
    exercise8_abel_integral k z = (z : ℂ) * ∫ s in (0 : ℝ)..1, f s := hfull
    _ = (z : ℂ) * (A + B) := by
          simp [A, B, ← intervalIntegral.integral_add_adjacent_intervals hInt0r hIntr1]
    _ = ((z : ℂ) * A) + ((z : ℂ) * B) := by
          ring
    _ =
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ))) +
          ((z : ℂ) * B) := by
          simp [A, B, hprefix]
    _ =
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ))) +
          ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w := by
          simp [B, htail]
/-- Helper for Cartan section26 0018_Exercise_8: subtracting the Abel values at a point and at
its vertical lift isolates the same scaled residual on the smaller strip. -/
lemma exercise8_abel_integral_sub_verticalLift_sub_horizontal_eq_scaledResidual
    (k : Exercise8Modulus) (w : UpperHalfPlane) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    let y : ℝ := (w : ℂ).im
    exercise8_abel_integral k w -
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((y : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment ((y : ℂ) * Complex.I) (w : ℂ), (exercise8_integrand k dz) z =
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * (w : ℂ))) -
        exercise8_abel_integral k (UpperHalfPlane.ofComplex (((r * y : ℝ) : ℂ) * Complex.I)) -
        ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
          (exercise8_integrand k dz) z := by
  set y : ℝ := (w : ℂ).im with hy
  let vertical : UpperHalfPlane := ⟨((y : ℂ) * Complex.I), by
    simpa [y, hy] using w.im_pos⟩
  let scaledVertical : UpperHalfPlane := ⟨(((r * y : ℝ) : ℂ) * Complex.I), by
    simpa [y, hy] using mul_pos hr0 w.im_pos⟩
  let scaled : UpperHalfPlane := ⟨((r : ℂ) * (w : ℂ)), exercise8_im_pos_mul_of_upper (z := w) hr0⟩
  have hvertical_eq : UpperHalfPlane.ofComplex ((y : ℂ) * Complex.I) = vertical := by
    simpa [vertical] using (UpperHalfPlane.ofComplex_apply vertical)
  have hscaledVertical_eq :
      UpperHalfPlane.ofComplex (((r * y : ℝ) : ℂ) * Complex.I) = scaledVertical := by
    simpa [scaledVertical] using (UpperHalfPlane.ofComplex_apply scaledVertical)
  have hscaled_eq : UpperHalfPlane.ofComplex ((r : ℂ) * (w : ℂ)) = scaled := by
    simpa [scaled] using (UpperHalfPlane.ofComplex_apply scaled)
  have hvertical_im : 0 < (((y : ℂ) * Complex.I).im) := by
    simpa [y, hy] using w.im_pos
  have hscaledVertical_im : 0 < ((((r * y : ℝ) : ℂ) * Complex.I).im) := by
    simpa [y, hy] using mul_pos hr0 w.im_pos
  have hscaled_im : 0 < (((r : ℂ) * (w : ℂ)).im) :=
    exercise8_im_pos_mul_of_upper (z := w) hr0
  have hvertical_coe : ((vertical : UpperHalfPlane) : ℂ) = (y : ℂ) * Complex.I := rfl
  have hscaledVertical_coe :
      ((scaledVertical : UpperHalfPlane) : ℂ) = (((r * y : ℝ) : ℂ) * Complex.I) := rfl
  have hscaled_coe : ((scaled : UpperHalfPlane) : ℂ) = ((r : ℂ) * (w : ℂ)) := rfl
  have hsplit_w :
      exercise8_abel_integral k w =
        exercise8_abel_integral k scaled +
          ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z := by
    -- Split the Abel integral at the scaled point on the same upper-half-plane ray.
    simpa [hscaled_eq] using
      (exercise8_abel_integral_eq_scaled_add_tail k w (r := r) hr0 hr1)
  have hsplit_vertical :
      exercise8_abel_integral k vertical =
        exercise8_abel_integral k scaledVertical +
          ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
            (exercise8_integrand k dz) z := by
    -- Apply the same split to the vertical lift `y I`.
    have hscale_vertical :
        (r : ℂ) * ((y : ℂ) * Complex.I) = (((r * y : ℝ) : ℂ) * Complex.I) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    calc
      exercise8_abel_integral k vertical =
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * ((y : ℂ) * Complex.I))) +
            ∫ᶜ z in Path.segment ((r : ℂ) * ((y : ℂ) * Complex.I)) ((y : ℂ) * Complex.I),
              (exercise8_integrand k dz) z := by
              simpa [vertical, y, hy] using
                (exercise8_abel_integral_eq_scaled_add_tail k vertical (r := r) hr0 hr1)
      _ =
          exercise8_abel_integral k scaledVertical +
            ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
              (exercise8_integrand k dz) z := by
              rw [hscale_vertical, hscaledVertical_eq]
  have hvertical_path :
      (∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
          (exercise8_integrand k dz) z) +
        ∫ᶜ z in Path.segment ((y : ℂ) * Complex.I) (w : ℂ), (exercise8_integrand k dz) z =
      ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) (w : ℂ),
        (exercise8_integrand k dz) z := by
    -- Additivity along the broken path `((r y) I) -> y I -> w`.
    simpa [vertical, scaledVertical, hvertical_coe, hscaledVertical_coe] using
      (exercise8_segment_integral_add_aux k scaledVertical vertical w)
  have hscaled_path :
      (∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
          (exercise8_integrand k dz) z) +
        ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z =
      ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) (w : ℂ),
        (exercise8_integrand k dz) z := by
    -- The same total path also factors through the scaled point `r w`.
    simpa [scaled, scaledVertical, hscaled_coe, hscaledVertical_coe] using
      (exercise8_segment_integral_add_aux k scaledVertical scaled w)
  have hconnector :
      ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z -
          ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
            (exercise8_integrand k dz) z -
          ∫ᶜ z in Path.segment ((y : ℂ) * Complex.I) (w : ℂ), (exercise8_integrand k dz) z =
        -∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
          (exercise8_integrand k dz) z := by
    -- Compare the two broken-segment decompositions of the same connector.
    have hsame :
        (∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
            (exercise8_integrand k dz) z) +
          ∫ᶜ z in Path.segment ((y : ℂ) * Complex.I) (w : ℂ), (exercise8_integrand k dz) z =
        (∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
            (exercise8_integrand k dz) z) +
          ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z := by
      rw [hvertical_path, hscaled_path]
    calc
      ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z -
            ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
              (exercise8_integrand k dz) z -
            ∫ᶜ z in Path.segment ((y : ℂ) * Complex.I) (w : ℂ), (exercise8_integrand k dz) z =
          ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z -
            ((∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
                (exercise8_integrand k dz) z) +
              ∫ᶜ z in Path.segment ((y : ℂ) * Complex.I) (w : ℂ), (exercise8_integrand k dz) z) := by
            ring
      _ =
          ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z -
            ((∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
                (exercise8_integrand k dz) z) +
              ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z) := by
            rw [hsame]
      _ =
          -∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
            (exercise8_integrand k dz) z := by
            ring
  -- Assemble the two same-ray splits and rewrite the connector difference to the scaled residual.
  have hmain :
      exercise8_abel_integral k w -
            exercise8_abel_integral k vertical -
            ∫ᶜ z in Path.segment ((vertical : ℂ)) (w : ℂ), (exercise8_integrand k dz) z =
          exercise8_abel_integral k scaled -
            exercise8_abel_integral k scaledVertical -
            ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
              (exercise8_integrand k dz) z := by
    calc
    exercise8_abel_integral k w -
          exercise8_abel_integral k vertical -
          ∫ᶜ z in Path.segment ((vertical : ℂ)) (w : ℂ), (exercise8_integrand k dz) z =
        (exercise8_abel_integral k scaled +
            ∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z) -
          (exercise8_abel_integral k scaledVertical +
            ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
              (exercise8_integrand k dz) z) -
          ∫ᶜ z in Path.segment ((vertical : ℂ)) (w : ℂ), (exercise8_integrand k dz) z := by
            rw [hsplit_w, hsplit_vertical]
    _ =
        exercise8_abel_integral k scaled -
          exercise8_abel_integral k scaledVertical +
          (∫ᶜ z in Path.segment ((r : ℂ) * (w : ℂ)) (w : ℂ), (exercise8_integrand k dz) z -
            ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((y : ℂ) * Complex.I),
              (exercise8_integrand k dz) z -
            ∫ᶜ z in Path.segment ((vertical : ℂ)) (w : ℂ), (exercise8_integrand k dz) z) := by
            ring
    _ =
        exercise8_abel_integral k scaled -
          exercise8_abel_integral k scaledVertical +
          (-∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
              (exercise8_integrand k dz) z) := by
            rw [hconnector]
    _ =
        exercise8_abel_integral k scaled -
          exercise8_abel_integral k scaledVertical -
          ∫ᶜ z in Path.segment (((r * y : ℝ) : ℂ) * Complex.I) ((r : ℂ) * (w : ℂ)),
            (exercise8_integrand k dz) z := by
            ring
  -- Rewrite the explicit upper-half-plane points back to the canonical `ofComplex` owners.
  have hmain' := hmain
  rw [← hvertical_eq, ← hscaledVertical_eq, ← hscaled_eq] at hmain'
  have hvertical_ofComplex_coe :
      (((UpperHalfPlane.ofComplex ((y : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)) =
        ((y : ℂ) * Complex.I) := by
    simpa [hvertical_coe] using
      congrArg (fun z : UpperHalfPlane ↦ (z : ℂ)) hvertical_eq
  rw [hvertical_ofComplex_coe] at hmain'
  simpa [vertical, scaledVertical, scaled, y, hy] using hmain'

/-- Helper for Cartan section26 0018_Exercise_8: a horizontal segment at height `y` rewrites to
an interval integral over the affine real parameter `a + t (b - a)`. -/
lemma exercise8_horizontal_segment_eq_intervalIntegral
    (k : Exercise8Modulus) (a b y : ℝ) :
    ∫ᶜ z in Path.segment ((a : ℂ) + (y : ℂ) * Complex.I)
        ((b : ℂ) + (y : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      (∫ t in (0 : ℝ)..1,
          exercise8_integrand k ((((a + t * (b - a)) : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
        ((b - a : ℝ) : ℂ) := by
  -- Rewrite the horizontal source segment through its affine parametrization and pull out the
  -- constant velocity `(b - a)`.
  rw [curveIntegral_segment]
  have hline :
      ∀ t : ℝ,
        (AffineMap.lineMap ((a : ℂ) + (y : ℂ) * Complex.I)
            ((b : ℂ) + (y : ℂ) * Complex.I)) t =
          ((((a + t * (b - a)) : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    intro t
    simp [AffineMap.lineMap_apply]
    ring
  have hdir :
      ((b : ℂ) + (y : ℂ) * Complex.I) - ((a : ℂ) + (y : ℂ) * Complex.I) =
        ((b - a : ℝ) : ℂ) := by
    ring_nf
    simp
  have hpoint :
      ∀ t : ℝ,
        ((exercise8_integrand k dz)
            ((AffineMap.lineMap ((a : ℂ) + (y : ℂ) * Complex.I)
              ((b : ℂ) + (y : ℂ) * Complex.I)) t))
            (((b : ℂ) + (y : ℂ) * Complex.I) - ((a : ℂ) + (y : ℂ) * Complex.I)) =
          exercise8_integrand k
              ((((a + t * (b - a)) : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
            ((b - a : ℝ) : ℂ) := by
    intro t
    rw [hline t, hdir]
    simp [mul_comm]
  calc
    ∫ t in (0 : ℝ)..1,
        ((exercise8_integrand k dz)
          ((AffineMap.lineMap ((a : ℂ) + (y : ℂ) * Complex.I)
            ((b : ℂ) + (y : ℂ) * Complex.I)) t))
          (((b : ℂ) + (y : ℂ) * Complex.I) - ((a : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ t in (0 : ℝ)..1,
          exercise8_integrand k
              ((((a + t * (b - a)) : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
            ((b - a : ℝ) : ℂ) := by
              refine intervalIntegral.integral_congr_ae ?_
              exact Filter.Eventually.of_forall (fun t _ ↦ hpoint t)
    _ =
        (∫ t in (0 : ℝ)..1,
          exercise8_integrand k
            ((((a + t * (b - a)) : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          ((b - a : ℝ) : ℂ) := by
            rw [intervalIntegral.integral_mul_const]

/-- Helper for Cartan section26 0018_Exercise_8: on the convex strict upper half-plane, the
Exercise 8 segment integrals are additive along broken segments because the integrand defines a
closed holomorphic `1`-form there. -/
lemma exercise8_segment_integral_add
    (k : Exercise8Modulus) (a b c : UpperHalfPlane) :
    (∫ᶜ w in Path.segment (a : ℂ) (b : ℂ), (exercise8_integrand k dz) w) +
        ∫ᶜ w in Path.segment (b : ℂ) (c : ℂ), (exercise8_integrand k dz) w =
      ∫ᶜ w in Path.segment (a : ℂ) (c : ℂ), (exercise8_integrand k dz) w := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (exercise8_integrand k dz) z
  have hωEq : (fun z : ℂ ↦ exercise8_integrand k z • (1 : ℂ →L[ℂ] ℂ)) = ω := by
    funext z
    ext
    simp [ω, mul_comm]
  let dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ := fun x ↦
    ContinuousLinearMap.smulRight
      (ContinuousLinearMap.restrictScalars (R := ℝ)
        (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
      (1 : ℂ →L[ℂ] ℂ)
  have hω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        HasFDerivWithinAt ω (dω x) UpperHalfPlane.upperHalfPlaneSet x := by
    intro x hx
    -- The closed-form theorem needs the derivative of the `dz`-valued integrand on `Im z > 0`.
    have hscalar :
        DifferentiableWithinAt ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x :=
      exercise8_integrand_differentiableOn_upper k x
        (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hx)
    have hscalarDeriv :
        HasFDerivWithinAt (exercise8_integrand k)
          (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x)
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalar.hasFDerivWithinAt
    have hscalarDerivR :
        HasFDerivWithinAt (exercise8_integrand k)
          (ContinuousLinearMap.restrictScalars (R := ℝ)
            (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalarDeriv.restrictScalars ℝ
    simpa [hωEq, dω] using hscalarDerivR.smul_const (1 : ℂ →L[ℂ] ℂ)
  have hdω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        ∀ u ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
          ∀ v ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
            dω x u v = dω x v u := by
    intro x hx u _ v _
    -- In one complex dimension, the bilinear derivative is symmetric by commutativity.
    let L := fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x
    have hu : L u = u * L 1 := by
      calc
        L u = L (u * (1 : ℂ)) := by simp
        _ = u * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    have hv : L v = v * L 1 := by
      calc
        L v = L (v * (1 : ℂ)) := by simp
        _ = v * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    simp [dω, L, hu, hv, mul_left_comm, mul_comm]
  -- Route correction: this is the reusable closed-form API that replaces the failed local
  -- primitive-through-`0` route.
  simpa [ω, dω] using
    Convex.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
      (s := UpperHalfPlane.upperHalfPlaneSet) (ω := ω) (dω := dω)
      exercise8_convex_upperHalfPlaneSet hω hdω a.2 b.2 c.2

/-- Helper for Cartan section26 0018_Exercise_8: if the source integrand is bounded by `2` on a
small upper-half-plane ball containing two interior endpoints, then the segment integral between
those endpoints is bounded by twice the segment length. -/
lemma exercise8_segment_integral_norm_le_two_mul_norm_sub_of_small
    (k : Exercise8Modulus) {R : ℝ}
    (hR_bound : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖exercise8_integrand k z‖ ≤ 2)
    (a b : UpperHalfPlane) (hRa : ‖(a : ℂ)‖ < R) (hRb : ‖(b : ℂ)‖ < R) :
    ‖∫ᶜ w in Path.segment (a : ℂ) (b : ℂ), (exercise8_integrand k dz) w‖ ≤
      2 * ‖(b : ℂ) - (a : ℂ)‖ := by
  -- Route correction: control the short connector by a direct curve-integral norm estimate, so
  -- later Abel-difference arguments do not need another ambient-to-vertical comparison lemma.
  refine norm_curveIntegral_segment_le ?_
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have hline_mem_ball :
      AffineMap.lineMap (a : ℂ) (b : ℂ) t ∈ Metric.ball (0 : ℂ) R := by
    -- Convexity of the open ball keeps every point of the segment inside the same small ball.
    refine (convex_ball (0 : ℂ) R).lineMap_mem ?_ ?_ ht
    · simpa [Metric.mem_ball, dist_eq_norm] using hRa
    · simpa [Metric.mem_ball, dist_eq_norm] using hRb
  have hline_mem_upper :
      AffineMap.lineMap (a : ℂ) (b : ℂ) t ∈ UpperHalfPlane.upperHalfPlaneSet := by
    -- The strict upper half-plane is convex, so the whole segment stays in `Im z > 0`.
    exact exercise8_convex_upperHalfPlaneSet.lineMap_mem a.2 b.2 ht
  have hline_norm : ‖AffineMap.lineMap (a : ℂ) (b : ℂ) t‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hline_mem_ball
  have hline_im : 0 < (AffineMap.lineMap (a : ℂ) (b : ℂ) t).im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hline_mem_upper
  -- Apply the near-zero integrand bound pointwise along the whole segment.
  simpa [mul_comm] using hR_bound _ hline_norm hline_im

/-- Helper for Cartan section26 0018_Exercise_8: with a fixed source point in the strict upper
half-plane, the corresponding segment integral varies continuously with the target. -/
lemma exercise8_upper_segment_integral_continuousAt
    (k : Exercise8Modulus) (a z0 : UpperHalfPlane) :
    ContinuousAt
      (fun z : UpperHalfPlane ↦
        ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w)
      z0 := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (exercise8_integrand k dz) z
  let H : ℂ → ℂ := fun z ↦ ∫ᶜ w in Path.segment (a : ℂ) z, ω w
  have hωEq : (fun z : ℂ ↦ exercise8_integrand k z • (1 : ℂ →L[ℂ] ℂ)) = ω := by
    funext z
    ext
    simp [ω, mul_comm]
  let dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ := fun x ↦
    ContinuousLinearMap.smulRight
      (ContinuousLinearMap.restrictScalars (R := ℝ)
        (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
      (1 : ℂ →L[ℂ] ℂ)
  have hω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        HasFDerivWithinAt ω (dω x) UpperHalfPlane.upperHalfPlaneSet x := by
    intro x hx
    -- The `dz`-valued integrand is differentiable on the strict upper half-plane.
    have hscalar :
        DifferentiableWithinAt ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x :=
      exercise8_integrand_differentiableOn_upper k x
        (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hx)
    have hscalarDeriv :
        HasFDerivWithinAt (exercise8_integrand k)
          (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x)
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalar.hasFDerivWithinAt
    have hscalarDerivR :
        HasFDerivWithinAt (exercise8_integrand k)
          (ContinuousLinearMap.restrictScalars (R := ℝ)
            (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalarDeriv.restrictScalars ℝ
    simpa [hωEq, dω] using hscalarDerivR.smul_const (1 : ℂ →L[ℂ] ℂ)
  have hdω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        ∀ u ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
          ∀ v ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
            dω x u v = dω x v u := by
    intro x hx u _ v _
    -- The same symmetric-derivative computation is reused for the primitive theorem.
    let L := fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x
    have hu : L u = u * L 1 := by
      calc
        L u = L (u * (1 : ℂ)) := by simp
        _ = u * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    have hv : L v = v * L 1 := by
      calc
        L v = L (v * (1 : ℂ)) := by simp
        _ = v * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    simp [dω, L, hu, hv, mul_left_comm, mul_comm]
  have hderiv :
      HasFDerivWithinAt H (ω z0) UpperHalfPlane.upperHalfPlaneSet z0 := by
    -- The convex closed-form primitive theorem gives the target derivative directly at `z0`.
    simpa [H, ω, dω] using
      Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
        (s := UpperHalfPlane.upperHalfPlaneSet) (ω := ω) (dω := dω)
        exercise8_convex_upperHalfPlaneSet hω hdω a.2 z0.2
  have hcontWithin : ContinuousWithinAt H UpperHalfPlane.upperHalfPlaneSet z0 :=
    hderiv.continuousWithinAt
  have hcont : ContinuousAt H z0 :=
    hcontWithin.continuousAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z0.2)
  -- Restrict the ambient continuity statement back to the subtype owner.
  simpa [H, ω] using hcont.comp UpperHalfPlane.continuous_coe.continuousAt

/-- Helper for Cartan section26 0018_Exercise_8: fixing the source endpoint `a`, the corresponding
segment primitive is holomorphic on the ambient strict upper half-plane. -/
lemma exercise8_segmentPrimitive_differentiableAmbient
    (k : Exercise8Modulus) (a : UpperHalfPlane) :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ᶜ w in Path.segment (a : ℂ) z, (exercise8_integrand k dz) w)
      UpperHalfPlane.upperHalfPlaneSet := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (exercise8_integrand k dz) z
  have hωEq : (fun z : ℂ ↦ exercise8_integrand k z • (1 : ℂ →L[ℂ] ℂ)) = ω := by
    funext z
    ext
    simp [ω, mul_comm]
  let dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ := fun x ↦
    ContinuousLinearMap.smulRight
      (ContinuousLinearMap.restrictScalars (R := ℝ)
        (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
      (1 : ℂ →L[ℂ] ℂ)
  have hω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        HasFDerivWithinAt ω (dω x) UpperHalfPlane.upperHalfPlaneSet x := by
    intro x hx
    -- The ambient `dz`-valued integrand is differentiable on `Im z > 0`.
    have hscalar :
        DifferentiableWithinAt ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x :=
      exercise8_integrand_differentiableOn_upper k x
        (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hx)
    have hscalarDeriv :
        HasFDerivWithinAt (exercise8_integrand k)
          (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x)
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalar.hasFDerivWithinAt
    have hscalarDerivR :
        HasFDerivWithinAt (exercise8_integrand k)
          (ContinuousLinearMap.restrictScalars (R := ℝ)
            (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalarDeriv.restrictScalars ℝ
    simpa [hωEq, dω] using hscalarDerivR.smul_const (1 : ℂ →L[ℂ] ℂ)
  have hdω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        ∀ u ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
          ∀ v ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
            dω x u v = dω x v u := by
    intro x hx u _ v _
    -- In one complex dimension, the bilinear derivative is symmetric by commutativity.
    let L := fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x
    have hu : L u = u * L 1 := by
      calc
        L u = L (u * (1 : ℂ)) := by simp
        _ = u * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    have hv : L v = v * L 1 := by
      calc
        L v = L (v * (1 : ℂ)) := by simp
        _ = v * L 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    simp [dω, L, hu, hv, mul_left_comm, mul_comm]
  intro z hz
  -- The convex closed-form primitive theorem differentiates the segment primitive directly.
  have hderiv :
      HasFDerivWithinAt
        (fun z : ℂ ↦ ∫ᶜ w in Path.segment (a : ℂ) z, (exercise8_integrand k dz) w)
        (ω z) UpperHalfPlane.upperHalfPlaneSet z := by
    simpa [ω, dω] using
        Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
          (s := UpperHalfPlane.upperHalfPlaneSet) (ω := ω) (dω := dω)
        exercise8_convex_upperHalfPlaneSet hω hdω a.2 hz
  exact hderiv.differentiableWithinAt

/-- Helper for Cartan section26 0018_Exercise_8: at a real-axis point, continuity of the canonical
closed-half-plane owner is exactly the source boundary-limit bridge from the Abel integral to the
repaired boundary trace. -/
lemma exercise8_closed_extension_continuousAt_boundary_of_tendsto
    (k : Exercise8Modulus) {z : ClosedUpperHalfPlane} (hz : ((z : ℂ)).im = 0)
    (hlimit :
      Filter.Tendsto (exercise8_closed_extension k)
        (nhdsWithin z {w : ClosedUpperHalfPlane | 0 < ((w : ℂ)).im})
        (nhds (exercise8_boundary_trace k ((z : ℂ).re)))) :
    ContinuousAt (exercise8_closed_extension k) z := by
  let boundarySlice : Set ClosedUpperHalfPlane := {w | ((w : ℂ)).im = 0}
  let upperSlice : Set ClosedUpperHalfPlane := {w | 0 < ((w : ℂ)).im}
  have hboundaryOwner :
      ContinuousWithinAt
        (fun w : ClosedUpperHalfPlane ↦ exercise8_boundary_trace k ((w : ℂ).re))
        boundarySlice z :=
    (exercise8_boundary_trace_re_continuous k).continuousAt.continuousWithinAt
  have hboundary : ContinuousWithinAt (exercise8_closed_extension k) boundarySlice z := by
    -- Along the real axis, the canonical owner is literally the repaired boundary trace.
    refine hboundaryOwner.congr ?_ ?_
    · intro w hw
      simpa [boundarySlice] using
        (exercise8_closed_extension_eq_boundary_trace_of_im_zero (k := k) hw)
    · simpa [boundarySlice] using
        (exercise8_closed_extension_eq_boundary_trace_of_im_zero (k := k) hz)
  have hupper : ContinuousWithinAt (exercise8_closed_extension k) upperSlice z := by
    -- The only missing input is the from-above limit on the strict upper slice.
    simpa [ContinuousWithinAt, upperSlice,
      exercise8_closed_extension_eq_boundary_trace_of_im_zero (k := k) hz] using hlimit
  have hunion : boundarySlice ∪ upperSlice = Set.univ := by
    -- Every closed-upper-half-plane point is either on the boundary or strictly above it.
    ext w
    constructor
    · intro _
      simp
    · intro _
      by_cases hw : ((w : ℂ)).im = 0
      · exact Or.inl hw
      · exact Or.inr (lt_of_le_of_ne w.2 (Ne.symm hw))
  -- Glue the boundary slice to the strict upper slice inside the closed half-plane.
  simpa [ContinuousAt, ContinuousWithinAt, hunion] using hboundary.union hupper

/-- Helper for Cartan section26 0018_Exercise_8: when the Exercise 8 integrand is uniformly
bounded by `2` on the short ray from `0` to `z`, the corresponding Abel integral is bounded by
`2 ‖z‖`. -/
lemma exercise8_abel_integral_norm_le_two_mul_norm_of_small
    (k : Exercise8Modulus) {R : ℝ}
    (hR_bound : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖exercise8_integrand k z‖ ≤ 2)
    (z : UpperHalfPlane) (hzR : ‖(z : ℂ)‖ < R) :
    ‖exercise8_abel_integral k z‖ ≤ 2 * ‖(z : ℂ)‖ := by
  -- Rewrite the segment integral in ray coordinates so the source near-zero bound applies pointwise
  -- on the interval `(0, 1]`.
  rw [exercise8_abel_integral_def, curveIntegral_segment]
  refine
    (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * ‖(z : ℂ)‖) ?_).trans ?_
  · intro t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le zero_le_one] using ht
    have ht_pos : 0 < t := ht'.1
    have ht_le : t ≤ 1 := ht'.2
    have hscaled_im : 0 < (((t : ℂ) * (z : ℂ)).im) := by
      simpa [Complex.mul_im, mul_comm] using mul_pos ht_pos z.im_pos
    have hscaled_norm : ‖(t : ℂ) * (z : ℂ)‖ < R := by
      calc
        ‖(t : ℂ) * (z : ℂ)‖ = |t| * ‖(z : ℂ)‖ := by
          simpa using norm_mul (t : ℂ) (z : ℂ)
        _ = t * ‖(z : ℂ)‖ := by rw [abs_of_pos ht_pos]
        _ ≤ 1 * ‖(z : ℂ)‖ := by
              gcongr
        _ = ‖(z : ℂ)‖ := by ring
        _ < R := hzR
    have hbound :
        ‖exercise8_integrand k ((t : ℂ) * (z : ℂ))‖ ≤ 2 :=
      hR_bound _ hscaled_norm hscaled_im
    -- The line-map formula turns the curve integral kernel into the ray kernel `t ↦ t z`.
    simpa [AffineMap.lineMap_apply, mul_comm, mul_left_comm, mul_assoc] using
      (show ‖exercise8_integrand k ((t : ℂ) * (z : ℂ)) * (z : ℂ)‖ ≤ 2 * ‖(z : ℂ)‖ by
        calc
          ‖exercise8_integrand k ((t : ℂ) * (z : ℂ)) * (z : ℂ)‖
              = ‖exercise8_integrand k ((t : ℂ) * (z : ℂ))‖ * ‖(z : ℂ)‖ := by
                  rw [norm_mul]
          _ ≤ 2 * ‖(z : ℂ)‖ := by
                gcongr)
  · simpa

/-- Helper for Cartan section26 0018_Exercise_8: approaching the origin from the strict upper
half-plane sends the Abel integral to the boundary value `0`. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_zero
    (k : Exercise8Modulus) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k 0)) := by
  have hzero : exercise8_boundary_trace k 0 = 0 := by
    -- The repaired boundary trace is normalized to vanish at the source base point.
    simpa using exercise8_boundary_value_zero k
  rcases exercise8_integrand_bounded_near_zero k with ⟨R, hR_pos, hR_bound⟩
  rw [hzero, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min R (ε / 4), lt_min hR_pos (by positivity), ?_⟩
  intro w hw hdist
  have hw_im : 0 < w.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hw
  have hw_small : ‖w‖ < min R (ε / 4) := by
    simpa [dist_eq_norm] using hdist
  have hwR : ‖w‖ < R := lt_of_lt_of_le hw_small (min_le_left _ _)
  have hof :
      (((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)) = w := by
    -- On strict upper-half-plane points, `ofComplex` is just the subtype constructor.
    simpa using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply (⟨w, hw_im⟩ : UpperHalfPlane))
  have hbound :
      ‖exercise8_abel_integral k (UpperHalfPlane.ofComplex w)‖ ≤ 2 * ‖w‖ := by
    -- The short segment from `0` to `w` stays inside the bounded near-zero neighborhood.
    simpa [hof] using
      exercise8_abel_integral_norm_le_two_mul_norm_of_small k hR_bound
        (UpperHalfPlane.ofComplex w) (by simpa [hof] using hwR)
  have hnorm_lt : 2 * ‖w‖ < ε := by
    have hwε : ‖w‖ < ε / 4 := lt_of_lt_of_le hw_small (min_le_right _ _)
    nlinarith
  -- Combine the explicit near-zero bound with the metric characterization of `nhdsWithin`.
  simpa [dist_eq_norm] using lt_of_le_of_lt hbound hnorm_lt

/-- Helper for Exercise 8: scaling both endpoints by `r ∈ (0, 1]` preserves the Abel-difference
`f(z) - f(a) - ∫_a^z`. -/
lemma exercise8_abelIntegral_difference_eq_scaled
    (k : Exercise8Modulus) (a z : UpperHalfPlane) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    exercise8_abel_integral k z - exercise8_abel_integral k a -
        ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w =
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ))) -
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((r : ℂ) * (a : ℂ))) -
          ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
            (exercise8_integrand k dz) w := by
  let ar : UpperHalfPlane := UpperHalfPlane.ofComplex ((r : ℂ) * (a : ℂ))
  let zr : UpperHalfPlane := UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ))
  have har_im : 0 < (((r : ℂ) * (a : ℂ)).im) := by
    simpa [Complex.mul_im, mul_comm] using mul_pos hr0 a.im_pos
  have hzr_im : 0 < (((r : ℂ) * (z : ℂ)).im) := by
    simpa [Complex.mul_im, mul_comm] using mul_pos hr0 z.im_pos
  have har_coe : ((ar : UpperHalfPlane) : ℂ) = (r : ℂ) * (a : ℂ) := by
    simpa [ar] using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos har_im)
  have hzr_coe : ((zr : UpperHalfPlane) : ℂ) = (r : ℂ) * (z : ℂ) := by
    simpa [zr] using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos hzr_im)
  have har_split :
      exercise8_abel_integral k a =
        exercise8_abel_integral k ar +
          ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w := by
    -- The Abel integral already splits additively at any positive rescaling of the endpoint.
    simpa [ar] using exercise8_abel_integral_eq_scaled_add_tail k a (r := r) hr0 hr1
  have hzr_split :
      exercise8_abel_integral k z =
        exercise8_abel_integral k zr +
          ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w := by
    -- Apply the same same-ray splitting to the target endpoint `z`.
    simpa [zr] using exercise8_abel_integral_eq_scaled_add_tail k z (r := r) hr0 hr1
  have hpath_through_a :
      (∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w) +
          ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w =
        ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (z : ℂ), (exercise8_integrand k dz) w := by
    -- The broken path `r a -> a -> z` lies entirely in the strict upper half-plane.
    have htmp := exercise8_segment_integral_add k ar a z
    rw [har_coe] at htmp
    exact htmp
  have hpath_through_scaled :
      (∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
          (exercise8_integrand k dz) w) +
          ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w =
        ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (z : ℂ), (exercise8_integrand k dz) w := by
    -- The same total connector also factors through the scaled endpoint `r z`.
    have htmp := exercise8_segment_integral_add k ar zr z
    rw [har_coe, hzr_coe] at htmp
    exact htmp
  have hconnector :
      (∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w) -
            ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w -
            ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w =
        -∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
          (exercise8_integrand k dz) w := by
    have hsame :
        (∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w) +
            ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w =
          (∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
              (exercise8_integrand k dz) w) +
            ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w := by
      rw [hpath_through_a, hpath_through_scaled]
    -- Compare the two decompositions of the same segment from `r a` to `z`.
    calc
      (∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w) -
            ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w -
            ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w =
          (∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w) -
            ((∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w) +
              ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w) := by
                ring
      _ =
          (∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w) -
            ((∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
                (exercise8_integrand k dz) w) +
              ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w) := by
                rw [hsame]
      _ =
          -∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
            (exercise8_integrand k dz) w := by
              ring
  -- Substitute the same-ray splits and collapse the connector with the path comparison above.
  calc
    exercise8_abel_integral k z - exercise8_abel_integral k a -
          ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w =
        (exercise8_abel_integral k zr +
            ∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w) -
          (exercise8_abel_integral k ar +
            ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w) -
          ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w := by
            rw [hzr_split, har_split]
    _ =
        exercise8_abel_integral k zr - exercise8_abel_integral k ar +
          ((∫ᶜ w in Path.segment ((r : ℂ) * (z : ℂ)) (z : ℂ), (exercise8_integrand k dz) w) -
            ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) (a : ℂ), (exercise8_integrand k dz) w -
            ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w) := by
              ring
    _ =
        exercise8_abel_integral k zr - exercise8_abel_integral k ar +
          (-∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
            (exercise8_integrand k dz) w) := by
              rw [hconnector]
    _ =
        exercise8_abel_integral k zr - exercise8_abel_integral k ar -
          ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
            (exercise8_integrand k dz) w := by
              ring

/-- Helper for Exercise 8: once the scaled-difference residual is controlled near `0`, the Abel
integral between two interior points is exactly the segment integral joining them. -/
lemma exercise8_abelIntegral_eq_anchor_add_segment
    (k : Exercise8Modulus) (a z : UpperHalfPlane) :
    exercise8_abel_integral k z =
      exercise8_abel_integral k a +
        ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w := by
  let Δ : ℂ :=
    exercise8_abel_integral k z - exercise8_abel_integral k a -
      ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w
  have hΔ : Δ = 0 := by
    by_contra hΔ_ne
    have hΔ_norm_pos : 0 < ‖Δ‖ := norm_pos_iff.mpr hΔ_ne
    rcases exercise8_integrand_bounded_near_zero k with ⟨R, hR_pos, hR_bound⟩
    let D : ℝ := ‖(a : ℂ)‖ + ‖(z : ℂ)‖ + ‖(z : ℂ) - (a : ℂ)‖ + 1
    have hD_pos : 0 < D := by
      positivity
    have hnorm_a_lt : ‖(a : ℂ)‖ < D := by
      dsimp [D]
      nlinarith [norm_nonneg (a : ℂ), norm_nonneg (z : ℂ), norm_nonneg ((z : ℂ) - (a : ℂ))]
    have hnorm_z_lt : ‖(z : ℂ)‖ < D := by
      dsimp [D]
      nlinarith [norm_nonneg (a : ℂ), norm_nonneg (z : ℂ), norm_nonneg ((z : ℂ) - (a : ℂ))]
    have hnorm_sub_lt : ‖(z : ℂ) - (a : ℂ)‖ < D := by
      dsimp [D]
      nlinarith [norm_nonneg (a : ℂ), norm_nonneg (z : ℂ), norm_nonneg ((z : ℂ) - (a : ℂ))]
    let r : ℝ := min 1 (min (R / D) (‖Δ‖ / (4 * D)))
    have hr0 : 0 < r := by
      dsimp [r]
      refine lt_min zero_lt_one ?_
      refine lt_min ?_ ?_
      · exact div_pos hR_pos hD_pos
      · exact div_pos hΔ_norm_pos (by positivity)
    have hr1 : r ≤ 1 := by
      dsimp [r]
      exact min_le_left _ _
    have hrRD : r ≤ R / D := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hrΔ : r ≤ ‖Δ‖ / (4 * D) := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    let ar : UpperHalfPlane := UpperHalfPlane.ofComplex ((r : ℂ) * (a : ℂ))
    let zr : UpperHalfPlane := UpperHalfPlane.ofComplex ((r : ℂ) * (z : ℂ))
    have har_im : 0 < (((r : ℂ) * (a : ℂ)).im) :=
      exercise8_im_pos_mul_of_upper (z := a) hr0
    have hzr_im : 0 < (((r : ℂ) * (z : ℂ)).im) :=
      exercise8_im_pos_mul_of_upper (z := z) hr0
    have har_coe : ((ar : UpperHalfPlane) : ℂ) = (r : ℂ) * (a : ℂ) := by
      simpa [ar] using
        congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
          (UpperHalfPlane.ofComplex_apply_of_im_pos har_im)
    have hzr_coe : ((zr : UpperHalfPlane) : ℂ) = (r : ℂ) * (z : ℂ) := by
      simpa [zr] using
        congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
          (UpperHalfPlane.ofComplex_apply_of_im_pos hzr_im)
    have hnorm_ar : ‖((ar : UpperHalfPlane) : ℂ)‖ = r * ‖(a : ℂ)‖ := by
      rw [har_coe, norm_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg hr0.le]
    have hnorm_zr : ‖((zr : UpperHalfPlane) : ℂ)‖ = r * ‖(z : ℂ)‖ := by
      rw [hzr_coe, norm_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg hr0.le]
    have hnorm_scaled_sub :
        ‖(r : ℂ) * (z : ℂ) - (r : ℂ) * (a : ℂ)‖ =
          r * ‖(z : ℂ) - (a : ℂ)‖ := by
      calc
        ‖(r : ℂ) * (z : ℂ) - (r : ℂ) * (a : ℂ)‖ = ‖(r : ℂ) * ((z : ℂ) - (a : ℂ))‖ := by
            congr 1
            ring
        _ = r * ‖(z : ℂ) - (a : ℂ)‖ := by
            rw [norm_mul]
            simp [Real.norm_eq_abs, abs_of_nonneg hr0.le]
    have har_small : ‖((ar : UpperHalfPlane) : ℂ)‖ < R := by
      calc
        ‖((ar : UpperHalfPlane) : ℂ)‖ = r * ‖(a : ℂ)‖ := hnorm_ar
        _ ≤ (R / D) * ‖(a : ℂ)‖ := by
              gcongr
        _ < (R / D) * D := by
              gcongr
        _ = R := by
              field_simp [hD_pos.ne']
    have hzr_small : ‖((zr : UpperHalfPlane) : ℂ)‖ < R := by
      calc
        ‖((zr : UpperHalfPlane) : ℂ)‖ = r * ‖(z : ℂ)‖ := hnorm_zr
        _ ≤ (R / D) * ‖(z : ℂ)‖ := by
              gcongr
        _ < (R / D) * D := by
              gcongr
        _ = R := by
              field_simp [hD_pos.ne']
    have hscaled :
        Δ =
          exercise8_abel_integral k zr - exercise8_abel_integral k ar -
            ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
              (exercise8_integrand k dz) w := by
      simpa [Δ, ar, zr] using exercise8_abelIntegral_difference_eq_scaled k a z hr0 hr1
    have hbound_z :
        ‖exercise8_abel_integral k zr‖ ≤ 2 * (r * ‖(z : ℂ)‖) := by
      simpa [hnorm_zr] using
        exercise8_abel_integral_norm_le_two_mul_norm_of_small k hR_bound zr hzr_small
    have hbound_a :
        ‖exercise8_abel_integral k ar‖ ≤ 2 * (r * ‖(a : ℂ)‖) := by
      simpa [hnorm_ar] using
        exercise8_abel_integral_norm_le_two_mul_norm_of_small k hR_bound ar har_small
    have hbound_seg_raw :
        ‖∫ᶜ w in Path.segment ((ar : UpperHalfPlane) : ℂ) ((zr : UpperHalfPlane) : ℂ),
            (exercise8_integrand k dz) w‖ ≤
          2 * (r * ‖(z : ℂ) - (a : ℂ)‖) := by
      have hbound_seg_raw' :=
        exercise8_segment_integral_norm_le_two_mul_norm_sub_of_small
          k hR_bound ar zr har_small hzr_small
      calc
        ‖∫ᶜ w in Path.segment ((ar : UpperHalfPlane) : ℂ) ((zr : UpperHalfPlane) : ℂ),
            (exercise8_integrand k dz) w‖ ≤
          2 * ‖((zr : UpperHalfPlane) : ℂ) - ((ar : UpperHalfPlane) : ℂ)‖ := hbound_seg_raw'
        _ = 2 * (r * ‖(z : ℂ) - (a : ℂ)‖) := by
              rw [har_coe, hzr_coe, hnorm_scaled_sub]
    have hbound_seg :
        ‖∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
            (exercise8_integrand k dz) w‖ ≤
          2 * (r * ‖(z : ℂ) - (a : ℂ)‖) := by
      calc
        ‖∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
            (exercise8_integrand k dz) w‖ =
          ‖∫ᶜ w in Path.segment ((ar : UpperHalfPlane) : ℂ) ((zr : UpperHalfPlane) : ℂ),
              (exercise8_integrand k dz) w‖ := by
                rw [har_coe, hzr_coe]
        _ ≤ 2 * (r * ‖(z : ℂ) - (a : ℂ)‖) := hbound_seg_raw
    have hΔ_bound :
        ‖Δ‖ ≤
          2 * (r * ‖(z : ℂ)‖) +
            2 * (r * ‖(a : ℂ)‖) +
              2 * (r * ‖(z : ℂ) - (a : ℂ)‖) := by
      rw [hscaled]
      calc
        ‖exercise8_abel_integral k zr - exercise8_abel_integral k ar -
            ∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
              (exercise8_integrand k dz) w‖
            ≤ ‖exercise8_abel_integral k zr - exercise8_abel_integral k ar‖ +
                ‖∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
                    (exercise8_integrand k dz) w‖ := by
                exact norm_sub_le _ _
        _ ≤ (‖exercise8_abel_integral k zr‖ + ‖exercise8_abel_integral k ar‖) +
                ‖∫ᶜ w in Path.segment ((r : ℂ) * (a : ℂ)) ((r : ℂ) * (z : ℂ)),
                    (exercise8_integrand k dz) w‖ := by
                gcongr
                exact norm_sub_le _ _
        _ ≤ (2 * (r * ‖(z : ℂ)‖) + 2 * (r * ‖(a : ℂ)‖)) +
                2 * (r * ‖(z : ℂ) - (a : ℂ)‖) := by
                gcongr
        _ = 2 * (r * ‖(z : ℂ)‖) + 2 * (r * ‖(a : ℂ)‖) +
              2 * (r * ‖(z : ℂ) - (a : ℂ)‖) := by
                ring
    have hsmall :
        2 * (r * ‖(z : ℂ)‖) + 2 * (r * ‖(a : ℂ)‖) +
            2 * (r * ‖(z : ℂ) - (a : ℂ)‖) <
          ‖Δ‖ := by
      have hsum_lt :
          ‖(z : ℂ)‖ + ‖(a : ℂ)‖ + ‖(z : ℂ) - (a : ℂ)‖ < D := by
        dsimp [D]
        nlinarith [norm_nonneg (a : ℂ), norm_nonneg (z : ℂ), norm_nonneg ((z : ℂ) - (a : ℂ))]
      calc
        2 * (r * ‖(z : ℂ)‖) + 2 * (r * ‖(a : ℂ)‖) +
              2 * (r * ‖(z : ℂ) - (a : ℂ)‖)
            = 2 * r * (‖(z : ℂ)‖ + ‖(a : ℂ)‖ + ‖(z : ℂ) - (a : ℂ)‖) := by
                ring
        _ ≤ 2 * (‖Δ‖ / (4 * D)) *
              (‖(z : ℂ)‖ + ‖(a : ℂ)‖ + ‖(z : ℂ) - (a : ℂ)‖) := by
              gcongr
        _ < 2 * (‖Δ‖ / (4 * D)) * D := by
              gcongr
        _ = ‖Δ‖ / 2 := by
              field_simp [hD_pos.ne']
              ring
        _ < ‖Δ‖ := by
              linarith
    exact lt_irrefl ‖Δ‖ (lt_of_le_of_lt hΔ_bound hsmall)
  -- The vanishing residual is exactly the desired fixed-anchor identity.
  have hΔ_zero :
      exercise8_abel_integral k z -
            (exercise8_abel_integral k a +
              ∫ᶜ w in Path.segment (a : ℂ) (z : ℂ), (exercise8_integrand k dz) w) = 0 := by
    simpa [Δ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hΔ
  exact sub_eq_zero.mp hΔ_zero
