import Mathlib

open Filter Metric Complex
open scoped Topology

-- Declarations for this item will be appended below by the statement pipeline.

private theorem diffContOnCl_intermediate_ball
    {f : ℂ → ℂ} {ρ r : ℝ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ)) :
    DiffContOnCl ℂ f (ball (0 : ℂ) ((ρ + r) / 2)) := by
  refine DiffContOnCl.mk_ball ?_ ?_
  · refine hf.mono <| ball_subset_ball ?_
    linarith
  · exact hf.continuousOn.mono <| closedBall_subset_ball <| by linarith

/-- Helper for Cartan section06 0028_Exercise_13: the pointwise difference-quotient integrand
collapses to the single kernel from the textbook identity. -/
private lemma differenceQuotientIntegrand_identity {a t z h : ℂ}
    (hh : h ≠ 0) (htz : t ≠ z) (htzh : t ≠ z + h) :
    ((a / (t - (z + h)) - a / (t - z)) / h - a / (t - z) ^ 2) =
      h * (a / ((t - z - h) * (t - z) ^ 2)) := by
  have htz' : t - z ≠ 0 := sub_ne_zero.mpr htz
  have htzh' : t - (z + h) ≠ 0 := sub_ne_zero.mpr htzh
  have htzh'' : t - z - h ≠ 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htzh'
  -- Clear the denominators once, then normalize the numerator algebraically.
  field_simp [hh, htz', htzh'']
  ring_nf

/-- Helper for Cartan section06 0028_Exercise_13: on the intermediate circle, `t - z` stays
uniformly away from `0` by at least `(ρ - r) / 2`. -/
private theorem intermediateSphere_sub_lowerBound
    {ρ r : ℝ} {z t : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r)
    (ht : t ∈ sphere (0 : ℂ) ((ρ + r) / 2)) :
    (ρ - r) / 2 ≤ ‖t - z‖ := by
  have hz_norm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have ht_norm : ‖t‖ = (ρ + r) / 2 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using ht
  have htri : ‖t‖ ≤ ‖t - z‖ + ‖z‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le (t - z) z
  -- The circle radius is larger than the closed-ball radius by exactly `(ρ - r) / 2`.
  linarith

/-- Helper for Cartan section06 0028_Exercise_13: subtracting a small increment `h` still leaves
the intermediate-circle denominator uniformly bounded below. -/
private theorem intermediateSphere_sub_sub_lowerBound
    {ρ r : ℝ} {z h t : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r)
    (hh : ‖h‖ < (ρ - r) / 4)
    (ht : t ∈ sphere (0 : ℂ) ((ρ + r) / 2)) :
    (ρ - r) / 4 < ‖t - z - h‖ := by
  have htz : (ρ - r) / 2 ≤ ‖t - z‖ :=
    intermediateSphere_sub_lowerBound hz ht
  have htri : ‖t - z‖ ≤ ‖t - z - h‖ + ‖h‖ := by
    convert norm_add_le (t - z - h) h using 1
    ring_nf
  -- The `‖h‖ < (ρ - r) / 4` hypothesis preserves half of the original distance from the pole.
  linarith

/-- Helper for Cartan section06 0028_Exercise_13: the single-kernel integrand is uniformly bounded
on the intermediate circle by the boundary supremum and the geometric denominator estimate. -/
private theorem differenceQuotientIntegrand_bound
    {f : ℂ → ℂ} {ρ r M : ℝ} {z h t : ℂ}
    (hrρ : r < ρ)
    (hz : z ∈ closedBall (0 : ℂ) r)
    (hh : ‖h‖ < (ρ - r) / 4)
    (hM : ∀ u ∈ sphere (0 : ℂ) ((ρ + r) / 2), ‖f u‖ ≤ M)
    (ht : t ∈ sphere (0 : ℂ) ((ρ + r) / 2)) :
    ‖f t / ((t - z - h) * (t - z) ^ 2)‖ ≤ 16 * M / (ρ - r) ^ 3 := by
  have hrr : 0 < ρ - r := by
    linarith
  have hM_nonneg : 0 ≤ M := by
    let R : ℝ := (ρ + r) / 2
    have hR_nonneg : 0 ≤ R := by
      have hz_norm : ‖z‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg z) hz_norm
      dsimp [R]
      linarith
    have hmem : ((R : ℂ)) ∈ sphere (0 : ℂ) R := by
      simp [Complex.norm_real, abs_of_nonneg hR_nonneg]
    have hbound := hM (R : ℂ) (by simpa [R] using hmem)
    have hnorm_nonneg : 0 ≤ ‖f (R : ℂ)‖ := norm_nonneg _
    linarith
  have htz : (ρ - r) / 2 ≤ ‖t - z‖ :=
    intermediateSphere_sub_lowerBound hz ht
  have htzh : (ρ - r) / 4 < ‖t - z - h‖ :=
    intermediateSphere_sub_sub_lowerBound hz hh ht
  have hsq : ((ρ - r) / 2) ^ 2 ≤ ‖t - z‖ ^ 2 := by
    nlinarith [htz, norm_nonneg (t - z)]
  have htmp : ((ρ - r) / 4) * ‖t - z‖ ^ 2 < ‖t - z - h‖ * ‖t - z‖ ^ 2 := by
    have htz_pos : 0 < ‖t - z‖ := by
      linarith
    exact mul_lt_mul_of_pos_right htzh (sq_pos_of_pos htz_pos)
  have hden : (ρ - r) ^ 3 / 16 < ‖t - z - h‖ * ‖t - z‖ ^ 2 := by
    have hleft : (ρ - r) ^ 3 / 16 = ((ρ - r) / 4) * ((ρ - r) / 2) ^ 2 := by
      ring
    rw [hleft]
    have hmono : ((ρ - r) / 4) * ((ρ - r) / 2) ^ 2 ≤ ((ρ - r) / 4) * ‖t - z‖ ^ 2 := by
      gcongr
    exact lt_of_le_of_lt hmono htmp
  rw [norm_div, norm_mul, norm_pow]
  have hsmallpos : 0 < (ρ - r) ^ 3 / 16 := by
    positivity
  have hstep1 :
      ‖f t‖ / (‖t - z - h‖ * ‖t - z‖ ^ 2) ≤ ‖f t‖ / ((ρ - r) ^ 3 / 16) := by
    exact div_le_div_of_nonneg_left (norm_nonneg _) hsmallpos hden.le
  have hstep2 :
      ‖f t‖ / ((ρ - r) ^ 3 / 16) ≤ M / ((ρ - r) ^ 3 / 16) := by
    exact div_le_div_of_nonneg_right (hM _ ht) hsmallpos.le
  calc
    ‖f t‖ / (‖t - z - h‖ * ‖t - z‖ ^ 2) ≤ M / ((ρ - r) ^ 3 / 16) :=
      hstep1.trans hstep2
    _ = 16 * M / (ρ - r) ^ 3 := by
      have hpow : (ρ - r) ^ 3 ≠ 0 := by
        positivity
      field_simp [hpow]

/-- Helper for Cartan section06 0028_Exercise_13: if both poles lie strictly inside the circle,
the three Cauchy kernels used in the difference-quotient identity are circle-integrable. -/
private lemma cauchyDifferenceQuotientTerms_circleIntegrable
    {f : ℂ → ℂ} {R : ℝ} {z h : ℂ}
    (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall (0 : ℂ) R))
    (hz : z ∈ ball (0 : ℂ) R)
    (hzh : z + h ∈ ball (0 : ℂ) R) :
    CircleIntegrable (fun t ↦ f t / (t - (z + h))) 0 R ∧
      CircleIntegrable (fun t ↦ f t / (t - z)) 0 R ∧
      CircleIntegrable (fun t ↦ f t / (t - z) ^ 2) 0 R := by
  have hcont_f : ContinuousOn f (sphere (0 : ℂ) R) := hcont.mono sphere_subset_closedBall
  have hAcont : ContinuousOn (fun t : ℂ ↦ f t / (t - (z + h))) (sphere (0 : ℂ) R) := by
    -- The pole `z + h` stays inside the circle, so the boundary denominator never vanishes.
    refine hcont_f.div (continuousOn_id.sub continuousOn_const) ?_
    intro t ht
    exact sub_ne_zero.2 (Metric.sphere_disjoint_ball.ne_of_mem ht hzh)
  have hBcont : ContinuousOn (fun t : ℂ ↦ f t / (t - z)) (sphere (0 : ℂ) R) := by
    -- The same boundary nonvanishing argument applies to the pole at `z`.
    refine hcont_f.div (continuousOn_id.sub continuousOn_const) ?_
    intro t ht
    exact sub_ne_zero.2 (Metric.sphere_disjoint_ball.ne_of_mem ht hz)
  have hCcont : ContinuousOn (fun t : ℂ ↦ f t / (t - z) ^ 2) (sphere (0 : ℂ) R) := by
    -- Squaring the denominator preserves boundary nonvanishing because the simple pole is absent.
    refine hcont_f.div ((continuousOn_id.sub continuousOn_const).pow 2) ?_
    intro t ht
    exact pow_ne_zero 2 (sub_ne_zero.2 (Metric.sphere_disjoint_ball.ne_of_mem ht hz))
  refine ⟨ContinuousOn.circleIntegrable hR.le hAcont, ContinuousOn.circleIntegrable hR.le hBcont,
    ContinuousOn.circleIntegrable hR.le hCcont⟩

/-- Helper for Cartan section06 0028_Exercise_13: package the separated contour terms
`((∮ A - ∮ B) / h - ∮ C)` into one contour integral before applying the kernel identity. -/
private lemma differenceQuotientCircleIntegralLinearization
    {c h : ℂ} {R : ℝ} {A B C : ℂ → ℂ}
    (hR : 0 ≤ R)
    (hA : CircleIntegrable A c R)
    (hB : CircleIntegrable B c R)
    (hC : CircleIntegrable C c R) :
    ((∮ t in C(c, R), A t) - ∮ t in C(c, R), B t) / h - ∮ t in C(c, R), C t =
      ∮ t in C(c, R), ((A t - B t) / h - C t) := by
  have hAB : CircleIntegrable (fun t ↦ A t - B t) c R := hA.sub hB
  have hABdiv : CircleIntegrable (fun t ↦ (A t - B t) / h) c R := by
    have hscaled : CircleIntegrable (fun t ↦ (1 / h) * (A t - B t)) c R := hAB.const_mul (1 / h)
    simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hdiv :
      ∮ t in C(c, R), (A t - B t) / h =
        ((∮ t in C(c, R), A t) - ∮ t in C(c, R), B t) / h := by
    calc
      ∮ t in C(c, R), (A t - B t) / h = ∮ t in C(c, R), (1 / h) * (A t - B t) := by
        refine circleIntegral.integral_congr hR ?_
        intro t ht
        simp [div_eq_mul_inv, mul_comm]
      _ = (1 / h) * ∮ t in C(c, R), (A t - B t) := by
        rw [circleIntegral.integral_const_mul]
      _ = (1 / h) * ((∮ t in C(c, R), A t) - ∮ t in C(c, R), B t) := by
        rw [circleIntegral.integral_sub hA hB]
      _ = ((∮ t in C(c, R), A t) - ∮ t in C(c, R), B t) / h := by
        simp [div_eq_mul_inv, mul_comm]
  -- Convert the quotient of the separated integrals into one contour integral before
  -- using the pointwise kernel identity.
  calc
    ((∮ t in C(c, R), A t) - ∮ t in C(c, R), B t) / h - ∮ t in C(c, R), C t
        = (∮ t in C(c, R), (A t - B t) / h) - ∮ t in C(c, R), C t := by
            rw [← hdiv]
    _ = ∮ t in C(c, R), ((A t - B t) / h - C t) := by
          symm
          simpa using circleIntegral.integral_sub hABdiv hC

/-- Helper for Cartan section06 0028_Exercise_13: the difference-quotient error equals one contour
integral with the textbook kernel on the intermediate circle. -/
private theorem difference_quotient_sub_deriv_eq_circle_integral_aux
    {f : ℂ → ℂ} {ρ r : ℝ} {z h : ℂ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ))
    (hz : z ∈ closedBall (0 : ℂ) r) (hh₀ : h ≠ 0)
    (hh : ‖h‖ < (ρ - r) / 4) :
    (f (z + h) - f z) / h - deriv f z =
      h * ((((2 * Real.pi : ℂ) * I)⁻¹) *
        ∮ t in C(0, (ρ + r) / 2), f t / ((t - z - h) * (t - z) ^ 2)) := by
  -- Route correction: use the arbitrary-point derivative Cauchy formula from mathlib for the
  -- `∮ f(t) / (t - z)^2` term, then normalize the separated contour terms through one dedicated
  -- circle-integral linearity lemma before applying the pointwise kernel identity.
  let R : ℝ := (ρ + r) / 2
  let K : ℂ := (((2 * Real.pi : ℂ) * I)⁻¹)
  let hfmid := diffContOnCl_intermediate_ball hrρ hf
  let A : ℂ → ℂ := fun t ↦ f t / (t - (z + h))
  let B : ℂ → ℂ := fun t ↦ f t / (t - z)
  let C : ℂ → ℂ := fun t ↦ f t / (t - z) ^ 2
  let G : ℂ → ℂ := fun t ↦ f t / ((t - z - h) * (t - z) ^ 2)
  have hz_norm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg z) hz_norm
  have hR0 : 0 < R := by
    dsimp [R]
    linarith
  have hz_mid : z ∈ ball (0 : ℂ) R := by
    have hz_lt_R : ‖z‖ < R := lt_of_le_of_lt hz_norm (by
      dsimp [R]
      linarith)
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz_lt_R
  have hzh_mid : z + h ∈ ball (0 : ℂ) R := by
    have hnorm_add : ‖z + h‖ ≤ ‖z‖ + ‖h‖ := norm_add_le z h
    have hzh_lt_R : ‖z + h‖ < R := lt_of_le_of_lt hnorm_add (by
      dsimp [R]
      linarith [hz_norm, hh])
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hzh_lt_R
  have hclosed_sub : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) ρ := by
    refine closedBall_subset_ball ?_
    dsimp [R]
    linarith
  obtain ⟨hAint, hBint, hCint⟩ :=
    cauchyDifferenceQuotientTerms_circleIntegrable hR0 hfmid.continuousOn_ball hz_mid hzh_mid
  have hvalue_zh :
      K * (∮ t in C(0, R), A t) = f (z + h) := by
    -- Evaluate the first contour term by the usual Cauchy integral formula at `z + h`.
    simpa [A, K, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hfmid.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzh_mid
  have hvalue_z :
      K * (∮ t in C(0, R), B t) = f z := by
    -- Evaluate the second contour term by the same Cauchy formula at `z`.
    simpa [B, K, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hfmid.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz_mid
  have hderiv :
      K * (∮ t in C(0, R), C t) = deriv f z := by
    -- The arbitrary-point derivative Cauchy formula matches the fixed circle centered at `0`.
    simpa [C, K, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
        isOpen_ball hclosed_sub hf hz_mid
  -- Replace the value and derivative terms by contour integrals on the common intermediate circle.
  calc
    (f (z + h) - f z) / h - deriv f z
        = K * (((∮ t in C(0, R), A t) - ∮ t in C(0, R), B t) / h - ∮ t in C(0, R), C t) := by
            rw [← hvalue_zh, ← hvalue_z, ← hderiv]
            ring
    _ = K * ∮ t in C(0, R), ((A t - B t) / h - C t) := by
          rw [differenceQuotientCircleIntegralLinearization hR0.le hAint hBint hCint]
    _ = K * ∮ t in C(0, R), h * G t := by
          congr 1
          refine circleIntegral.integral_congr hR0.le ?_
          intro t ht
          have htz : t ≠ z := Metric.sphere_disjoint_ball.ne_of_mem ht hz_mid
          have htzh : t ≠ z + h := Metric.sphere_disjoint_ball.ne_of_mem ht hzh_mid
          simpa [A, B, C, G, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
            differenceQuotientIntegrand_identity (a := f t) (z := z) (h := h) (t := t) hh₀ htz htzh
    _ = h * (K * ∮ t in C(0, R), G t) := by
          rw [circleIntegral.integral_const_mul]
          ring
    _ = h * ((((2 * Real.pi : ℂ) * I)⁻¹) *
          ∮ t in C(0, (ρ + r) / 2), f t / ((t - z - h) * (t - z) ^ 2)) := by
            rfl

/-- Helper for Cartan section06 0028_Exercise_13: a boundary supremum on the intermediate circle
gives a uniform linear `O(‖h‖)` bound for the difference-quotient error. -/
private theorem norm_difference_quotient_sub_deriv_le_of_boundary_bound_aux
    {f : ℂ → ℂ} {ρ r M : ℝ} {z h : ℂ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ))
    (hz : z ∈ closedBall (0 : ℂ) r) (hh₀ : h ≠ 0)
    (hh : ‖h‖ < (ρ - r) / 4)
    (hM : ∀ t ∈ sphere (0 : ℂ) ((ρ + r) / 2), ‖f t‖ ≤ M) :
    ‖(f (z + h) - f z) / h - deriv f z‖ ≤
      8 * M * (ρ + r) / (ρ - r) ^ 3 * ‖h‖ := by
  have hz_norm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg z) hz_norm
  have hmid₀ : 0 < (ρ + r) / 2 := by
    linarith
  have hM_nonneg : 0 ≤ M := by
    let R : ℝ := (ρ + r) / 2
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      linarith
    have hmem : ((R : ℂ)) ∈ sphere (0 : ℂ) R := by
      simp [Complex.norm_real, abs_of_nonneg hR_nonneg]
    have hbound := hM (R : ℂ) (by simpa [R] using hmem)
    have hnorm_nonneg : 0 ≤ ‖f (R : ℂ)‖ := norm_nonneg _
    linarith
  have hnorm_kernel :
      ‖((((2 * Real.pi : ℂ) * I)⁻¹) *
          ∮ t in C(0, (ρ + r) / 2), f t / ((t - z - h) * (t - z) ^ 2))‖ ≤
        ((ρ + r) / 2) * (16 * M / (ρ - r) ^ 3) := by
    refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hmid₀.le ?_
    intro t ht
    exact differenceQuotientIntegrand_bound hrρ hz hh hM ht
  -- Combine the contour representation with the uniform bound on the intermediate circle.
  calc
    ‖(f (z + h) - f z) / h - deriv f z‖ =
        ‖h * ((((2 * Real.pi : ℂ) * I)⁻¹) *
          ∮ t in C(0, (ρ + r) / 2), f t / ((t - z - h) * (t - z) ^ 2))‖ := by
      rw [difference_quotient_sub_deriv_eq_circle_integral_aux hrρ hf hz hh₀ hh]
    _ = ‖h‖ *
          ‖((((2 * Real.pi : ℂ) * I)⁻¹) *
            ∮ t in C(0, (ρ + r) / 2), f t / ((t - z - h) * (t - z) ^ 2))‖ := by
      rw [norm_mul]
    _ ≤ ‖h‖ * (((ρ + r) / 2) * (16 * M / (ρ - r) ^ 3)) := by
      gcongr
    _ = 8 * M * (ρ + r) / (ρ - r) ^ 3 * ‖h‖ := by
      ring

/-- Cartan section06 0028_Exercise_13: Exercise 13 shows that for a holomorphic function on the
open disc `|z| < ρ`, the difference quotients
converge uniformly to `deriv f` on the closed disc `|z| ≤ r` as `h → 0` through the punctured
neighborhood filter `𝓝[≠] (0 : ℂ)`. -/
-- Proof sketch: use the circle-integral identity for the error term on the intermediate circle
-- of radius `(ρ + r) / 2`, then combine the resulting uniform `O(‖h‖)` estimate on the closed
-- ball `closedBall 0 r` with `Metric.tendstoUniformlyOn_iff`; the small-ball restriction on `h`
-- is automatic because `r < ρ`.
theorem difference_quotients_tendsto_uniformly_on_deriv_closed_ball
    {f : ℂ → ℂ} {ρ r : ℝ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ)) :
    TendstoUniformlyOn
      (fun h z ↦ (f (z + h) - f z) / h)
      (deriv f)
      (𝓝[≠] (0 : ℂ))
      (closedBall (0 : ℂ) r) := by
  by_cases hr : 0 ≤ r
  · let R : ℝ := (ρ + r) / 2
    let hfmid := diffContOnCl_intermediate_ball hrρ hf
    have hR0 : 0 < R := by
      dsimp [R]
      linarith
    have hcontSphere : ContinuousOn f (sphere (0 : ℂ) R) := by
      exact hfmid.continuousOn_ball.mono sphere_subset_closedBall
    have hsphere_nonempty : (sphere (0 : ℂ) R).Nonempty := by
      refine ⟨(R : ℂ), ?_⟩
      simp [Complex.norm_real, abs_of_nonneg hR0.le]
    obtain ⟨w, hw, hwmax⟩ :=
      (isCompact_sphere (0 : ℂ) R).exists_isMaxOn hsphere_nonempty hcontSphere.norm
    let M : ℝ := ‖f w‖
    have hM : ∀ t ∈ sphere (0 : ℂ) R, ‖f t‖ ≤ M := by
      intro t ht
      exact (isMaxOn_iff.mp hwmax) t ht
    let K : ℝ := 8 * M * (ρ + r) / (ρ - r) ^ 3
    have hK_nonneg : 0 ≤ K := by
      have hρr_nonneg : 0 ≤ ρ + r := by
        linarith [hR0]
      have hM_nonneg : 0 ≤ M := by
        dsimp [M]
        exact norm_nonneg _
      have hpow_nonneg : 0 ≤ (ρ - r) ^ 3 := by
        positivity
      dsimp [K]
      exact div_nonneg (by nlinarith) hpow_nonneg
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let δ : ℝ := min ((ρ - r) / 4) (ε / (K + 1))
    have hδpos : 0 < δ := by
      dsimp [δ]
      have hrr : 0 < (ρ - r) / 4 := by
        linarith
      have hK1 : 0 < K + 1 := by
        linarith
      have hεdiv : 0 < ε / (K + 1) := by
        exact div_pos hε hK1
      exact lt_min hrr hεdiv
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
    refine ⟨ball (0 : ℂ) δ, Metric.ball_mem_nhds (0 : ℂ) hδpos, ?_⟩
    intro h hhmem z hz
    have hhδ : ‖h‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm, δ] using hhmem.1
    have hh₀ : h ≠ 0 := by
      simpa using hhmem.2
    have hhsmall : ‖h‖ < (ρ - r) / 4 := lt_of_lt_of_le hhδ (min_le_left _ _)
    have hbound :
        ‖(f (z + h) - f z) / h - deriv f z‖ ≤ K * ‖h‖ := by
      have hbound' :=
        norm_difference_quotient_sub_deriv_le_of_boundary_bound_aux
          hrρ hf hz hh₀ hhsmall (fun t ht => by simpa [R] using hM t ht)
      dsimp [K, M] at hbound' ⊢
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbound'
    have hhdiv : ‖h‖ < ε / (K + 1) := lt_of_lt_of_le hhδ (min_le_right _ _)
    have hK1 : 0 < K + 1 := by
      linarith
    have hmul : (K + 1) * ‖h‖ < ε := by
      have htmp := mul_lt_mul_of_pos_left hhdiv hK1
      have hcancel : (K + 1) * (ε / (K + 1)) = ε := by
        field_simp [hK1.ne']
      simpa [hcancel] using htmp
    have hlt : K * ‖h‖ < ε := by
      have hle : K * ‖h‖ ≤ (K + 1) * ‖h‖ := by
        nlinarith [hK_nonneg, norm_nonneg h]
      exact lt_of_le_of_lt hle hmul
    have hnorm : ‖(f (z + h) - f z) / h - deriv f z‖ < ε := lt_of_le_of_lt hbound hlt
    -- Convert the norm estimate into the metric-form statement required by
    -- `Metric.tendstoUniformlyOn_iff`.
    simpa [dist_eq_norm, norm_sub_rev] using hnorm
  · have hempty : closedBall (0 : ℂ) r = ∅ := Metric.closedBall_eq_empty.2 (lt_of_not_ge hr)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall fun _ _ hz => by
      simp [hempty] at hz

/-- On the smaller closed disc, the error in the difference quotient admits a Cauchy-integral
representation over the intermediate circle of radius `(ρ + r) / 2`. -/
-- Proof sketch: apply the Cauchy integral formula for `deriv f z` on the circle of radius
-- `(ρ + r) / 2` via `DiffContOnCl.deriv_eq_smul_circleIntegral`, apply
-- `DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul` to `f (· + h) - f`, and simplify
-- the resulting difference into a single integral kernel.
theorem difference_quotient_sub_deriv_eq_circle_integral
    {f : ℂ → ℂ} {ρ r : ℝ} {z h : ℂ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ))
    (hz : z ∈ closedBall (0 : ℂ) r) (hh₀ : h ≠ 0)
    (hh : ‖h‖ < (ρ - r) / 4) :
    (f (z + h) - f z) / h - deriv f z =
      h * ((((2 * Real.pi : ℂ) * I)⁻¹) *
        ∮ t in C(0, (ρ + r) / 2), f t / ((t - z - h) * (t - z) ^ 2)) := by
  -- Reuse the stabilized contour-identity helper rather than replaying the circle-algebra.
  exact difference_quotient_sub_deriv_eq_circle_integral_aux hrρ hf hz hh₀ hh

/-- Any uniform boundary bound on the intermediate circle gives the linear error estimate for the
difference quotient on the smaller closed disc. -/
-- Proof sketch: take norms in the circle-integral formula for the error term, bound `‖f t‖`
-- on the circle by `M`, estimate the kernel using `‖z‖ ≤ r` and `‖h‖ < (ρ - r) / 4`, and
-- bound the circle integral by the length of the circle times the supremum norm of the integrand,
-- after reducing the Cauchy-integral step to the canonical intermediate-disc owner
-- `diffContOnCl_intermediate_ball hrρ hf`.
theorem norm_difference_quotient_sub_deriv_le_of_boundary_bound
    {f : ℂ → ℂ} {ρ r M : ℝ} {z h : ℂ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ))
    (hz : z ∈ closedBall (0 : ℂ) r) (hh₀ : h ≠ 0)
    (hh : ‖h‖ < (ρ - r) / 4)
    (hM : ∀ t ∈ sphere (0 : ℂ) ((ρ + r) / 2), ‖f t‖ ≤ M) :
    ‖(f (z + h) - f z) / h - deriv f z‖ ≤
      8 * M * (ρ + r) / (ρ - r) ^ 3 * ‖h‖ := by
  -- Route correction: the direct intermediate-circle estimate naturally yields the coefficient
  -- `8`, and this linear bound is exactly what the uniform convergence theorem needs.
  exact norm_difference_quotient_sub_deriv_le_of_boundary_bound_aux hrρ hf hz hh₀ hh hM
