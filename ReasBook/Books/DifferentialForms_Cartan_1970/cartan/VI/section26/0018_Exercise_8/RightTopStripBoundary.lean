import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».InnerStripBoundary

open Set
open scoped UpperHalfPlane ComplexOrder

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: when a complex number lies in the open upper
half-plane, taking the principal square root after multiplying by `-1` is the same as
multiplying the original principal square root by `-I`. This is the branch-cut normalization
used on the right and top boundary slices. -/
lemma exercise8_sqrt_neg_eq_negI_sqrt_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.sqrt (-w) = -Complex.I * Complex.sqrt w := by
  -- Expand both principal square roots into their explicit real/imaginary normal forms.
  rw [Complex.sqrt_eq_real_add_ite, Complex.sqrt_eq_real_add_ite]
  have hnot : ¬ w.im ≤ 0 := not_le_of_gt hw
  have hpos : 0 ≤ w.im := le_of_lt hw
  simp [hnot, hpos, mul_add]
  let A : ℂ := ↑√(‖w‖ - w.re) / ↑√2
  let B : ℂ := ↑√(‖w‖ + w.re) / ↑√2
  have hdoubleI : -(Complex.I * (Complex.I * A)) = A := by
    -- Two factors of `I` contribute `-1`, and the outer minus sign cancels it.
    calc
      -(Complex.I * (Complex.I * A)) = -(Complex.I * Complex.I * A) := by
        ring
      _ = -((-1 : ℂ) * A) := by
        simp
      _ = A := by
        ring
  calc
    A + -(B * Complex.I) = A + -(Complex.I * B) := by
      rw [mul_comm]
    _ = -(Complex.I * B) + -(Complex.I * (A * Complex.I)) := by
      rw [show -(Complex.I * (A * Complex.I)) = A by
        calc
          -(Complex.I * (A * Complex.I)) = -(Complex.I * (Complex.I * A)) := by
            ring
          _ = A := hdoubleI]
      ring
    _ = -(Complex.I * (↑√(‖w‖ + w.re) / ↑√2)) +
          -(Complex.I * (↑√(‖w‖ - w.re) / ↑√2 * Complex.I)) := by
      simp [A, B]

/-- Helper for Cartan section26 0018_Exercise_8: on the right boundary slices, the translated
square term `z^2 - 1` lies in the open upper half-plane. This is the sign input for rewriting the
first principal square-root factor through `-I`. -/
lemma exercise8_square_sub_one_im_pos_on_right {t y : ℝ} (ht : 1 < t) (hy : 0 < y) :
    0 < ((((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ) - 1).im) := by
  simp [pow_two]
  nlinarith [ht, hy]

/-- Helper for Cartan section26 0018_Exercise_8: on every horizontal slice with real coordinate
strictly larger than `1`, the norm of `z^2 - 1` is bounded below by the positive real-axis value
`t^2 - 1`. This is the lower bound reused in the reciprocal top-edge majorant. -/
lemma exercise8_square_sub_one_norm_lower_on_right
    {t y : ℝ} (ht : 1 < t) (hy : 0 < y) :
    t ^ (2 : ℕ) - 1 ≤ ‖(((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ) - 1)‖ := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hfactor_nonneg : 0 ≤ t ^ (2 : ℕ) - 1 := by
    nlinarith [ht]
  have hsq :
      (t ^ (2 : ℕ) - 1) ^ (2 : ℕ) ≤
        Complex.normSq ((z ^ (2 : ℕ)) - 1) := by
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

/-- Helper for Cartan section26 0018_Exercise_8: on the reciprocal top-edge slices, the second
negative radicand factor `k² z² - 1` also lies in the open upper half-plane. -/
lemma exercise8_kSqSquare_sub_one_im_pos_on_top
    (k : Exercise8Modulus) {t y : ℝ} (ht : 1 / (k : ℝ) < t) (hy : 0 < y) :
    0 < ((((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) - 1).im) := by
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have hkt : 1 < (k : ℝ) * t := by
    have hmul := mul_lt_mul_of_pos_left ht hk_pos
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    rw [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp [hk_ne]] at hmul
    exact hmul
  have hscaled :=
    exercise8_square_sub_one_im_pos_on_right (t := (k : ℝ) * t) (y := (k : ℝ) * y) hkt
      (mul_pos hk_pos hy)
  simpa [pow_two, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Cartan section26 0018_Exercise_8: after the reciprocal substitution
`t = 1 / (k s)`, this fixed-interval slice owner records the top-edge tail on `s ∈ [0, 1]`. -/
def exercise8_topReciprocalSlice (k : Exercise8Modulus) (s y : ℝ) : ℂ :=
  (((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ) *
    exercise8_integrand k (((1 / ((k : ℝ) * s)) : ℂ) + (y : ℂ) * Complex.I)

/-- Helper for Cartan section26 0018_Exercise_8: this is the stabilized branch-normal form for
the reciprocal top-edge slice, with both negative real-axis factors rewritten through the positive
square roots of `z^2 - 1` and `k^2 z^2 - 1`. -/
def exercise8_topReciprocalBranchProduct (k : Exercise8Modulus) (s y : ℝ) : ℂ :=
  let z : ℂ := (((1 / ((k : ℝ) * s)) : ℂ) + (y : ℂ) * Complex.I)
  (-1 : ℂ) * Complex.sqrt (z ^ (2 : ℕ) - 1) *
    Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)

/-- Helper for Cartan section26 0018_Exercise_8: the reciprocal parameter `t = 1 / (k s)` lies
strictly to the right of the shared top-right vertex whenever `s ∈ (0, 1)`. -/
lemma exercise8_topReciprocalParameter_gt_invK
    (k : Exercise8Modulus) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    1 / (k : ℝ) < 1 / ((k : ℝ) * s) := by
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have hks_pos : 0 < (k : ℝ) * s := mul_pos hk_pos hs.1
  have hks_lt_k : (k : ℝ) * s < (k : ℝ) := by
    simpa using mul_lt_mul_of_pos_left hs.2 hk_pos
  have hrecip : ((k : ℝ))⁻¹ < ((k : ℝ) * s)⁻¹ := by
    exact (inv_lt_inv₀ hk_pos hks_pos).2 hks_lt_k
  simpa [one_div] using hrecip

/-- Helper for Cartan section26 0018_Exercise_8: the reciprocal parameter
`s ↦ 1 / (k s)` already lies to the right of `1` on the whole interval `(0, 1)`. -/
lemma exercise8_topReciprocalParameter_gt_one
    (k : Exercise8Modulus) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    1 < 1 / ((k : ℝ) * s) := by
  have hk_inv_ge_one : 1 ≤ 1 / (k : ℝ) := by
    exact (one_le_div (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k).le
  exact lt_of_le_of_lt hk_inv_ge_one (exercise8_topReciprocalParameter_gt_invK k hs)

/-- Helper for Cartan section26 0018_Exercise_8: the reciprocal parameter
`s ↦ 1 / (k s)` has the expected derivative on the positive real axis. -/
lemma exercise8_topReciprocalParameter_hasDerivAt
    (k : Exercise8Modulus) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s : ℝ ↦ 1 / ((k : ℝ) * s)) (-1 / ((k : ℝ) * s ^ (2 : ℕ))) s := by
  -- Rewrite the reciprocal parameter as `(1 / k) * s⁻¹`, then differentiate `s ↦ s⁻¹`.
  simpa [one_div, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using
    ((hasDerivAt_inv hs.ne').const_mul (1 / (k : ℝ)))

/-- Helper for Cartan section26 0018_Exercise_8: for fixed positive height `y`, the reciprocal
top-edge slice is continuous in the reciprocal parameter away from the singular endpoint `s = 0`.
This is the continuity input for freezing the moving cutoff on `[0, 1]`. -/
lemma exercise8_topReciprocalSlice_continuousOn_pos
    (k : Exercise8Modulus) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun s : ℝ ↦ exercise8_topReciprocalSlice k s y) (Set.Ioi 0) := by
  have hscalar_real :
      ContinuousOn (fun s : ℝ ↦ 1 / ((k : ℝ) * s ^ (2 : ℕ))) (Set.Ioi 0) := by
    have hden :
        ContinuousOn (fun s : ℝ ↦ (k : ℝ) * s ^ (2 : ℕ)) (Set.Ioi (0 : ℝ)) := by
      fun_prop
    have hden_ne : ∀ s ∈ Set.Ioi (0 : ℝ), (k : ℝ) * s ^ (2 : ℕ) ≠ 0 := by
      intro s hs
      exact mul_ne_zero (Exercise8Modulus.pos k).ne' (pow_ne_zero _ hs.ne')
    simpa [one_div] using ContinuousOn.inv₀ hden hden_ne
  have hscalar :
      ContinuousOn
        (fun s : ℝ ↦ (((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ))
        (Set.Ioi 0) := by
    simpa using Complex.continuous_ofReal.comp_continuousOn' hscalar_real
  have hrecip_real :
      ContinuousOn (fun s : ℝ ↦ 1 / ((k : ℝ) * s)) (Set.Ioi 0) := by
    have hden :
        ContinuousOn (fun s : ℝ ↦ (k : ℝ) * s) (Set.Ioi (0 : ℝ)) := by
      fun_prop
    have hden_ne : ∀ s ∈ Set.Ioi (0 : ℝ), (k : ℝ) * s ≠ 0 := by
      intro s hs
      exact mul_ne_zero (Exercise8Modulus.pos k).ne' hs.ne'
    simpa [one_div] using ContinuousOn.inv₀ hden hden_ne
  have hrecip :
      ContinuousOn (fun s : ℝ ↦ (((1 / ((k : ℝ) * s)) : ℝ) : ℂ)) (Set.Ioi 0) := by
    simpa using Complex.continuous_ofReal.comp_continuousOn' hrecip_real
  have hpath :
      ContinuousOn
        (fun s : ℝ ↦ (((1 / ((k : ℝ) * s)) : ℂ) + (y : ℂ) * Complex.I))
        (Set.Ioi 0) := by
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hrecip.add continuousOn_const
  have hintegrand :
      ContinuousOn
        (fun s : ℝ ↦
          exercise8_integrand k (((1 / ((k : ℝ) * s)) : ℂ) + (y : ℂ) * Complex.I))
        (Set.Ioi 0) := by
    refine (exercise8_integrand_continuousOn_upper k).comp hpath ?_
    intro s hs
    simpa using hy
  -- The reciprocal slice is the product of the scalar Jacobian and the transported integrand.
  simpa [exercise8_topReciprocalSlice] using hscalar.mul hintegrand

/-- Helper for Cartan section26 0018_Exercise_8: on a reciprocal top-edge slice, the transported
integrand is the reciprocal Jacobian times the inverse of the stabilized branch product. -/
lemma exercise8_topReciprocalSlice_eq_scalar_mul_branchInverse
    (k : Exercise8Modulus) {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : 0 < y) :
    exercise8_topReciprocalSlice k s y =
      ((((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ)) *
        (exercise8_topReciprocalBranchProduct k s y)⁻¹ := by
  let z : ℂ := (((1 / ((k : ℝ) * s)) : ℂ) + (y : ℂ) * Complex.I)
  have hz_im : 0 < z.im := by
    simpa [z] using hy
  have ht : 1 < 1 / ((k : ℝ) * s) :=
    exercise8_topReciprocalParameter_gt_one k hs
  have hleft_im : 0 < ((z ^ (2 : ℕ) - 1).im) := by
    simpa [z] using
      exercise8_square_sub_one_im_pos_on_right (t := 1 / ((k : ℝ) * s)) (y := y) ht hy
  have hright_im : 0 < ((((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1).im) := by
    simpa [z] using
      exercise8_kSqSquare_sub_one_im_pos_on_top k
        (t := 1 / ((k : ℝ) * s)) (y := y)
        (exercise8_topReciprocalParameter_gt_invK k hs) hy
  have hneg_left : (1 : ℂ) - z ^ (2 : ℕ) = -(z ^ (2 : ℕ) - 1) := by
    ring
  have hneg_right :
      (1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) =
        -(((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1) := by
    ring
  let a : ℂ := Complex.sqrt (z ^ (2 : ℕ) - 1)
  let b : ℂ := Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)
  have hbranch : ((-Complex.I) * a) * ((-Complex.I) * b) = (-1 : ℂ) * a * b := by
    calc
      ((-Complex.I) * a) * ((-Complex.I) * b) = ((-Complex.I) * (-Complex.I)) * (a * b) := by
        ring
      _ = (-1 : ℂ) * (a * b) := by
        simp
      _ = (-1 : ℂ) * a * b := by
        ring
  -- Route correction: freeze the top-edge branch choice once, so later limits and bounds work
  -- with the stabilized owner `exercise8_topReciprocalBranchProduct`.
  rw [exercise8_topReciprocalSlice, exercise8_integrand,
    exercise8_simpleSqrtBranch_eq_principalFactorization_on_upper k hz_im,
    hneg_left, hneg_right,
    exercise8_sqrt_neg_eq_negI_sqrt_of_im_pos hleft_im,
    exercise8_sqrt_neg_eq_negI_sqrt_of_im_pos hright_im, hbranch]
  simp [exercise8_topReciprocalBranchProduct, z, a, b]

/-- Helper for Cartan section26 0018_Exercise_8: after the reciprocal substitution `t = 1 / (k s)`,
the Jacobian and the two positive boundary square-root factors collapse exactly to the real kernel
on the bottom edge. -/
lemma exercise8_real_kernel_eq_topReciprocalLimitFactors
    (k : Exercise8Modulus) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    exercise8_real_kernel k s =
      (1 / ((k : ℝ) * s ^ (2 : ℕ))) *
        (Real.sqrt (((1 / ((k : ℝ) * s)) ^ (2 : ℕ)) - 1) *
          Real.sqrt (((1 / s) ^ (2 : ℕ)) - 1))⁻¹ := by
  have hs_mem : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have hks_pos : 0 < (k : ℝ) * s := mul_pos hk_pos hs.1
  have hs_sq_nonneg : 0 ≤ 1 - s ^ (2 : ℕ) := by
    nlinarith [hs.1, hs.2]
  have hks_sq_nonneg : 0 ≤ 1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ) := by
    nlinarith [Exercise8Modulus.pos k, Exercise8Modulus.lt_one k, hs.1, hs.2]
  have hsqrt_right :
      Real.sqrt (((1 / s) ^ (2 : ℕ)) - 1) =
        s⁻¹ * Real.sqrt (1 - s ^ (2 : ℕ)) := by
    have hrewrite :
        ((1 / s) ^ (2 : ℕ)) - 1 = (s⁻¹) ^ (2 : ℕ) * (1 - s ^ (2 : ℕ)) := by
      field_simp [hs.1.ne']
    calc
      Real.sqrt (((1 / s) ^ (2 : ℕ)) - 1) =
          Real.sqrt ((s⁻¹) ^ (2 : ℕ) * (1 - s ^ (2 : ℕ))) := by
            rw [hrewrite]
      _ = Real.sqrt (1 - s ^ (2 : ℕ)) * Real.sqrt ((s⁻¹) ^ (2 : ℕ)) := by
            rw [mul_comm, Real.sqrt_mul hs_sq_nonneg]
      _ = Real.sqrt ((s⁻¹) ^ (2 : ℕ)) * Real.sqrt (1 - s ^ (2 : ℕ)) := by
            ring
      _ = |s⁻¹| * Real.sqrt (1 - s ^ (2 : ℕ)) := by
            rw [Real.sqrt_sq_eq_abs]
      _ = s⁻¹ * Real.sqrt (1 - s ^ (2 : ℕ)) := by
            rw [abs_of_pos (inv_pos.2 hs.1)]
  have hsqrt_left :
      Real.sqrt (((1 / ((k : ℝ) * s)) ^ (2 : ℕ)) - 1) =
        ((k : ℝ) * s)⁻¹ * Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ)) := by
    have hrewrite :
        ((1 / ((k : ℝ) * s)) ^ (2 : ℕ)) - 1 =
          (((k : ℝ) * s)⁻¹) ^ (2 : ℕ) * (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ)) := by
      field_simp [hk_pos.ne', hs.1.ne']
    calc
      Real.sqrt (((1 / ((k : ℝ) * s)) ^ (2 : ℕ)) - 1) =
          Real.sqrt ((((k : ℝ) * s)⁻¹ ^ (2 : ℕ)) *
            (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ))) := by
              rw [hrewrite]
      _ = Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ)) *
            Real.sqrt ((((k : ℝ) * s)⁻¹) ^ (2 : ℕ)) := by
              rw [mul_comm, Real.sqrt_mul hks_sq_nonneg]
      _ = Real.sqrt ((((k : ℝ) * s)⁻¹) ^ (2 : ℕ)) *
            Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ)) := by
              ring
      _ = |((k : ℝ) * s)⁻¹| * Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ)) := by
            rw [Real.sqrt_sq_eq_abs]
      _ = ((k : ℝ) * s)⁻¹ * Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ)) := by
            rw [abs_of_pos (inv_pos.2 hks_pos)]
  have hleft_ne :
      Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ)) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by
      nlinarith [Exercise8Modulus.pos k, Exercise8Modulus.lt_one k, hs.1, hs.2])
  have hright_ne : Real.sqrt (1 - s ^ (2 : ℕ)) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by
      nlinarith [hs.1, hs.2])
  -- Rewrite the kernel through the factored bottom-edge form, then cancel the reciprocal
  -- Jacobian against the two explicit boundary square-root factors.
  rw [exercise8_real_kernel, exercise8_real_kernel_eq_factored hs_mem, hsqrt_left, hsqrt_right]
  field_simp [hk_pos.ne', hs.1.ne', hleft_ne, hright_ne]

/-- Helper for Cartan section26 0018_Exercise_8: for every fixed reciprocal parameter
`s ∈ (0, 1)`, the transported top-edge slice tends to the negative real boundary kernel as the
height goes to `0+`. -/
lemma exercise8_topReciprocalSlice_tendsto_negRealKernel
    (k : Exercise8Modulus) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Filter.Tendsto (fun y : ℝ ↦ exercise8_topReciprocalSlice k s y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(((exercise8_real_kernel k s : ℝ) : ℂ)))) := by
  let t : ℝ := 1 / ((k : ℝ) * s)
  let leftFactor : ℝ → ℂ := fun y ↦ Complex.sqrt ((((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) - 1)
  let rightFactor : ℝ → ℂ := fun y ↦
    Complex.sqrt ((((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ))) - 1)
  let branchProduct : ℝ → ℂ := fun y ↦ (-1 : ℂ) * leftFactor y * rightFactor y
  let limitBranch : ℂ :=
    (-1 : ℂ) * (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) *
      (((Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) : ℝ) : ℂ))
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have hks_pos : 0 < (k : ℝ) * s := mul_pos hk_pos hs.1
  have ht : 1 < t := by
    simpa [t] using exercise8_topReciprocalParameter_gt_one k hs
  have hs_inv_gt_one : 1 < 1 / s := by
    simpa [one_div] using (one_lt_inv₀ hs.1).2 hs.2
  have hleft_pos : 0 < t ^ (2 : ℕ) - 1 := by
    nlinarith [ht]
  have hright_pos : 0 < (1 / s) ^ (2 : ℕ) - 1 := by
    nlinarith [hs_inv_gt_one]
  have hleft_tendsto :
      Filter.Tendsto leftFactor (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)))) := by
    have hrad_tendsto :
        Filter.Tendsto
          (fun y : ℝ ↦ (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)) - 1)
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
            nlinarith [ht])) :
          ContinuousAt Complex.sqrt (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)))
    have hsqrt_raw := hsqrt_cont.tendsto.comp hrad_tendsto
    have htarget :
        Complex.sqrt (((t ^ (2 : ℕ) - 1 : ℝ) : ℂ)) =
          (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) := by
      have hnonnegR : 0 ≤ t ^ (2 : ℕ) - 1 := le_of_lt hleft_pos
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
        (nhds ((((Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) : ℝ) : ℂ)))) := by
    have hrad_tendsto :
        Filter.Tendsto
          (fun y : ℝ ↦
            (((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ))) - 1)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((((1 / s) ^ (2 : ℕ) - 1 : ℝ) : ℂ))) := by
      have hslice :
          ContinuousAt
            (fun y : ℝ ↦
              (((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ))) - 1) 0 := by
        have hpath : Continuous fun y : ℝ ↦ (t : ℂ) + (y : ℂ) * Complex.I := by
          exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        exact (continuous_const.mul (hpath.pow 2)).sub continuous_const |>.continuousAt
      have hraw :
          Filter.Tendsto
            (fun y : ℝ ↦
              (((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ))) - 1)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds ((((k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) - 1 : ℝ) : ℂ))) := by
        simpa [pow_two] using hslice.continuousWithinAt.tendsto
      have htarget :
          (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) - 1 = (1 / s) ^ (2 : ℕ) - 1 := by
        dsimp [t]
        field_simp [hk_pos.ne', hs.1.ne']
      exact htarget ▸ hraw
    have hsqrt_cont :
        ContinuousAt Complex.sqrt ((((1 / s) ^ (2 : ℕ) - 1 : ℝ) : ℂ)) := by
      simpa using
        (Complex.continuousAt_sqrt (Or.inl
          (show (0 : ℝ) ≤ (((((1 / s) ^ (2 : ℕ) - 1 : ℝ) : ℂ)).re) by
            exact le_of_lt hright_pos)) :
          ContinuousAt Complex.sqrt ((((1 / s) ^ (2 : ℕ) - 1 : ℝ) : ℂ)))
    have hsqrt_raw := hsqrt_cont.tendsto.comp hrad_tendsto
    have htarget :
        Complex.sqrt ((((1 / s) ^ (2 : ℕ) - 1 : ℝ) : ℂ)) =
          (((Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) : ℝ) : ℂ)) := by
      have hnonnegR : 0 ≤ (1 / s) ^ (2 : ℕ) - 1 := le_of_lt hright_pos
      simpa [pow_two] using
        (Complex.sqrt_of_nonneg
          (show 0 ≤ ((((1 / s) ^ (2 : ℕ) - 1 : ℝ) : ℂ)) by
            exact_mod_cast hnonnegR))
    have hsqrt_raw' :
        Filter.Tendsto rightFactor (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Complex.sqrt ((((1 / s) ^ (2 : ℕ) - 1 : ℝ) : ℂ)))) := by
      simpa [rightFactor, Function.comp] using hsqrt_raw
    exact htarget ▸ hsqrt_raw'
  have hproduct_tendsto :
      Filter.Tendsto branchProduct (nhdsWithin 0 (Set.Ioi 0))
        (nhds limitBranch) := by
    have hmul :
        Filter.Tendsto
          (fun y : ℝ ↦ ((-1 : ℂ) * leftFactor y) * rightFactor y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds limitBranch) := by
      exact (tendsto_const_nhds.mul hleft_tendsto).mul hright_tendsto
    simpa [branchProduct, limitBranch, mul_assoc] using hmul
  have hleft_ne :
      (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 hleft_pos)
  have hright_ne :
      (((Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 hright_pos)
  have hproduct_ne :
      limitBranch ≠ 0 := by
    dsimp [limitBranch]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hleft_ne) hright_ne
  have hraw_tendsto :
      Filter.Tendsto (fun y : ℝ ↦ (branchProduct y)⁻¹) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (limitBranch⁻¹)) := by
    exact Filter.Tendsto.inv₀ hproduct_tendsto hproduct_ne
  have heq :
      (fun y : ℝ ↦ exercise8_topReciprocalSlice k s y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun y : ℝ ↦ ((((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ)) * (branchProduct y)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hbranch_eq : exercise8_topReciprocalBranchProduct k s y = branchProduct y := by
      simp [exercise8_topReciprocalBranchProduct, branchProduct, leftFactor, rightFactor, t,
        mul_assoc]
    rw [exercise8_topReciprocalSlice_eq_scalar_mul_branchInverse k hs hy, hbranch_eq]
  have hscalar_tendsto :
      Filter.Tendsto
        (fun y : ℝ ↦ ((((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ)) * (branchProduct y)⁻¹)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ)) * (limitBranch⁻¹))) := by
    have hconst :
        Filter.Tendsto
          (fun _ : ℝ ↦ (((1 / ((k : ℝ) * s ^ (2 : ℕ)) : ℝ) : ℂ)))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (((1 / ((k : ℝ) * s ^ (2 : ℕ)) : ℝ) : ℂ))) := tendsto_const_nhds
    exact hconst.mul hraw_tendsto
  have htarget :
      (((((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ)) * (limitBranch⁻¹)) =
        -(((exercise8_real_kernel k s : ℝ) : ℂ)) := by
    let a : ℂ := (((Real.sqrt (t ^ (2 : ℕ) - 1) : ℝ) : ℂ))
    let b : ℂ := (((Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) : ℝ) : ℂ))
    have ha : a ≠ 0 := by
      dsimp [a]
      exact_mod_cast (Real.sqrt_ne_zero'.2 hleft_pos)
    have hb : b ≠ 0 := by
      dsimp [b]
      exact_mod_cast (Real.sqrt_ne_zero'.2 hright_pos)
    have hInvNeg : (((-1 : ℂ) * a * b)⁻¹) = -((a * b)⁻¹) := by
      field_simp [ha, hb]
    have hkernel :
        (((exercise8_real_kernel k s : ℝ) : ℂ)) =
          (((1 / ((k : ℝ) * s ^ (2 : ℕ)) : ℝ) : ℂ)) * (a * b)⁻¹ := by
      dsimp [a, b]
      exact_mod_cast exercise8_real_kernel_eq_topReciprocalLimitFactors k hs
    -- Evaluate the reciprocal limit product explicitly before the final sign rewrite.
    calc
      (((((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ)) * (limitBranch⁻¹)) =
        (((1 / ((k : ℝ) * s ^ (2 : ℕ)) : ℝ) : ℂ)) * (((-1 : ℂ) * a * b)⁻¹) := by
          simp [a, b, limitBranch, mul_assoc]
      _ = (((1 / ((k : ℝ) * s ^ (2 : ℕ)) : ℝ) : ℂ)) * (-((a * b)⁻¹)) := by
          rw [hInvNeg]
      _ = -((((1 / ((k : ℝ) * s ^ (2 : ℕ)) : ℝ) : ℂ)) * (a * b)⁻¹) := by
          ring
      _ = -(((exercise8_real_kernel k s : ℝ) : ℂ)) := by
          rw [hkernel]
  -- The fixed-slice branch normalization now turns the top-edge boundary value into the negative
  -- bottom-edge kernel at the reciprocal source parameter.
  have hmain := Filter.Tendsto.congr' heq.symm hscalar_tendsto
  exact htarget ▸ hmain

/-- Helper for Cartan section26 0018_Exercise_8: each transported reciprocal top-edge slice is
dominated by the real boundary kernel on `(0, 1)`. This is the literal majorant used in the final
dominated-convergence step. -/
lemma exercise8_topReciprocalSlice_norm_le_realKernel
    (k : Exercise8Modulus) {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : 0 < y) :
    ‖exercise8_topReciprocalSlice k s y‖ ≤ exercise8_real_kernel k s := by
  let z : ℂ := (((1 / ((k : ℝ) * s)) : ℂ) + (y : ℂ) * Complex.I)
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have ht : 1 < 1 / ((k : ℝ) * s) := exercise8_topReciprocalParameter_gt_one k hs
  have hs_inv_gt_one : 1 < 1 / s := by
    simpa [one_div] using (one_lt_inv₀ hs.1).2 hs.2
  have hleft_pos : 0 < (1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1 := by
    nlinarith [ht]
  have hright_pos : 0 < (1 / s) ^ (2 : ℕ) - 1 := by
    nlinarith [hs_inv_gt_one]
  have hfactor1 :
      (1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1 ≤ ‖z ^ (2 : ℕ) - 1‖ := by
    simpa [z] using
      exercise8_square_sub_one_norm_lower_on_right
        (t := 1 / ((k : ℝ) * s)) (y := y) ht hy
  have hfactor2 :
      (1 / s) ^ (2 : ℕ) - 1 ≤ ‖((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1‖ := by
    have hscaled :=
      exercise8_square_sub_one_norm_lower_on_right
        (t := 1 / s) (y := (k : ℝ) * y) hs_inv_gt_one (mul_pos hk_pos hy)
    have hk_one_real : (k : ℝ) * (1 / ((k : ℝ) * s)) = 1 / s := by
      field_simp [hk_pos.ne', hs.1.ne']
    have hz_scaled :
        ((k : ℂ) * z) = (((1 / s : ℝ) : ℂ) + (((k : ℝ) * y : ℝ) : ℂ) * Complex.I) := by
      calc
        (k : ℂ) * z =
            (k : ℂ) * (((1 / ((k : ℝ) * s)) : ℂ) + (y : ℂ) * Complex.I) := by
              rfl
        _ = (k : ℂ) * (((1 / ((k : ℝ) * s)) : ℂ)) + (k : ℂ) * ((y : ℂ) * Complex.I) := by
              ring
        _ = (((1 / s : ℝ) : ℂ)) + (((k : ℝ) * y : ℝ) : ℂ) * Complex.I := by
              rw [show (k : ℂ) * (((1 / ((k : ℝ) * s)) : ℂ)) = (((1 / s : ℝ) : ℂ)) by
                exact_mod_cast hk_one_real]
              simp [mul_assoc, mul_left_comm, mul_comm]
    have hpow : (((k : ℂ) * z) ^ (2 : ℕ)) = ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) := by
      ring
    calc
      (1 / s) ^ (2 : ℕ) - 1 ≤
          ‖((((1 / s : ℝ) : ℂ) + (((k : ℝ) * y : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ) - 1)‖ := hscaled
      _ = ‖(((k : ℂ) * z) ^ (2 : ℕ) - 1)‖ := by rw [hz_scaled]
      _ = ‖((k : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - 1)‖ := by rw [hpow]
  have hleft_sq :
      ‖Complex.sqrt (z ^ (2 : ℕ) - 1)‖ ^ (2 : ℕ) = ‖z ^ (2 : ℕ) - 1‖ := by
    calc
      ‖Complex.sqrt (z ^ (2 : ℕ) - 1)‖ ^ (2 : ℕ) =
          ‖Complex.sqrt (z ^ (2 : ℕ) - 1) ^ (2 : ℕ)‖ := by
            simp [sq]
      _ = ‖z ^ (2 : ℕ) - 1‖ := by
            rw [sq_sqrt_complex]
  have hright_sq :
      ‖Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)‖ ^ (2 : ℕ) =
        ‖((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1‖ := by
    calc
      ‖Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)‖ ^ (2 : ℕ) =
          ‖Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1) ^ (2 : ℕ)‖ := by
            simp [sq]
      _ = ‖((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1‖ := by
            rw [sq_sqrt_complex]
  have hsqrt1 :
      Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) ≤ ‖Complex.sqrt (z ^ (2 : ℕ) - 1)‖ := by
    have hnonneg : 0 ≤ (1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1 := by
      nlinarith [ht]
    nlinarith [hfactor1, hleft_sq, hnonneg,
      norm_nonneg (Complex.sqrt (z ^ (2 : ℕ) - 1)), Real.sq_sqrt hnonneg]
  have hsqrt2 :
      Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) ≤
        ‖Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)‖ := by
    have hnonneg : 0 ≤ (1 / s) ^ (2 : ℕ) - 1 := by
      nlinarith [hs_inv_gt_one]
    nlinarith [hfactor2, hright_sq, hnonneg,
      norm_nonneg (Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)), Real.sq_sqrt hnonneg]
  have hbranch_lower :
      Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) * Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) ≤
        ‖exercise8_topReciprocalBranchProduct k s y‖ := by
    have hmul :
        Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) * Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) ≤
          ‖Complex.sqrt (z ^ (2 : ℕ) - 1)‖ *
            ‖Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)‖ := by
      exact mul_le_mul hsqrt1 hsqrt2
        (Real.sqrt_nonneg _)
        (norm_nonneg (Complex.sqrt (z ^ (2 : ℕ) - 1)))
    calc
      Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) * Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) ≤
          ‖Complex.sqrt (z ^ (2 : ℕ) - 1)‖ *
            ‖Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)‖ := hmul
      _ = ‖Complex.sqrt (z ^ (2 : ℕ) - 1) *
            Complex.sqrt (((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) - 1)‖ := by
            rw [norm_mul]
      _ = ‖exercise8_topReciprocalBranchProduct k s y‖ := by
            simp [exercise8_topReciprocalBranchProduct, z, mul_assoc]
  have hbranch_pos :
      0 < ‖exercise8_topReciprocalBranchProduct k s y‖ := by
    have hsqrt_prod_pos :
        0 <
          Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) *
            Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) := by
      apply mul_pos
      · exact Real.sqrt_pos.2 hleft_pos
      · exact Real.sqrt_pos.2 hright_pos
    exact lt_of_lt_of_le hsqrt_prod_pos hbranch_lower
  have hsqrt_prod_pos :
      0 <
        Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) *
          Real.sqrt ((1 / s) ^ (2 : ℕ) - 1) := by
    apply mul_pos
    · exact Real.sqrt_pos.2 hleft_pos
    · exact Real.sqrt_pos.2 hright_pos
  have hbound_inv :
      ‖exercise8_topReciprocalBranchProduct k s y‖⁻¹ ≤
        (Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) *
          Real.sqrt ((1 / s) ^ (2 : ℕ) - 1))⁻¹ := by
    exact (inv_le_inv₀ hbranch_pos hsqrt_prod_pos).2 hbranch_lower
  have hkernel_eq :
      exercise8_real_kernel k s =
        (1 / ((k : ℝ) * s ^ (2 : ℕ))) *
          (Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) *
            Real.sqrt ((1 / s) ^ (2 : ℕ) - 1))⁻¹ :=
    exercise8_real_kernel_eq_topReciprocalLimitFactors k hs
  -- The slice is a positive real scalar times the inverse stabilized branch product, so the
  -- kernel identity above converts the inverse norm bound into the exact real majorant.
  rw [exercise8_topReciprocalSlice_eq_scalar_mul_branchInverse k hs hy, norm_mul, norm_inv]
  have hscalar_eq :
      ‖((((1 / ((k : ℝ) * s ^ (2 : ℕ))) : ℝ) : ℂ))‖ = 1 / ((k : ℝ) * s ^ (2 : ℕ)) := by
    have hs_sq_pos : 0 < s ^ (2 : ℕ) := by
      nlinarith [hs.1]
    have hden_pos : 0 < (k : ℝ) * s ^ (2 : ℕ) := mul_pos (Exercise8Modulus.pos k) hs_sq_pos
    have hscalar_pos : 0 < 1 / ((k : ℝ) * s ^ (2 : ℕ)) := one_div_pos.2 hden_pos
    exact Complex.norm_of_nonneg hscalar_pos.le
  rw [hscalar_eq]
  have hfinal :
      (1 / ((k : ℝ) * s ^ (2 : ℕ))) * ‖exercise8_topReciprocalBranchProduct k s y‖⁻¹ ≤
        (1 / ((k : ℝ) * s ^ (2 : ℕ))) *
          (Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) *
            Real.sqrt ((1 / s) ^ (2 : ℕ) - 1))⁻¹ := by
    exact mul_le_mul_of_nonneg_left hbound_inv (by positivity)
  calc
    (1 / ((k : ℝ) * s ^ (2 : ℕ))) * ‖exercise8_topReciprocalBranchProduct k s y‖⁻¹ ≤
        (1 / ((k : ℝ) * s ^ (2 : ℕ))) *
          (Real.sqrt ((1 / ((k : ℝ) * s)) ^ (2 : ℕ) - 1) *
            Real.sqrt ((1 / s) ^ (2 : ℕ) - 1))⁻¹ := hfinal
    _ = exercise8_real_kernel k s := by
        exact hkernel_eq.symm

/-- Helper for Cartan section26 0018_Exercise_8: on the top strip, the direct horizontal interval
integral becomes the reciprocal fixed-cutoff model on `[0, 1]`. -/
lemma exercise8_topHorizontal_segment_eq_directIntervalIntegral
    (k : Exercise8Modulus) (w : ℂ) :
    ∫ᶜ z in Path.segment (((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I)
        ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ t in (1 / (k : ℝ))..w.re, exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) := by
  -- Freeze the top horizontal segment once in direct-interval form to avoid repeating the same
  -- endpoint coercion work inside the reciprocal-substitution theorem.
  convert exercise8_horizontal_segment_eq_directIntervalIntegral k (1 / (k : ℝ)) w.re w.im using 1
  apply congrArg
    (fun a : ℂ ↦
      ∫ᶜ z in Path.segment a ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z)
  simp [Complex.ofReal_inv]

/-- Helper for Cartan section26 0018_Exercise_8: on the top strip, the direct horizontal interval
integral becomes the reciprocal fixed-cutoff model on `[0, 1]`. -/
lemma exercise8_topDirectInterval_eq_reciprocalIndicatorIntegral
    (k : Exercise8Modulus) {w : ℂ}
    (hw : w ∈ {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}) :
    ∫ t in (1 / (k : ℝ))..w.re, exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) =
      ∫ s in (0 : ℝ)..1,
        if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0 := by
  let cutoff : ℝ := 1 / ((k : ℝ) * w.re)
  let g : ℝ → ℂ := fun t ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I)
  have hwim : 0 < w.im := hw.1
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have hwre_pos : 0 < w.re := lt_of_lt_of_le (one_div_pos.2 hk_pos) hw.2
  have hcutoff_pos : 0 < cutoff := by
    dsimp [cutoff]
    exact one_div_pos.2 (mul_pos hk_pos hwre_pos)
  have hcutoff_mem : cutoff ∈ Icc (0 : ℝ) 1 := by
    simpa [cutoff] using exercise8_top_branch_argument_mem_Icc (k := k) hw.2
  have hderiv :
      ∀ s ∈ Set.uIcc (1 : ℝ) cutoff,
        HasDerivAt (fun s : ℝ ↦ 1 / ((k : ℝ) * s)) (-1 / ((k : ℝ) * s ^ (2 : ℕ))) s := by
    intro s hs
    have hs' : s ∈ Set.Icc cutoff 1 := by
      rw [Set.uIcc_of_ge hcutoff_mem.2] at hs
      exact hs
    exact exercise8_topReciprocalParameter_hasDerivAt k
      (show 0 < s from lt_of_lt_of_le hcutoff_pos hs'.1)
  have hderiv_cont :
      ContinuousOn (fun s : ℝ ↦ -1 / ((k : ℝ) * s ^ (2 : ℕ))) (Set.uIcc (1 : ℝ) cutoff) := by
    have hpow : ContinuousOn (fun s : ℝ ↦ (k : ℝ) * s ^ (2 : ℕ)) (Set.uIcc (1 : ℝ) cutoff) := by
      fun_prop
    have hpow_ne :
        ∀ s ∈ Set.uIcc (1 : ℝ) cutoff, (k : ℝ) * s ^ (2 : ℕ) ≠ 0 := by
      intro s hs
      have hs' : s ∈ Set.Icc cutoff 1 := by
        rw [Set.uIcc_of_ge hcutoff_mem.2] at hs
        exact hs
      exact mul_ne_zero hk_pos.ne'
        (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hcutoff_pos hs'.1)))
    -- The derivative is the negative reciprocal of a positive continuous denominator.
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (ContinuousOn.inv₀ hpow hpow_ne).const_mul (-1 : ℝ)
  have hg : Continuous g := by
    have hcontOn :
        ContinuousOn (fun t : ℝ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I))
          Set.univ := by
      let hpath : ℝ → ℂ := fun t ↦ (t : ℂ) + (w.im : ℂ) * Complex.I
      have hhpath : Continuous hpath := by
        simpa [hpath] using Complex.continuous_ofReal.add continuous_const
      refine (exercise8_integrand_continuousOn_upper k).comp hhpath.continuousOn ?_
      intro t ht
      simpa [hpath] using hwim
    rw [← continuousOn_univ]
    simpa [g] using hcontOn
  have hsubstitution :
      ∫ s in (1 : ℝ)..cutoff,
          (-1 / ((k : ℝ) * s ^ (2 : ℕ))) •
            g (1 / ((k : ℝ) * s)) =
        ∫ t in (1 / (k : ℝ))..w.re, g t := by
    simpa [cutoff, g, hk_pos.ne', hwre_pos.ne', one_div, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using
      (intervalIntegral.integral_deriv_smul_comp
        (a := (1 : ℝ)) (b := cutoff)
        (f := fun s : ℝ ↦ 1 / ((k : ℝ) * s))
        (f' := fun s : ℝ ↦ -1 / ((k : ℝ) * s ^ (2 : ℕ)))
        (g := g) hderiv hderiv_cont hg)
  have hslice :
      (fun s : ℝ ↦
        (-1 / ((k : ℝ) * s ^ (2 : ℕ))) • g (1 / ((k : ℝ) * s))) =
      fun s : ℝ ↦ -exercise8_topReciprocalSlice k s w.im := by
    funext s
    simp [g, exercise8_topReciprocalSlice, smul_eq_mul, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
  have htail_indicator :
      (∫ s in (0 : ℝ)..1,
          if cutoff ≤ s then exercise8_topReciprocalSlice k s w.im else 0) =
        ∫ s in cutoff..(1 : ℝ), exercise8_topReciprocalSlice k s w.im := by
    have hone_sub_mem : 1 - cutoff ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hcutoff_mem.1, hcutoff_mem.2]
    calc
      (∫ s in (0 : ℝ)..1,
          if cutoff ≤ s then exercise8_topReciprocalSlice k s w.im else 0) =
        ∫ s in (0 : ℝ)..1,
          if s ≤ 1 - cutoff then exercise8_topReciprocalSlice k (1 - s) w.im else 0 := by
            symm
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (intervalIntegral.integral_comp_sub_left
                (f := fun s : ℝ ↦
                  if cutoff ≤ s then exercise8_topReciprocalSlice k s w.im else 0)
                (a := (0 : ℝ)) (b := 1) (d := 1))
      _ = ∫ s in (0 : ℝ)..(1 - cutoff), exercise8_topReciprocalSlice k (1 - s) w.im := by
            simpa [Set.indicator] using
              (intervalIntegral.integral_indicator
                (μ := MeasureTheory.volume)
                (f := fun s : ℝ ↦ exercise8_topReciprocalSlice k (1 - s) w.im)
                (a₁ := (0 : ℝ)) (a₂ := 1 - cutoff) (a₃ := (1 : ℝ))
                hone_sub_mem)
      _ = ∫ s in cutoff..(1 : ℝ), exercise8_topReciprocalSlice k s w.im := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (intervalIntegral.integral_comp_sub_left
                (f := fun s : ℝ ↦ exercise8_topReciprocalSlice k s w.im)
                (a := (0 : ℝ)) (b := 1 - cutoff) (d := 1))
  -- First isolate the reciprocal substitution on the direct interval, then freeze the lower
  -- endpoint as an indicator on the fixed interval `[0, 1]`.
  calc
    ∫ t in (1 / (k : ℝ))..w.re, exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) =
        ∫ s in (1 : ℝ)..cutoff, -exercise8_topReciprocalSlice k s w.im := by
          rw [← hsubstitution, hslice]
    _ = ∫ s in cutoff..(1 : ℝ), exercise8_topReciprocalSlice k s w.im := by
          rw [intervalIntegral.integral_symm]
          simp
    _ = ∫ s in (0 : ℝ)..1,
          if cutoff ≤ s then exercise8_topReciprocalSlice k s w.im else 0 := by
          exact htail_indicator.symm

/-- Helper for Cartan section26 0018_Exercise_8: the horizontal segment from `1 / k + i Im w` to
`w.re + i Im w` is exactly the reciprocal fixed-interval cutoff integral on `[0, 1]`. -/
lemma exercise8_topHorizontal_segment_eq_reciprocalIndicatorIntegral
    (k : Exercise8Modulus) {w : ℂ}
    (hw : w ∈ {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}) :
    ∫ᶜ z in Path.segment (((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I)
        ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ s in (0 : ℝ)..1,
        if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0 := by
  -- Route correction: the public top-edge normalization now only composes the segment/direct-
  -- interval adapter with the reciprocal-substitution theorem.
  calc
    ∫ᶜ z in Path.segment (((1 / (k : ℝ)) : ℂ) + (w.im : ℂ) * Complex.I)
        ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ t in (1 / (k : ℝ))..w.re, exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) := by
        simpa using exercise8_topHorizontal_segment_eq_directIntervalIntegral k w
    _ =
      ∫ s in (0 : ℝ)..1,
        if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0 := by
        exact exercise8_topDirectInterval_eq_reciprocalIndicatorIntegral k hw

/-- Helper for Cartan section26 0018_Exercise_8: the limiting cutoff integral of the negative real
kernel on `[0, 1]` always lies in the bottom-edge interval. This is the interval side condition
for the reciprocal-substitution top-edge package. -/
lemma exercise8_topHorizontal_cutoff_mem_Icc
    (k : Exercise8Modulus) {w : ℂ}
    (hw : w ∈ {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}) :
    1 / ((k : ℝ) * w.re) ∈ Icc (0 : ℝ) 1 := by
  -- The top-strip reciprocal parameter is exactly the boundary-trace argument `x ↦ 1 / (k x)`.
  exact exercise8_top_branch_argument_mem_Icc (k := k) hw.2

/-- Helper for Cartan section26 0018_Exercise_8: the limiting negative cutoff integral on
`[0, 1]` is exactly the top-edge branch increment after translating through the reciprocal
boundary parameter. -/
lemma exercise8_topIndicatorIntegral_eq_topBranchIncrement
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    (∫ s in (0 : ℝ)..1,
      if 1 / ((k : ℝ) * x) ≤ s then (-(((exercise8_real_kernel k s : ℝ) : ℂ))) else 0) =
      exercise8_boundary_top_branch k x -
        exercise8_boundary_right_branch k (1 / (k : ℝ)) := by
  let y : ℝ := 1 / ((k : ℝ) * x)
  let kernel : ℝ → ℂ := fun s ↦ (((exercise8_real_kernel k s : ℝ) : ℂ))
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.2 hk_pos) hx
  have hy_pos : 0 < y := by
    dsimp [y]
    exact one_div_pos.2 (mul_pos hk_pos hx_pos)
  have hy_mem : y ∈ Icc (0 : ℝ) 1 := by
    simpa [y] using exercise8_top_branch_argument_mem_Icc (k := k) hx
  have hkernel₀y :
      IntervalIntegrable (exercise8_real_kernel k) MeasureTheory.volume (0 : ℝ) y := by
    refine (exercise8_real_kernel_intervalIntegrable k).mono_set ?_
    have hsubset : Set.Icc (0 : ℝ) y ⊆ Set.Icc (0 : ℝ) 1 := by
      intro t ht
      exact ⟨ht.1, ht.2.trans hy_mem.2⟩
    simpa [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hy_mem.1] using hsubset
  have hkernely₁ :
      IntervalIntegrable (exercise8_real_kernel k) MeasureTheory.volume y (1 : ℝ) := by
    refine (exercise8_real_kernel_intervalIntegrable k).mono_set ?_
    have hsubset : Set.Icc y (1 : ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro t ht
      exact ⟨hy_mem.1.trans ht.1, ht.2⟩
    simpa [Set.uIcc_of_le hy_mem.2, Set.uIcc_of_le zero_le_one] using hsubset
  have htail_indicator :
      (∫ s in (0 : ℝ)..1, if y ≤ s then -kernel s else 0) =
        ∫ s in y..(1 : ℝ), -kernel s := by
    have hone_sub_mem : 1 - y ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hy_mem.1, hy_mem.2]
    calc
      (∫ s in (0 : ℝ)..1, if y ≤ s then -kernel s else 0) =
        ∫ s in (0 : ℝ)..1, if s ≤ 1 - y then -kernel (1 - s) else 0 := by
          symm
          simpa [kernel, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun s : ℝ ↦ if y ≤ s then -kernel s else 0)
              (a := (0 : ℝ)) (b := 1) (d := 1))
      _ = ∫ s in (0 : ℝ)..(1 - y), -kernel (1 - s) := by
          simpa [Set.indicator] using
            (intervalIntegral.integral_indicator
              (μ := MeasureTheory.volume)
              (f := fun s : ℝ ↦ -kernel (1 - s))
              (a₁ := (0 : ℝ)) (a₂ := 1 - y) (a₃ := (1 : ℝ))
              hone_sub_mem)
      _ = ∫ s in y..(1 : ℝ), -kernel s := by
          simpa [kernel, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun s : ℝ ↦ -kernel s)
              (a := (0 : ℝ)) (b := 1 - y) (d := 1))
  have hsplit :
      (∫ s in (0 : ℝ)..y, kernel s) + (∫ s in y..(1 : ℝ), kernel s) =
        ∫ s in (0 : ℝ)..1, kernel s := by
    have hsplit_real :
        (∫ s in (0 : ℝ)..y, exercise8_real_kernel k s) +
            (∫ s in y..(1 : ℝ), exercise8_real_kernel k s) =
          ∫ s in (0 : ℝ)..1, exercise8_real_kernel k s := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals
          (f := exercise8_real_kernel k) hkernel₀y hkernely₁)
    have hsplit_cast := congrArg (fun r : ℝ ↦ ((r : ℂ))) hsplit_real
    simpa [kernel, exercise8_intervalIntegral_ofReal] using hsplit_cast
  have hinner :
      ∫ s in (0 : ℝ)..y, kernel s = exercise8_boundary_inner_branch k y := by
    calc
      ∫ s in (0 : ℝ)..y, kernel s =
          ∫ s in (0 : ℝ)..1, if s ≤ y then kernel s else 0 := by
            symm
            simpa [Set.indicator, kernel] using
              (intervalIntegral.integral_indicator
                (μ := MeasureTheory.volume)
                (f := fun s : ℝ ↦ kernel s)
                (a₁ := (0 : ℝ)) (a₂ := y) (a₃ := (1 : ℝ))
                hy_mem)
      _ = exercise8_boundary_inner_branch k y := by
            simpa [kernel] using exercise8_indicatorIntegral_eq_inner_branch k hy_pos hy_mem.2
  have htotal :
      ∫ s in (0 : ℝ)..1, kernel s = exercise8_complete_real_period k := by
    calc
      ∫ s in (0 : ℝ)..1, kernel s =
          (((∫ s in (0 : ℝ)..1, exercise8_real_kernel k s : ℝ)) : ℂ) := by
            symm
            simpa [kernel] using (exercise8_intervalIntegral_ofReal (f := exercise8_real_kernel k))
      _ = exercise8_complete_real_period k := by
        simpa [exercise8_real_kernel] using
          (congrArg (fun r : ℝ ↦ ((r : ℂ))) (exercise8_complete_real_period_def k)).symm
  have htop :
      exercise8_boundary_top_branch k x =
        (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
          exercise8_boundary_inner_branch k y := by
    rw [exercise8_boundary_top_branch_eq_inner_composition,
      exercise8_boundary_inner_branch_eq_inner_primitive]
  have hvertex :
      exercise8_boundary_right_branch k (1 / (k : ℝ)) =
        exercise8_complete_real_period k +
          exercise8_complete_imaginary_period k * Complex.I := by
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
      _ = exercise8_complete_real_period k +
            exercise8_complete_imaginary_period k * Complex.I := by
            simpa using exercise8_boundary_value_inv_k k
  -- Rewrite the upper cutoff as the tail integral `-∫_y^1 kernel`, then identify that tail with
  -- the top-edge branch increment by splitting the complete real period at `y`.
  calc
    (∫ s in (0 : ℝ)..1, if 1 / ((k : ℝ) * x) ≤ s then (-(((exercise8_real_kernel k s : ℝ) : ℂ))) else 0) =
        ∫ s in y..(1 : ℝ), -kernel s := by
          simpa [y, kernel] using htail_indicator
    _ = exercise8_boundary_inner_branch k y - exercise8_complete_real_period k := by
          have hsplit' :
              ∫ s in y..(1 : ℝ), kernel s =
                (∫ s in (0 : ℝ)..1, kernel s) - (∫ s in (0 : ℝ)..y, kernel s) := by
            apply eq_sub_iff_add_eq.mpr
            simpa [add_comm, add_left_comm, add_assoc] using hsplit
          rw [intervalIntegral.integral_neg, hsplit']
          calc
            -((∫ s in (0 : ℝ)..1, kernel s) - (∫ s in (0 : ℝ)..y, kernel s)) =
                -exercise8_complete_real_period k + exercise8_boundary_inner_branch k y := by
                  rw [hinner, htotal]
                  ring
            _ = exercise8_boundary_inner_branch k y - exercise8_complete_real_period k := by
                  ring
    _ = exercise8_boundary_top_branch k x -
          exercise8_boundary_right_branch k (1 / (k : ℝ)) := by
          rw [htop, hvertex]
          ring

/-- Helper for Cartan section26 0018_Exercise_8: away from the null endpoint set
`{0, 1, 1 / ((k : ℝ) * x)}`, the fixed top-edge cutoff integrand has the pointwise boundary limit
needed by dominated convergence. -/
lemma exercise8_topIndicator_ae_tendsto_limit
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc (0 : ℝ) 1 →
        Filter.Tendsto
          (fun w : ℂ ↦
            if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0)
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
          (nhds (if 1 / ((k : ℝ) * x) ≤ s then -(((exercise8_real_kernel k s : ℝ) : ℂ)) else 0)) := by
  let l : Filter ℂ := nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}
  let cutoff : ℂ → ℝ := fun w ↦ (k : ℝ)⁻¹ * w.re⁻¹
  let cutoffX : ℝ := x⁻¹ * (k : ℝ)⁻¹
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.2 hk_pos) hx
  have hcutoffx_ae : ∀ᵐ s ∂MeasureTheory.volume, s ≠ cutoffX := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  have h0_ae : ∀ᵐ s ∂MeasureTheory.volume, s ≠ (0 : ℝ) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  have h1_ae : ∀ᵐ s ∂MeasureTheory.volume, s ≠ (1 : ℝ) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [hcutoffx_ae, h0_ae, h1_ae] with s hcutoffx h0 h1
  intro hs
  have hs_mem : s ∈ Ioc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le zero_le_one] at hs
    exact hs
  have hs_top : s ∈ Ioo (0 : ℝ) 1 := ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 h1⟩
  have hIm :
      Filter.Tendsto (fun w : ℂ ↦ w.im) l (nhds 0) := by
    simpa [l] using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (f := fun w : ℂ ↦ w.im)
        (s := {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
        (Complex.continuous_im.continuousAt.tendsto :
          Filter.Tendsto (fun w : ℂ ↦ w.im) (nhds (x : ℂ)) (nhds ((x : ℂ).im))))
  have hIm_pos :
      ∀ᶠ w in l, w.im ∈ Set.Ioi 0 := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    exact hw.1
  have hImWithin :
      Filter.Tendsto (fun w : ℂ ↦ w.im) l (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hIm hIm_pos
  have hslice :
      Filter.Tendsto (fun w : ℂ ↦ exercise8_topReciprocalSlice k s w.im) l
        (nhds (-(((exercise8_real_kernel k s : ℝ) : ℂ)))) := by
    simpa [l] using (exercise8_topReciprocalSlice_tendsto_negRealKernel k hs_top).comp hImWithin
  have hre :
      Filter.Tendsto (fun w : ℂ ↦ w.re) l (nhds x) := by
    simpa [l] using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (f := fun w : ℂ ↦ w.re)
        (s := {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
        (Complex.continuous_re.continuousAt.tendsto :
          Filter.Tendsto (fun w : ℂ ↦ w.re) (nhds (x : ℂ)) (nhds ((x : ℂ).re))))
  have hcutoff :
      Filter.Tendsto cutoff l (nhds cutoffX) := by
    have hscale :
        Filter.Tendsto (fun w : ℂ ↦ (k : ℝ) * w.re) l (nhds ((k : ℝ) * x)) := by
      exact tendsto_const_nhds.mul hre
    have hscale_ne : (k : ℝ) * x ≠ 0 := mul_ne_zero hk_pos.ne' hx_pos.ne'
    have hinv :
        ContinuousAt (fun r : ℝ ↦ r⁻¹) ((k : ℝ) * x) := continuousAt_id.inv₀ hscale_ne
    convert hinv.tendsto.comp hscale using 1
    · ext w
      simp [cutoff, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
    · simp [cutoffX, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
  by_cases hcut : cutoffX ≤ s
  · have hcut_lt : cutoffX < s := lt_of_le_of_ne hcut (by simpa [cutoffX, eq_comm] using hcutoffx)
    have htrue :
        ∀ᶠ w in l, cutoff w ≤ s := by
      have hlt :
          {w : ℂ | cutoff w < s} ∈ l := by
        simpa [l] using hcutoff (IsOpen.mem_nhds isOpen_Iio hcut_lt)
      filter_upwards [hlt] with w hw
      exact le_of_lt hw
    have hEq :
        Filter.EventuallyEq l
          (fun w : ℂ ↦
            if cutoff w ≤ s then exercise8_topReciprocalSlice k s w.im else 0)
          (fun w : ℂ ↦ exercise8_topReciprocalSlice k s w.im) := by
      filter_upwards [htrue] with w hw
      simp [hw]
    simpa [cutoff, cutoffX, hcut, l, one_div, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.congr' hEq.symm hslice
  · have hcut_lt : s < cutoffX := lt_of_not_ge hcut
    have hfalse :
        ∀ᶠ w in l, ¬cutoff w ≤ s := by
      have hgt :
          {w : ℂ | s < cutoff w} ∈ l := by
        simpa [l] using hcutoff (IsOpen.mem_nhds isOpen_Ioi hcut_lt)
      filter_upwards [hgt] with w hw
      exact not_le_of_gt hw
    have hEq :
        Filter.EventuallyEq l
          (fun w : ℂ ↦
            if cutoff w ≤ s then exercise8_topReciprocalSlice k s w.im else 0)
          (fun _ : ℂ ↦ (0 : ℂ)) := by
      filter_upwards [hfalse] with w hw
      simp [hw]
    simpa [cutoff, cutoffX, hcut, l, one_div, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.congr' hEq.symm
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℂ ↦ (0 : ℂ)) l (nhds (0 : ℂ)))

/-- Helper for Cartan section26 0018_Exercise_8: the remaining analytic blocker on the top edge is
the dominated-convergence theorem for the reciprocal fixed-interval owner. Once that is proved,
the public top-strip theorem is only a final rewrite from the explicit segment to this owner. -/
lemma exercise8_topHorizontal_indicator_tendsto_topBranchIncrement
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    Filter.Tendsto
      (fun w : ℂ ↦
        ∫ s in (0 : ℝ)..1,
          if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
      (nhds
        (exercise8_boundary_top_branch k x -
          exercise8_boundary_right_branch k (1 / (k : ℝ)))) := by
  let l : Filter ℂ := nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}
  have hF_meas :
      ∀ᶠ w in l,
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ ↦
            if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    have hslice_cont :
        ContinuousOn (fun s : ℝ ↦ exercise8_topReciprocalSlice k s w.im) (Set.uIoc (0 : ℝ) 1) := by
      refine (exercise8_topReciprocalSlice_continuousOn_pos k hw.1).mono ?_
      intro s hs
      have hs_mem : s ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hs
      exact hs_mem.1
    have hslice_ae :
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ ↦ exercise8_topReciprocalSlice k s w.im)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      exact hslice_cont.aestronglyMeasurable (by
        simpa [Set.uIoc_of_le zero_le_one] using measurableSet_Ioc)
    -- On `[0, 1]`, the only nontrivial branch is the continuous reciprocal slice above the fixed
    -- positive cutoff, so the fixed-cutoff owner is just the indicator of that slice.
    simpa [Set.indicator] using hslice_ae.indicator measurableSet_Ici
  have h_bound :
      ∀ᶠ w in l,
        ∀ᵐ s ∂MeasureTheory.volume,
          s ∈ Set.uIoc (0 : ℝ) 1 →
            ‖if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0‖ ≤
              exercise8_real_kernel k s := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    have h0_ae : ∀ᵐ s ∂MeasureTheory.volume, s ≠ (0 : ℝ) := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    have h1_ae : ∀ᵐ s ∂MeasureTheory.volume, s ≠ (1 : ℝ) := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [h0_ae, h1_ae] with s h0 h1
    intro hs
    let cutoffW : ℝ := (k : ℝ)⁻¹ * w.re⁻¹
    by_cases hcut : cutoffW ≤ s
    · have hs_mem : s ∈ Ioc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hs
        exact hs
      have hs_top : s ∈ Ioo (0 : ℝ) 1 := ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 h1⟩
      simpa [cutoffW, hcut, one_div, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
        exercise8_topReciprocalSlice_norm_le_realKernel k hs_top hw.1
    · dsimp [exercise8_real_kernel]
      simp [cutoffW, hcut, one_div, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
  have h_lim :
      ∀ᵐ s ∂MeasureTheory.volume,
        s ∈ Set.uIoc (0 : ℝ) 1 →
          Filter.Tendsto
            (fun w : ℂ ↦
              if 1 / ((k : ℝ) * w.re) ≤ s then exercise8_topReciprocalSlice k s w.im else 0)
            l
            (nhds (if 1 / ((k : ℝ) * x) ≤ s then -(((exercise8_real_kernel k s : ℝ) : ℂ)) else 0)) :=
    exercise8_topIndicator_ae_tendsto_limit k hx
  -- Route correction: the public top-edge increment is now only the fixed-interval dominated-
  -- convergence step, with the final value supplied by the support-file cutoff theorem above.
  have hdc :=
    (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume)
      (bound := exercise8_real_kernel k)
      hF_meas h_bound (exercise8_real_kernel_intervalIntegrable k) h_lim)
  have hlimit_eq :
      (∫ s in (0 : ℝ)..1,
          if 1 / ((k : ℝ) * x) ≤ s then -(((exercise8_real_kernel k s : ℝ) : ℂ)) else 0) =
        exercise8_boundary_top_branch k x -
          exercise8_boundary_right_branch k (1 / (k : ℝ)) :=
    exercise8_topIndicatorIntegral_eq_topBranchIncrement k hx
  exact hlimit_eq ▸ (by simpa [l] using hdc)
