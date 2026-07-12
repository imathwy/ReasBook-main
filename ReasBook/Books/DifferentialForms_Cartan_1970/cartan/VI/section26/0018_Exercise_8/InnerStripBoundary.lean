import DifferentialForms_Cartan_1970.VI.section26.«0017_Exercise_7».CassiniCore
import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».BoundarySliceTransport

open Set
open scoped UpperHalfPlane

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: on the positive inner edge, the factor
`1 - z^2` of the radicand has norm bounded below by its real-axis value `1 - t^2`. -/
lemma exercise8_innerFactor_norm_lower_on_inner
    {t y : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hy : 0 < y) :
    1 - t ^ (2 : ℕ) ≤
      ‖(1 : ℂ) - (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ))‖ := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hfactor_nonneg : 0 ≤ 1 - t ^ (2 : ℕ) := by
    nlinarith [ht.1, ht.2]
  have hsq :
      (1 - t ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        Complex.normSq ((1 : ℂ) - (z ^ (2 : ℕ))) := by
    -- Expanding `‖1 - (t + i y)^2‖²` shows the positive `y`-terms only increase the norm.
    rw [show
        Complex.normSq ((1 : ℂ) - (z ^ (2 : ℕ))) =
          (1 - t ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ) +
            (2 * t * y) ^ (2 : ℕ) by
      simp [z, Complex.normSq_apply, pow_two]
      ring_nf]
    nlinarith
  have hnorm :
      ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ ^ (2 : ℕ) =
        Complex.normSq ((1 : ℂ) - (z ^ (2 : ℕ))) := by
    simpa using Complex.sq_norm ((1 : ℂ) - (z ^ (2 : ℕ)))
  -- Compare the squared lower bound with the squared norm, then drop back to norms.
  nlinarith [hfactor_nonneg, norm_nonneg ((1 : ℂ) - (z ^ (2 : ℕ))), hsq, hnorm]

/-- Helper for Cartan section26 0018_Exercise_8: on the positive inner edge, the factor
`1 - k^2 z^2` of the radicand has norm bounded below by its real-axis value
`1 - k^2 t^2`. -/
lemma exercise8_modulusFactor_norm_lower_on_inner
    (k : Exercise8Modulus) {t y : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hy : 0 < y) :
    1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) ≤
      ‖(1 : ℂ) -
          (((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)))‖ := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hk_sq_lt : (k : ℝ) ^ (2 : ℕ) < 1 := by
    nlinarith [Exercise8Modulus.pos k, Exercise8Modulus.lt_one k]
  have hfactor_nonneg : 0 ≤ 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    nlinarith [hk_sq_lt, ht.1, ht.2]
  have hsq :
      (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        Complex.normSq ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))) := by
    -- The same norm expansion works for the `1 - k^2 z^2` factor.
    rw [show
        Complex.normSq ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))) =
          (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) +
              (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ)) ^ (2 : ℕ) +
            (2 * (k : ℝ) ^ (2 : ℕ) * t * y) ^ (2 : ℕ) by
      simp [z, Complex.normSq_apply, pow_two]
      ring_nf]
    have hk_sq_nonneg : 0 ≤ (k : ℝ) ^ (2 : ℕ) := by positivity
    have hy_term_nonneg : 0 ≤ (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ) := by positivity
    have hbase :
        (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ^ (2 : ℕ) ≤
          (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) +
              (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ)) ^ (2 : ℕ) := by
      nlinarith
    have htail_nonneg : 0 ≤ (2 * (k : ℝ) ^ (2 : ℕ) * t * y) ^ (2 : ℕ) := by positivity
    exact le_trans hbase (by nlinarith)
  have hnorm :
      ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ ^ (2 : ℕ) =
        Complex.normSq ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))) := by
    simpa using Complex.sq_norm ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ))))
  -- As on the first factor, the squared inequality is enough because both sides are nonnegative.
  nlinarith [hfactor_nonneg,
    norm_nonneg ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))), hsq, hnorm]

/-- Helper for Cartan section26 0018_Exercise_8: on the positive inner edge, the complex
integrand is dominated by the real boundary kernel. This is the majorant needed for the pending
dominated-convergence proof of the horizontal boundary limit. -/
lemma exercise8_integrand_norm_le_realKernel_on_inner
    (k : Exercise8Modulus) {t y : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hy : 0 < y) :
    ‖exercise8_integrand k (((t : ℂ) + (y : ℂ) * Complex.I))‖ ≤ exercise8_real_kernel k t := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hz : 0 < z.im := by
    simpa [z] using hy
  have hfactor1_pos : 0 < 1 - t ^ (2 : ℕ) := by
    have ht_abs_lt_one : |t| < 1 := by
      simpa [abs_of_pos ht.1] using ht.2
    have ht_sq_lt_one : t ^ (2 : ℕ) < 1 := by
      have ht_abs_bounds := abs_lt.mp ht_abs_lt_one
      nlinarith [sq_abs t, ht_abs_bounds.1, ht_abs_bounds.2]
    nlinarith
  have hk_sq_lt : (k : ℝ) ^ (2 : ℕ) < 1 := by
    nlinarith [Exercise8Modulus.pos k, Exercise8Modulus.lt_one k]
  have hfactor2_pos : 0 < 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    have ht_abs_lt_one : |t| < 1 := by
      simpa [abs_of_pos ht.1] using ht.2
    have ht_sq_lt_one : t ^ (2 : ℕ) < 1 := by
      have ht_abs_bounds := abs_lt.mp ht_abs_lt_one
      nlinarith [sq_abs t, ht_abs_bounds.1, ht_abs_bounds.2]
    have hkt_sq_lt_one : (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) < 1 := by
      nlinarith [hk_sq_lt, ht_sq_lt_one]
    nlinarith
  have hfactor1 :
      1 - t ^ (2 : ℕ) ≤ ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ :=
    exercise8_innerFactor_norm_lower_on_inner ht hy
  have hfactor2 :
      1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) ≤
        ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ :=
    exercise8_modulusFactor_norm_lower_on_inner k ht hy
  have hmul :
      (1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤
        ‖exercise8_radicand k z‖ := by
    have hmul_aux :
        (1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤
          ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ *
            ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ := by
      nlinarith [hfactor1, hfactor2,
        norm_nonneg ((1 : ℂ) - (z ^ (2 : ℕ))),
        norm_nonneg ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ))))]
    calc
      (1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤
          ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ *
            ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ := hmul_aux
      _ = ‖((1 : ℂ) - (z ^ (2 : ℕ))) *
            ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ))))‖ := by
            rw [norm_mul]
      _ = ‖exercise8_radicand k z‖ := by
            simp [exercise8_radicand, z, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hbranch_sq :
      ‖exercise8_simple_sqrt_branch k z‖ ^ (2 : ℕ) = ‖exercise8_radicand k z‖ := by
    calc
      ‖exercise8_simple_sqrt_branch k z‖ ^ (2 : ℕ) =
          ‖exercise8_simple_sqrt_branch k z ^ (2 : ℕ)‖ := by
            simp [sq]
      _ = ‖exercise8_radicand k z‖ := by
            rw [exercise8_simple_sqrt_branch_sq_eq_on_upper hz]
  have hsqrt :
      Real.sqrt
          ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) ≤
        ‖exercise8_simple_sqrt_branch k z‖ := by
    have hprod_nonneg :
        0 ≤ (1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
      positivity
    nlinarith [hmul, hbranch_sq, hprod_nonneg,
      norm_nonneg (exercise8_simple_sqrt_branch k z), Real.sq_sqrt hprod_nonneg]
  have hbranch_pos : 0 < ‖exercise8_simple_sqrt_branch k z‖ := by
    exact norm_pos_iff.mpr (exercise8_simple_sqrt_branch_ne_zero_on_upper hz)
  have hsqrt_pos :
      0 <
        Real.sqrt
          ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) := by
    apply Real.sqrt_pos.2
    positivity
  -- Invert the lower bound on the square-root branch norm to obtain the desired majorant.
  rw [exercise8_integrand, exercise8_real_kernel]
  simpa [z] using (inv_le_inv₀ hbranch_pos hsqrt_pos).2 hsqrt

/-- Helper for Cartan section26 0018_Exercise_8: after spelling the endpoint as `w.re + i w.im`,
the inner-strip horizontal segment is the same fixed interval integral on `0..1` with the cutoff
`t ≤ w.re`. -/
lemma exercise8_horizontal_segment_explicit_eq_indicatorIntegral
    (k : Exercise8Modulus) {w : ℂ}
    (hw : w ∈ {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}) :
    ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I)
        ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ t in (0 : ℝ)..1,
        if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0 := by
  -- First normalize the horizontal segment to the direct interval `0..w.re`.
  have hdirect :
      ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I)
          ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
        ∫ t in (0 : ℝ)..w.re,
          exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) := by
    have h := exercise8_horizontal_segment_eq_directIntervalIntegral k 0 w.re w.im
    rw [show (((0 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I) = (w.im : ℂ) * Complex.I by simp] at h
    exact h
  calc
    ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I)
        ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z =
        ∫ t in (0 : ℝ)..w.re,
          exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) := hdirect
    _ = ∫ t in (0 : ℝ)..1,
          if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0 := by
        -- Then freeze the moving endpoint by inserting the cutoff indicator on the fixed
        -- interval `[0, 1]`.
        symm
        simpa [Set.indicator, one_mul] using
          (intervalIntegral.integral_indicator
            (μ := MeasureTheory.volume)
            (f := fun t : ℝ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I))
            (a₁ := (0 : ℝ)) (a₂ := w.re) (a₃ := (1 : ℝ))
            ⟨hw.2.1, hw.2.2⟩)

/-- Helper for Cartan section26 0018_Exercise_8: the fixed-interval cutoff model already has the
correct limit owner once the integrand is replaced by the real boundary kernel. -/
lemma exercise8_indicatorIntegral_eq_inner_branch
    (k : Exercise8Modulus) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∫ t in (0 : ℝ)..1,
        (if t ≤ x then ((exercise8_real_kernel k t : ℝ) : ℂ) else 0) =
      exercise8_boundary_inner_branch k x := by
  have hx_mem : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1⟩
  -- The cutoff integral collapses back to the primitive on `0..x`.
  calc
    ∫ t in (0 : ℝ)..1,
        (if t ≤ x then ((exercise8_real_kernel k t : ℝ) : ℂ) else 0) =
      ∫ t in (0 : ℝ)..x, ((exercise8_real_kernel k t : ℝ) : ℂ) := by
        simpa [Set.indicator, one_mul] using
          (intervalIntegral.integral_indicator
            (μ := MeasureTheory.volume)
            (f := fun t : ℝ ↦ ((exercise8_real_kernel k t : ℝ) : ℂ))
            (a₁ := (0 : ℝ)) (a₂ := x) (a₃ := (1 : ℝ)) hx_mem)
    _ = exercise8_boundary_inner_branch k x := by
        -- The bottom-edge branch is exactly the complexified primitive on `[0, 1]`.
        change
          ∫ t in (0 : ℝ)..x,
              ((1 / Real.sqrt
                  ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ) : ℂ) =
            exercise8_boundary_inner_branch k x
        rfl

/-- Helper for Cartan section26 0018_Exercise_8: for a fixed interior real parameter
`t ∈ (0, 1)`, the upper-half-plane branch along the vertical slice `t + i y` tends to the
positive real boundary kernel as `y → 0+`. -/
lemma exercise8_radicand_mem_slitPlane_on_innerStrip
    (k : Exercise8Modulus) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : 0 < y) :
    exercise8_radicand k ((x : ℂ) + (y : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  by_cases hx0 : x = 0
  · -- On the imaginary axis the radicand is a positive real number, hence lies in the slit plane.
    rw [Complex.mem_slitPlane_iff]
    left
    subst hx0
    have hpos : 0 < (1 + y ^ (2 : ℕ)) * (1 + (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ)) := by
      positivity
    simpa [exercise8_radicand, pow_two] using hpos
  · have hx_ne : (0 : ℝ) ≠ x := by
      simpa [eq_comm] using hx0
    have hx_pos : 0 < x := lt_of_le_of_ne hx.1 hx_ne
    have him :
        (exercise8_radicand k ((x : ℂ) + (y : ℂ) * Complex.I)).im =
          -2 * x * y *
            (1 + (k : ℝ) ^ (2 : ℕ) - 2 * (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) +
              2 * (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ)) := by
      simp [exercise8_radicand, pow_two]
      ring
    have hfactor_pos :
        0 <
          1 + (k : ℝ) ^ (2 : ℕ) - 2 * (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) +
            2 * (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ) := by
      have hx_sq_le : x ^ (2 : ℕ) ≤ 1 := by
        nlinarith [hx.1, hx.2]
      nlinarith [Exercise8Modulus.pos k, Exercise8Modulus.lt_one k, hx_sq_le, hy]
    have him_ne : (exercise8_radicand k ((x : ℂ) + (y : ℂ) * Complex.I)).im ≠ 0 := by
      rw [him]
      positivity
    -- Away from the imaginary axis, the imaginary part is strictly negative, so the branch cut
    -- is avoided automatically.
    rw [Complex.mem_slitPlane_iff]
    exact Or.inr him_ne

/-- Helper for Cartan section26 0018_Exercise_8: on the connected inner strip, the source branch
and the principal square root of the radicand differ by a single global sign. -/
lemma exercise8_simpleSqrtBranch_eq_or_eq_neg_principalSqrt_on_innerStrip
    (k : Exercise8Modulus) :
    (∀ {z : ℂ}, 0 < z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1 →
      exercise8_simple_sqrt_branch k z = Complex.sqrt (exercise8_radicand k z)) ∨
      (∀ {z : ℂ}, 0 < z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1 →
        exercise8_simple_sqrt_branch k z = -Complex.sqrt (exercise8_radicand k z)) := by
  let innerStrip : Set ℂ := {z : ℂ | 0 < z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1}
  have hconv : Convex ℝ innerStrip := by
    refine (convex_halfSpace_im_gt (0 : ℝ)).inter ?_
    refine (convex_halfSpace_re_ge (0 : ℝ)).inter ?_
    simpa [innerStrip] using (convex_halfSpace_re_le (1 : ℝ))
  have hnonempty : innerStrip.Nonempty := by
    refine ⟨((1 / 2 : ℝ) : ℂ) + Complex.I, ?_⟩
    constructor
    · simp [innerStrip]
    · constructor <;> norm_num
  let innerStripPoint := {z : ℂ // z ∈ innerStrip}
  let branchOn : innerStripPoint → ℂ :=
    fun z ↦ exercise8_simple_sqrt_branch k (z : ℂ)
  let principalOn : innerStripPoint → ℂ :=
    fun z ↦ Complex.sqrt (exercise8_radicand k (z : ℂ))
  letI : ContractibleSpace innerStripPoint := hconv.contractibleSpace hnonempty
  have hbranch_cont : Continuous branchOn := by
    -- The source branch is already continuous on the strict upper half-plane.
    exact (exercise8_simple_sqrt_branch_continuousOn_upper k).comp_continuous
      continuous_subtype_val fun z ↦ z.2.1
  have hprincipal_cont : Continuous principalOn := by
    rw [continuous_iff_continuousAt]
    intro z
    have hz_slit :
        exercise8_radicand k (z : ℂ) ∈ Complex.slitPlane :=
      by
        simpa [Complex.re_add_im (z : ℂ)] using
          exercise8_radicand_mem_slitPlane_on_innerStrip k
            (x := (z : ℂ).re) (y := (z : ℂ).im) ⟨z.2.2.1, z.2.2.2⟩ z.2.1
    have hsqrt :
        ContinuousAt Complex.sqrt (exercise8_radicand k (z : ℂ)) := by
      rw [Complex.mem_slitPlane_iff] at hz_slit
      exact Complex.continuousAt_sqrt <|
        hz_slit.elim (fun hre ↦ Or.inl hre.le) Or.inr
    -- The principal square root is continuous at every slit-plane-valued inner-strip point.
    have hrad_tendsto :
        Filter.Tendsto
          (fun w : innerStripPoint ↦ exercise8_radicand k (w : ℂ))
          (nhds z)
          (nhds (exercise8_radicand k (z : ℂ))) := by
      simpa using
        (((exercise8_radicand_continuous k).continuousAt.comp continuous_subtype_val.continuousAt).tendsto)
    simpa [principalOn, ContinuousAt] using hsqrt.tendsto.comp hrad_tendsto
  have hsquare :
      ∀ z : innerStripPoint, branchOn z ^ (2 : ℕ) = principalOn z ^ (2 : ℕ) := by
    intro z
    have hz_slit :
        exercise8_radicand k (z : ℂ) ∈ Complex.slitPlane :=
      by
        simpa [Complex.re_add_im (z : ℂ)] using
          exercise8_radicand_mem_slitPlane_on_innerStrip k
            (x := (z : ℂ).re) (y := (z : ℂ).im) ⟨z.2.2.1, z.2.2.2⟩ z.2.1
    -- Both branches square back to the same radicand.
    calc
      branchOn z ^ (2 : ℕ) = exercise8_radicand k (z : ℂ) := by
        exact exercise8_simple_sqrt_branch_sq_eq_on_upper z.2.1
      _ = Complex.sqrt (exercise8_radicand k (z : ℂ)) ^ (2 : ℕ) := by
        symm
        simpa [pow_two] using
          (sq_sqrt_of_mem_slitPlane_or_zero
            (Z := exercise8_radicand k (z : ℂ)) (Or.inr hz_slit))
      _ = principalOn z ^ (2 : ℕ) := by
        rfl
  let agreeSet : Set innerStripPoint := {z | branchOn z = principalOn z}
  let flipSet : Set innerStripPoint := {z | branchOn z = -principalOn z}
  have hagree_closed : IsClosed agreeSet := isClosed_eq hbranch_cont hprincipal_cont
  have hflip_closed : IsClosed flipSet := isClosed_eq hbranch_cont hprincipal_cont.neg
  have hcover : agreeSet ∪ flipSet = Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      have hsquare' : branchOn z ^ 2 = principalOn z ^ 2 := by
        simpa [pow_two] using hsquare z
      rcases eq_or_eq_neg_of_sq_eq_sq (branchOn z) (principalOn z) hsquare' with hEq | hEq
      · exact Or.inl hEq
      · exact Or.inr hEq
  have hdisjoint : agreeSet ∩ flipSet = (∅ : Set innerStripPoint) := by
    ext z
    constructor
    · rintro ⟨hagree, hflip⟩
      have hprincipal_zero : principalOn z = 0 := by
        have hEq : principalOn z = -principalOn z := hagree.symm.trans hflip
        have htwo :
            (2 : ℂ) * principalOn z = 0 := by
          have hsum := congrArg (fun w : ℂ ↦ w + principalOn z) hEq
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using hsum
        exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      have hbranch_zero : branchOn z = 0 := by
        exact hagree.trans hprincipal_zero
      exact False.elim (exercise8_simple_sqrt_branch_ne_zero_on_upper z.2.1 hbranch_zero)
    · intro hz
      simpa using hz
  have hagree_clopen : IsClopen agreeSet := by
    refine ⟨hagree_closed, ?_⟩
    rw [← isClosed_compl_iff]
    have hcompl : agreeSetᶜ = flipSet := by
      ext z
      constructor
      · intro hz
        rcases show z ∈ agreeSet ∪ flipSet by simpa [hcover] with hzAgree | hzFlip
        · exact False.elim (hz hzAgree)
        · exact hzFlip
      · intro hzFlip hzAgree
        have : z ∈ agreeSet ∩ flipSet := ⟨hzAgree, hzFlip⟩
        simpa [hdisjoint] using this
    simpa [hcompl] using hflip_closed
  let base : innerStripPoint := ⟨((1 / 2 : ℝ) : ℂ) + Complex.I, by
    constructor
    · simp [innerStrip]
    · constructor <;> norm_num⟩
  have hbase :
      base ∈ agreeSet ∪ flipSet := by
    have hsquare' : branchOn base ^ 2 = principalOn base ^ 2 := by
      simpa [pow_two] using hsquare base
    rcases eq_or_eq_neg_of_sq_eq_sq (branchOn base) (principalOn base) hsquare' with hEq | hEq
    · exact Or.inl hEq
    · exact Or.inr hEq
  rcases hbase with hbase | hbase
  · have hagree_univ : agreeSet = Set.univ := hagree_clopen.eq_univ ⟨base, hbase⟩
    left
    intro z hz
    have hz_mem : (⟨z, hz⟩ : innerStripPoint) ∈ agreeSet := by
      simpa [hagree_univ]
    simpa [agreeSet, branchOn, principalOn] using hz_mem
  · have hflip_univ : flipSet = Set.univ := by
      have hbase_not_agree : base ∉ agreeSet := by
        intro hbaseAgree
        have : base ∈ agreeSet ∩ flipSet := ⟨hbaseAgree, hbase⟩
        simpa [hdisjoint] using this
      have hagree_empty : agreeSet = (∅ : Set innerStripPoint) := by
        ext z
        constructor
        · intro hz
          have hagree_univ : agreeSet = Set.univ := hagree_clopen.eq_univ ⟨z, hz⟩
          exact False.elim (hbase_not_agree (by simpa [hagree_univ]))
        · intro hz
          simpa using hz
      ext z
      constructor
      · intro _
        simp
      · intro _
        rcases show z ∈ agreeSet ∪ flipSet by simpa [hcover] with hzAgree | hzFlip
        · simpa [hagree_empty] using hzAgree
        · exact hzFlip
    right
    intro z hz
    have hz_mem : (⟨z, hz⟩ : innerStripPoint) ∈ flipSet := by
      simpa [hflip_univ]
    simpa [flipSet, branchOn, principalOn] using hz_mem

/-- Helper for Cartan section26 0018_Exercise_8: the interior anchor at `i` rules out the global
negative sign, so the source branch agrees with the principal square root on the whole inner
strip. -/
lemma exercise8_simpleSqrtBranch_eq_principalSqrt_on_innerStrip
    (k : Exercise8Modulus) {z : ℂ} (hz : 0 < z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1) :
    exercise8_simple_sqrt_branch k z = Complex.sqrt (exercise8_radicand k z) := by
  rcases exercise8_simpleSqrtBranch_eq_or_eq_neg_principalSqrt_on_innerStrip k with hbranch | hbranch
  · -- Once the connected-strip comparison lands in the positive case, this point is immediate.
    exact hbranch hz
  · have hI_strip : 0 < Complex.I.im ∧ 0 ≤ Complex.I.re ∧ Complex.I.re ≤ 1 := by
      simp
    have hI_pos :
        exercise8_simple_sqrt_branch k Complex.I =
          Complex.sqrt (exercise8_radicand k Complex.I) :=
      exercise8_simple_sqrt_branch_eq_principalSqrt_at_I k
    have hI_neg :
        exercise8_simple_sqrt_branch k Complex.I =
          -Complex.sqrt (exercise8_radicand k Complex.I) :=
      hbranch hI_strip
    have hbranch_zero : exercise8_simple_sqrt_branch k Complex.I = 0 := by
      -- The negative global sign would force the anchored interior value to equal its own
      -- negative, contradicting nonvanishing on the upper half-plane.
      have hEq :
          exercise8_simple_sqrt_branch k Complex.I =
            -exercise8_simple_sqrt_branch k Complex.I := by
        calc
          exercise8_simple_sqrt_branch k Complex.I =
              -Complex.sqrt (exercise8_radicand k Complex.I) := hI_neg
          _ = -exercise8_simple_sqrt_branch k Complex.I := by rw [hI_pos]
      have htwo :
          (2 : ℂ) * exercise8_simple_sqrt_branch k Complex.I = 0 := by
        have hsum := congrArg
          (fun w : ℂ ↦ w + exercise8_simple_sqrt_branch k Complex.I) hEq
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using hsum
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact False.elim
      (exercise8_simple_sqrt_branch_ne_zero_on_upper
        (k := k) (z := Complex.I) (by simp) hbranch_zero)

/-- Helper for Cartan section26 0018_Exercise_8: after replacing the source branch by the
principal square root on the inner strip, the vertical slice tends to the positive real kernel. -/
lemma exercise8_principalVerticalSlice_tendsto_realKernel
    (k : Exercise8Modulus) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Filter.Tendsto
      (fun y : ℝ ↦ (Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))⁻¹)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((exercise8_real_kernel k t : ℝ) : ℂ))) := by
  have hprod_pos :
      0 < (1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
    -- On the open interval `(0, 1)`, both real factors in the boundary radicand are positive.
    have hinner : 0 < 1 - t ^ (2 : ℕ) := by
      nlinarith [ht.1, ht.2]
    have hmod : 0 < 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
      exact exercise8_real_factor_radicand_pos (k := k) ⟨ht.1.le, ht.2.le⟩
    positivity
  have hrad_eq :
      exercise8_radicand k (t : ℂ) =
        ((((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ) : ℂ) := by
    simp [exercise8_radicand]
  have hrad_tendsto :
      Filter.Tendsto
        (fun y : ℝ ↦ exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (exercise8_radicand k (t : ℂ))) := by
    -- The radicand is polynomial, so the slice limit is just continuity at the boundary point.
    have hslice :
        ContinuousAt (fun y : ℝ ↦ exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)) 0 := by
      have hpath : Continuous fun y : ℝ ↦ (t : ℂ) + (y : ℂ) * Complex.I := by
        exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      exact (exercise8_radicand_continuous k).continuousAt.comp hpath.continuousAt
    simpa using hslice.continuousWithinAt.tendsto
  have hsqrt_tendsto :
      Filter.Tendsto
        (fun y : ℝ ↦ Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Complex.sqrt (exercise8_radicand k (t : ℂ)))) := by
    have hsqrt_cont : ContinuousAt Complex.sqrt (exercise8_radicand k (t : ℂ)) := by
      simpa [hrad_eq] using
        (Complex.continuousAt_sqrt (Or.inl hprod_pos.le) :
          ContinuousAt Complex.sqrt
            ((((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ) : ℂ))
    exact hsqrt_cont.tendsto.comp hrad_tendsto
  have hsqrt_ne_zero : Complex.sqrt (exercise8_radicand k (t : ℂ)) ≠ 0 := by
    rw [hrad_eq, Complex.sqrt_of_nonneg]
    · exact_mod_cast (Real.sqrt_ne_zero'.2 hprod_pos)
    · exact_mod_cast hprod_pos.le
  have hprincipal_limit_raw :
      Filter.Tendsto
        (fun y : ℝ ↦ (Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((Complex.sqrt (exercise8_radicand k (t : ℂ)))⁻¹)) := by
    -- The inversion step is valid because the limiting square root is nonzero.
    exact Filter.Tendsto.inv₀ hsqrt_tendsto hsqrt_ne_zero
  have hprincipal_target :
      (Complex.sqrt (exercise8_radicand k (t : ℂ)))⁻¹ =
        (((exercise8_real_kernel k t : ℝ) : ℂ)) := by
    have hsqrt_eq :
        Complex.sqrt (exercise8_radicand k (t : ℂ)) =
          (((Real.sqrt
              ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)))) : ℝ) : ℂ) := by
      rw [hrad_eq, Complex.sqrt_of_nonneg]
      · rfl
      · exact_mod_cast hprod_pos.le
    rw [hsqrt_eq, exercise8_real_kernel]
    simp
  -- The principal square root on the real boundary value is the positive real one, so its
  -- reciprocal is exactly Cartan's real kernel.
  simpa [hprincipal_target] using hprincipal_limit_raw

/-- Helper for Cartan section26 0018_Exercise_8: the inner-strip vertical slice already converges
to one of the two real boundary kernels; only the global sign anchor remains open. -/
lemma exercise8_innerVerticalSlice_tendsto_signedRealKernel
    (k : Exercise8Modulus) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Filter.Tendsto
      (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((exercise8_real_kernel k t : ℝ) : ℂ))) ∨
      Filter.Tendsto
        (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(((exercise8_real_kernel k t : ℝ) : ℂ)))) := by
  have hprod_pos :
      0 < (1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
    have hinner : 0 < 1 - t ^ (2 : ℕ) := by
      nlinarith [ht.1, ht.2]
    have hmod : 0 < 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
      exact exercise8_real_factor_radicand_pos (k := k) ⟨ht.1.le, ht.2.le⟩
    positivity
  have hrad_eq :
      exercise8_radicand k (t : ℂ) =
        ((((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ) : ℂ) := by
    simp [exercise8_radicand]
  have hrad_tendsto :
      Filter.Tendsto
        (fun y : ℝ ↦ exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (exercise8_radicand k (t : ℂ))) := by
    -- The radicand is polynomial, so the slice tends to the real boundary value by continuity.
    have hslice :
        ContinuousAt (fun y : ℝ ↦ exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)) 0 := by
      have hpath : Continuous fun y : ℝ ↦ (t : ℂ) + (y : ℂ) * Complex.I := by
        exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      exact (exercise8_radicand_continuous k).continuousAt.comp hpath.continuousAt
    simpa using hslice.continuousWithinAt.tendsto
  have hsqrt_tendsto :
      Filter.Tendsto
        (fun y : ℝ ↦ Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Complex.sqrt (exercise8_radicand k (t : ℂ)))) := by
    have hsqrt_cont : ContinuousAt Complex.sqrt (exercise8_radicand k (t : ℂ)) := by
      simpa [hrad_eq] using
        (Complex.continuousAt_sqrt (Or.inl hprod_pos.le) :
          ContinuousAt Complex.sqrt
            ((((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ) : ℂ))
    exact hsqrt_cont.tendsto.comp hrad_tendsto
  have hsqrt_ne_zero : Complex.sqrt (exercise8_radicand k (t : ℂ)) ≠ 0 := by
    rw [hrad_eq, Complex.sqrt_of_nonneg]
    · exact_mod_cast (Real.sqrt_ne_zero'.2 hprod_pos)
    · exact_mod_cast hprod_pos.le
  have hprincipal_limit_raw :
      Filter.Tendsto
        (fun y : ℝ ↦ (Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((Complex.sqrt (exercise8_radicand k (t : ℂ)))⁻¹)) := by
    exact Filter.Tendsto.inv₀ hsqrt_tendsto hsqrt_ne_zero
  have hprincipal_target :
      (Complex.sqrt (exercise8_radicand k (t : ℂ)))⁻¹ =
        (((exercise8_real_kernel k t : ℝ) : ℂ)) := by
    have hsqrt_eq :
        Complex.sqrt (exercise8_radicand k (t : ℂ)) =
          (((Real.sqrt
              ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)))) : ℝ) : ℂ) := by
      rw [hrad_eq, Complex.sqrt_of_nonneg]
      · rfl
      · exact_mod_cast hprod_pos.le
    rw [hsqrt_eq, exercise8_real_kernel]
    simp
  have hprincipal_limit :
      Filter.Tendsto
        (fun y : ℝ ↦ (Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((exercise8_real_kernel k t : ℝ) : ℂ))) := by
    simpa [hprincipal_target] using hprincipal_limit_raw
  rcases exercise8_simpleSqrtBranch_eq_or_eq_neg_principalSqrt_on_innerStrip k with hbranch | hbranch
  · left
    have heq :
        (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun y : ℝ ↦
            (Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))⁻¹ := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy_strip :
          0 < (((t : ℂ) + (y : ℂ) * Complex.I)).im ∧
            0 ≤ (((t : ℂ) + (y : ℂ) * Complex.I)).re ∧
              (((t : ℂ) + (y : ℂ) * Complex.I)).re ≤ 1 := by
        simpa using ⟨hy, ht.1.le, ht.2.le⟩
      simp [exercise8_integrand, hbranch hy_strip]
    exact Filter.Tendsto.congr' heq.symm hprincipal_limit
  · right
    have heq :
        (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun y : ℝ ↦
            -((Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))⁻¹) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy_strip :
          0 < (((t : ℂ) + (y : ℂ) * Complex.I)).im ∧
            0 ≤ (((t : ℂ) + (y : ℂ) * Complex.I)).re ∧
              (((t : ℂ) + (y : ℂ) * Complex.I)).re ≤ 1 := by
        simpa using ⟨hy, ht.1.le, ht.2.le⟩
      simp [exercise8_integrand, hbranch hy_strip]
    exact Filter.Tendsto.congr' heq.symm hprincipal_limit.neg

/-- Helper for Cartan section26 0018_Exercise_8: for a fixed interior real parameter
`t ∈ (0, 1)`, the upper-half-plane branch along the vertical slice `t + i y` tends to the
positive real boundary kernel as `y → 0+`. -/
lemma exercise8_innerVerticalSlice_tendsto_realKernel
    (k : Exercise8Modulus) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Filter.Tendsto
      (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((exercise8_real_kernel k t : ℝ) : ℂ))) := by
  have heq :
      (fun y : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun y : ℝ ↦
          (Complex.sqrt (exercise8_radicand k ((t : ℂ) + (y : ℂ) * Complex.I)))⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy_strip :
        0 < (((t : ℂ) + (y : ℂ) * Complex.I)).im ∧
          0 ≤ (((t : ℂ) + (y : ℂ) * Complex.I)).re ∧
            (((t : ℂ) + (y : ℂ) * Complex.I)).re ≤ 1 := by
      simpa using ⟨hy, ht.1.le, ht.2.le⟩
    -- The new interior anchor at `i` sharpens the old global `±` comparison to plain equality.
    simp [exercise8_integrand, exercise8_simpleSqrtBranch_eq_principalSqrt_on_innerStrip k hy_strip]
  exact Filter.Tendsto.congr' heq.symm
    (exercise8_principalVerticalSlice_tendsto_realKernel k ht)

/-- Helper for Cartan section26 0018_Exercise_8: away from the null exceptional set
`{x, 1}`, the fixed-interval cutoff integrand has the pointwise boundary limit needed by the
interval dominated-convergence theorem. -/
lemma exercise8_innerIndicator_ae_tendsto_limit
    (k : Exercise8Modulus) {x : ℝ} :
    ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (0 : ℝ) 1 →
        Filter.Tendsto
          (fun w : ℂ ↦
            if t ≤ w.re then
              exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I)
            else 0)
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
          (nhds (if t ≤ x then (((exercise8_real_kernel k t : ℝ)) : ℂ) else 0)) := by
  have htx_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ x := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  have h1_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 : ℝ) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [htx_ae, h1_ae] with t htx h1
  intro ht
  have ht_mem : t ∈ Ioc (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le zero_le_one] using ht
  have ht_inner : t ∈ Ioo (0 : ℝ) 1 := ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 h1⟩
  have hIm :
      Filter.Tendsto (fun w : ℂ ↦ w.im)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
        (nhds 0) := by
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (f := fun w : ℂ ↦ w.im)
        (s := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
        (Complex.continuous_im.continuousAt.tendsto : Filter.Tendsto (fun w : ℂ ↦ w.im) (nhds (x : ℂ)) (nhds ((x : ℂ).im))))
  have hIm_pos :
      ∀ᶠ w in nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1},
        w.im ∈ Set.Ioi 0 := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    exact hw.1
  have hImWithin :
      Filter.Tendsto (fun w : ℂ ↦ w.im)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
        (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hIm hIm_pos
  have hslice :
      Filter.Tendsto
        (fun w : ℂ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I))
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
        (nhds (((exercise8_real_kernel k t : ℝ) : ℂ))) := by
    simpa using (exercise8_innerVerticalSlice_tendsto_realKernel k ht_inner).comp hImWithin
  have hre :
      Filter.Tendsto (fun w : ℂ ↦ w.re)
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
        (nhds x) := by
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (f := fun w : ℂ ↦ w.re)
        (s := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
        (Complex.continuous_re.continuousAt.tendsto : Filter.Tendsto (fun w : ℂ ↦ w.re) (nhds (x : ℂ)) (nhds ((x : ℂ).re))))
  by_cases htx_le : t ≤ x
  · have htx_lt : t < x := lt_of_le_of_ne htx_le htx
    have htrue :
        ∀ᶠ w in nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1},
          t ≤ w.re := by
      have hgt :
          {w : ℂ | t < w.re} ∈
            nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1} := by
        simpa using hre (IsOpen.mem_nhds isOpen_Ioi htx_lt)
      filter_upwards [hgt] with w hw using le_of_lt hw
    have hEq :
        (fun w : ℂ ↦
          if t ≤ w.re then
            exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I)
          else 0) =ᶠ[nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}]
        fun w : ℂ ↦ exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) := by
      filter_upwards [htrue] with w hw
      simp [hw]
    simpa [htx_le] using Filter.Tendsto.congr' hEq.symm hslice
  · have hxt_lt : x < t := lt_of_not_ge htx_le
    have hfalse :
        ∀ᶠ w in nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1},
          ¬ t ≤ w.re := by
      have hlt :
          {w : ℂ | w.re < t} ∈
            nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1} := by
        simpa using hre (IsOpen.mem_nhds isOpen_Iio hxt_lt)
      filter_upwards [hlt] with w hw
      exact not_le_of_gt hw
    have hEq :
        (fun w : ℂ ↦
          if t ≤ w.re then
            exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I)
          else 0) =ᶠ[nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}]
        fun _ : ℂ ↦ (0 : ℂ) := by
      filter_upwards [hfalse] with w hw
      simp [hw]
    simpa [htx_le] using Filter.Tendsto.congr' hEq.symm
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℂ ↦ (0 : ℂ))
        (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}) (nhds (0 : ℂ)))

/-- Helper for Cartan section26 0018_Exercise_8: the remaining inner-strip blocker is the
fixed-interval dominated-convergence bridge for the cutoff model. -/
lemma exercise8_innerHorizontal_indicator_tendsto
    (k : Exercise8Modulus) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Filter.Tendsto
      (fun w : ℂ ↦
        ∫ t in (0 : ℝ)..1,
          if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
      (nhds (exercise8_boundary_inner_branch k x)) := by
  -- Route correction: the moving endpoint has already been frozen on the fixed interval `0..1`,
  -- so only the interval dominated-convergence theorem remains.
  let l : Filter ℂ := nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}
  have hF_meas :
      ∀ᶠ w in l,
        MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ ↦
            if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
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
    exact
      ((hcont.measurable.piecewise measurableSet_Iic measurable_const).aestronglyMeasurable)
  have h_bound :
      ∀ᶠ w in l,
        ∀ᵐ t ∂MeasureTheory.volume,
          t ∈ Set.uIoc (0 : ℝ) 1 →
            ‖if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0‖ ≤
              exercise8_real_kernel k t := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    have h1_ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 : ℝ) := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [h1_ae] with t h1
    intro ht
    by_cases hcut : t ≤ w.re
    · have ht_mem : t ∈ Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using ht
      have ht_inner : t ∈ Ioo (0 : ℝ) 1 := ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 h1⟩
      simpa [hcut] using exercise8_integrand_norm_le_realKernel_on_inner k ht_inner hw.1
    · dsimp [exercise8_real_kernel]
      simp [hcut, Real.sqrt_nonneg]
  have h_lim :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 →
          Filter.Tendsto
            (fun w : ℂ ↦
              if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0)
            l
            (nhds (if t ≤ x then (((exercise8_real_kernel k t : ℝ)) : ℂ) else 0)) :=
    exercise8_innerIndicator_ae_tendsto_limit k
  -- The limit integral is already the named bottom-edge branch owner.
  simpa [l, exercise8_indicatorIntegral_eq_inner_branch k hx0 hx1] using
    (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume)
      (bound := exercise8_real_kernel k)
      hF_meas h_bound (exercise8_real_kernel_intervalIntegrable k) h_lim)

/-- Helper for Cartan section26 0018_Exercise_8: on the positive bottom edge away from the origin,
the normalized horizontal segment from `Im w * I` to `w` converges to the bottom-edge boundary
branch after the fixed-interval cutoff model is identified. -/
lemma exercise8_horizontalSegment_tendsto_innerBranch
    (k : Exercise8Modulus) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Filter.Tendsto
      (fun w : ℂ ↦
        ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
      (nhds (exercise8_boundary_inner_branch k x)) := by
  -- Route correction: the moving endpoint is now isolated behind one fixed-interval cutoff
  -- bridge, so the public theorem is only a rewrite.
  refine Filter.Tendsto.congr' ?_ (exercise8_innerHorizontal_indicator_tendsto k hx0 hx1)
  filter_upwards [self_mem_nhdsWithin] with w hw using
    (calc
      ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z =
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I)
            ((w.re : ℂ) + (w.im : ℂ) * Complex.I), (exercise8_integrand k dz) z := by
              exact congrArg
                (fun b : ℂ ↦
                  ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) b, (exercise8_integrand k dz) z)
                (Complex.re_add_im w).symm
      _ =
          ∫ t in (0 : ℝ)..1,
            if t ≤ w.re then exercise8_integrand k ((t : ℂ) + (w.im : ℂ) * Complex.I) else 0 := by
              exact exercise8_horizontal_segment_explicit_eq_indicatorIntegral k hw).symm

/-- Helper for Cartan section26 0018_Exercise_8: approaching a point of `[0, 1]` through the
closed inner strip should recover the bottom-edge boundary branch. -/
lemma exercise8_abel_integral_tendsto_inner_strip
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
      (nhds (exercise8_boundary_inner_branch k x)) := by
  -- Route correction: the positive bottom-edge analysis should be proved once on the whole strip,
  -- then reused by both the off-vertex and the endpoint wrappers.
  by_cases hx0 : x = 0
  · subst hx0
    have htarget :
        exercise8_boundary_trace k 0 = exercise8_boundary_inner_branch k 0 := by
      -- At the origin, the repaired real-axis trace and the bottom-edge branch are the same owner.
      rw [show exercise8_boundary_trace k 0 = exercise8_boundary_value k 0 by rfl]
      simpa [exercise8_boundary_inner_branch] using
        exercise8_boundary_value_eq_inner (k := k) (x := 0) ⟨le_rfl, by norm_num⟩
    have hsubset :
        {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1} ⊆ UpperHalfPlane.upperHalfPlaneSet := by
      intro w hw
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hw.1
    -- The origin case is exactly the already-proved ambient from-above limit, restricted to the
    -- smaller inner-strip filter.
    simpa [htarget] using
      (exercise8_abel_integral_tendsto_boundary_trace_zero k).mono_left
        (nhdsWithin_mono _ hsubset)
  · have hxpos : 0 < x := by
      exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hresidual :
        Filter.Tendsto
          (fun w : ℂ ↦
            exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
              exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
              ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
          (nhds 0) :=
      exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_innerStrip k hx
    have hvertical :
        Filter.Tendsto
          (fun w : ℂ ↦
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)))
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
          (nhds 0) :=
      exercise8_abel_integral_verticalLift_tendsto_zero_on_innerStrip (k := k) (x := x)
    have hhorizontal :
        Filter.Tendsto
          (fun w : ℂ ↦
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
          (nhds (exercise8_boundary_inner_branch k x)) :=
      exercise8_horizontalSegment_tendsto_innerBranch k hxpos hx.2
    have hsum :
        Filter.Tendsto
          (fun w : ℂ ↦
            (exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
                exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
                ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z) +
              exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) +
              ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
          (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
          (nhds (exercise8_boundary_inner_branch k x)) := by
      -- The nonzero strip case is the sum of the residual, the vanishing vertical lift, and the
      -- horizontal boundary term.
      simpa using (hresidual.add hvertical).add hhorizontal
    -- The three-term decomposition collapses back to the original Abel integral.
    convert hsum using 1
    ext w
    ring
