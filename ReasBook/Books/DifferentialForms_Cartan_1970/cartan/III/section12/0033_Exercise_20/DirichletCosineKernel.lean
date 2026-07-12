import Mathlib
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import DifferentialForms_Cartan_1970.III.section12.«0008_Example_III_6_extra_3»

open MeasureTheory
open InnerProductSpace
open Filter
open scoped Real Topology

noncomputable section

/-- Helper for Exercise 20: the cosine-difference kernel is the difference of two copies of the
shared `(1 - cos)` kernel. -/
lemma exercise20_cos_sub_cos_div_sq_eq_kernel_difference
    (a b x : ℝ) :
    (Real.cos (2 * a * x) - Real.cos (2 * b * x)) / x ^ 2 =
      ((1 - Real.cos (2 * b * x)) - (1 - Real.cos (2 * a * x))) / x ^ 2 := by
  -- This is the algebraic rewrite that exposes the common kernel for part (2).
  ring

/-- Helper for Exercise 20: the boundary correction `(1 - cos x) / x` extends continuously across
`x = 0` as `(x / 2) * sinc (x / 2)^2`. -/
lemma exercise20_one_sub_cos_div_eq_half_mul_sinc_sq
    {x : ℝ} (hx : x ≠ 0) :
    (1 - Real.cos x) / x = (x / 2) * Real.sinc (x / 2) ^ 2 := by
  have hx2 : x / 2 ≠ 0 := by
    exact div_ne_zero hx two_ne_zero
  have hcos : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    calc
      1 - Real.cos x = 1 - Real.cos (2 * (x / 2)) := by
        congr 2
        ring
      _ = 2 * Real.sin (x / 2) ^ 2 := by
        rw [Real.cos_two_mul_eq_one_sub]
        ring
  -- Rewrite both sides in terms of `sin (x / 2)` and clear the nonzero denominator `x / 2`.
  rw [Real.sinc_of_ne_zero hx2]
  calc
    (1 - Real.cos x) / x = (2 * Real.sin (x / 2) ^ 2) / x := by
      rw [hcos]
    _ = (2 * Real.sin (x / 2) ^ 2) / (2 * (x / 2)) := by
      congr 2
      ring
    _ = (x / 2) * (Real.sin (x / 2) / (x / 2)) ^ 2 := by
      field_simp [hx2]

/-- Helper for Exercise 20: the primitive for the Dirichlet kernel is the `sinc` antiderivative
minus the boundary correction term. -/
def exercise20_dirichlet_kernel_primitive (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x, Real.sinc t) - (x / 2) * Real.sinc (x / 2) ^ 2

/-- Helper for Exercise 20: the Dirichlet-kernel primitive vanishes at `0`. -/
lemma exercise20_dirichlet_kernel_primitive_zero :
    exercise20_dirichlet_kernel_primitive 0 = 0 := by
  simp [exercise20_dirichlet_kernel_primitive]

/-- Helper for Exercise 20: the Dirichlet-kernel primitive is continuous, so it is continuous from
the right at `0`. -/
lemma exercise20_dirichlet_kernel_primitive_continuous :
    Continuous exercise20_dirichlet_kernel_primitive := by
  have hprimitive :
      Continuous fun x : ℝ ↦ ∫ t in (0 : ℝ)..x, Real.sinc t := by
    -- The interval-integral primitive of a continuous integrand is continuous everywhere.
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    exact (Real.continuous_sinc.integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt.continuousAt
  have hcorrection :
      Continuous fun x : ℝ ↦ (x / 2) * Real.sinc (x / 2) ^ 2 := by
    -- The boundary correction is a product of continuous factors.
    have hhalf : Continuous fun x : ℝ ↦ x / 2 := by
      continuity
    have hs : Continuous fun x : ℝ ↦ Real.sinc (x / 2) := by
      exact Real.continuous_sinc.comp hhalf
    exact hhalf.mul (hs.pow 2)
  -- Unfold the primitive pointwise so the continuity of each summand applies directly.
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  simpa [exercise20_dirichlet_kernel_primitive] using (hprimitive.sub hcorrection).continuousAt

/-- Helper for Exercise 20: near any positive point, the primitive rewrites to the quotient form
whose derivative is the kernel `(1 - cos x) / x^2`. -/
lemma exercise20_dirichlet_kernel_primitive_eventuallyEq_quotient
    {x : ℝ} (hx : 0 < x) :
    exercise20_dirichlet_kernel_primitive =ᶠ[𝓝 x]
      fun y : ℝ ↦ (∫ t in (0 : ℝ)..y, Real.sinc t) - (1 - Real.cos y) / y := by
  -- On a neighborhood of a positive point, the half-angle rewrite is valid pointwise.
  filter_upwards [Ioi_mem_nhds hx] with y hy
  have hy0 : y ≠ 0 := ne_of_gt hy
  rw [exercise20_dirichlet_kernel_primitive]
  rw [(exercise20_one_sub_cos_div_eq_half_mul_sinc_sq hy0).symm]

/-- Helper for Exercise 20: on `(0, ∞)`, the derivative of the primitive is exactly the positive
kernel `(1 - cos x) / x^2`. -/
lemma exercise20_hasDerivAt_dirichlet_kernel_primitive
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt exercise20_dirichlet_kernel_primitive ((1 - Real.cos x) / x ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hprimitive :
      HasDerivAt (fun y : ℝ ↦ ∫ t in (0 : ℝ)..y, Real.sinc t) (Real.sin x / x) x := by
    -- Differentiate the interval-integral primitive first, then rewrite `sinc x` on `(0, ∞)`.
    simpa [Real.sinc_of_ne_zero hx0] using
      (Real.continuous_sinc.integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt
  have hboundary :
      HasDerivAt (fun y : ℝ ↦ (1 - Real.cos y) / y)
        ((Real.sin x * x - (1 - Real.cos x)) / x ^ 2) x := by
    -- Differentiate the quotient form of the correction term by the usual quotient rule.
    have hnum : HasDerivAt (fun y : ℝ ↦ 1 - Real.cos y) (Real.sin x) x := by
      have hnum_raw : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) - Real.cos y) (0 - -Real.sin x) x :=
        (hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x)
      simpa using hnum_raw
    simpa [pow_two, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      hnum.div (hasDerivAt_id x) hx0
  have hquotient_raw :
      HasDerivAt
        ((fun y : ℝ ↦ ∫ t in (0 : ℝ)..y, Real.sinc t) - fun y : ℝ ↦ (1 - Real.cos y) / y)
        ((1 - Real.cos x) / x ^ 2) x := by
    -- The derivative simplifies exactly to the desired kernel.
    refine (hprimitive.sub hboundary).congr_deriv ?_
    field_simp [hx0]
    ring
  have hquotient :
      HasDerivAt
        (fun y : ℝ ↦ (∫ t in (0 : ℝ)..y, Real.sinc t) - (1 - Real.cos y) / y)
        ((1 - Real.cos x) / x ^ 2) x := by
    simpa using hquotient_raw
  -- Transport the differentiated quotient form back to the primitive by eventual equality.
  exact hquotient.congr_of_eventuallyEq
    (exercise20_dirichlet_kernel_primitive_eventuallyEq_quotient hx)

/-- Helper for Exercise 20: the boundary correction in the Dirichlet primitive vanishes at
infinity. -/
lemma exercise20_tendsto_boundary_correction_atTop :
    Tendsto (fun x : ℝ ↦ (x / 2) * Real.sinc (x / 2) ^ 2) atTop (𝓝 0) := by
  have hEq :
      (fun x : ℝ ↦ (x / 2) * Real.sinc (x / 2) ^ 2) =ᶠ[atTop]
        fun x : ℝ ↦ (1 - Real.cos x) / x := by
    -- On the eventual positive tail, the half-angle identity rewrites the correction term.
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (exercise20_one_sub_cos_div_eq_half_mul_sinc_sq (ne_of_gt hx)).symm
  have hnorm_le :
      ∀ᶠ x : ℝ in atTop, ‖(1 - Real.cos x) / x‖ ≤ 2 / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hnum_nonneg : 0 ≤ 1 - Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
    have hnum_le : 1 - Real.cos x ≤ 2 := by
      linarith [Real.neg_one_le_cos x]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum_nonneg hx.le)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hnum_le (inv_nonneg.mpr hx.le)
  have htwo_div :
      Tendsto (fun x : ℝ ↦ 2 / x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) atTop (𝓝 2)).mul
        tendsto_inv_atTop_zero
  have hquot_zero :
      Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / x) atTop (𝓝 0) := by
    -- Squeeze the quotient by the tail bound `|(1 - cos x) / x| ≤ 2 / x`.
    exact squeeze_zero_norm' hnorm_le htwo_div
  exact Tendsto.congr' hEq.symm hquot_zero

/-- Helper for Exercise 20: the Dirichlet primitive tends to `π / 2` at infinity because the
boundary correction vanishes and the `sinc` antiderivative has the Dirichlet limit. -/
lemma exercise20_tendsto_dirichlet_kernel_primitive_atTop :
    Tendsto exercise20_dirichlet_kernel_primitive atTop (𝓝 (Real.pi / 2)) := by
  have hsinc :
      Tendsto (fun r : ℝ ↦ ∫ x in (0 : ℝ)..r, Real.sinc x) atTop (𝓝 (Real.pi / 2)) := by
    have hEq :
        (fun r : ℝ ↦ ∫ x in (0 : ℝ)..r, Real.sin x / x) =ᶠ[atTop]
          fun r : ℝ ↦ ∫ x in (0 : ℝ)..r, Real.sinc x := by
      -- The imported Dirichlet limit is stated with `sin x / x`; rewrite it to `sinc` eventually.
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact intervalIntegral_sin_div_eq_intervalIntegral_sinc hr
    exact Tendsto.congr' hEq tendsto_intervalIntegral_sin_div_eq_pi_half
  -- Subtract the vanishing boundary correction from the convergent `sinc` primitive.
  simpa [exercise20_dirichlet_kernel_primitive] using
    hsinc.sub exercise20_tendsto_boundary_correction_atTop

/-- Helper for Exercise 20: the base kernel `(1 - cos x) / x^2` is integrable on `(0, ∞)` because
it is the nonnegative derivative of a primitive with a finite limit. -/
lemma exercise20_integrable_one_sub_cos_div_sq :
    IntegrableOn (fun x : ℝ ↦ (1 - Real.cos x) / x ^ 2) (Set.Ioi (0 : ℝ)) := by
  -- Apply improper FTC to the monotone primitive package on `(0, ∞)`.
  refine integrableOn_Ioi_deriv_of_nonneg
    exercise20_dirichlet_kernel_primitive_continuous.continuousAt.continuousWithinAt
    (fun x hx ↦ exercise20_hasDerivAt_dirichlet_kernel_primitive hx)
    ?_ exercise20_tendsto_dirichlet_kernel_primitive_atTop
  intro x hx
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one x)) (sq_nonneg x)

/-- Helper for Exercise 20: the base Dirichlet kernel has integral `π / 2` on `(0, ∞)`. -/
lemma exercise20_integral_one_sub_cos_div_sq :
    ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2 ∂volume = Real.pi / 2 := by
  have hbase :
      ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2 ∂volume
        = Real.pi / 2 - exercise20_dirichlet_kernel_primitive 0 := by
    -- Improper FTC turns the kernel integral into the primitive's boundary values.
    refine integral_Ioi_of_hasDerivAt_of_nonneg
      exercise20_dirichlet_kernel_primitive_continuous.continuousAt.continuousWithinAt
      (fun x hx ↦ exercise20_hasDerivAt_dirichlet_kernel_primitive hx)
      (fun x hx ↦ div_nonneg (sub_nonneg.mpr (Real.cos_le_one x)) (sq_nonneg x))
      exercise20_tendsto_dirichlet_kernel_primitive_atTop
  -- The primitive vanishes at `0`, so only the limit `π / 2` remains.
  simpa [exercise20_dirichlet_kernel_primitive_zero] using hbase

/-- Helper for Exercise 20: away from `0`, the scaled kernel is a constant multiple of the base
kernel after the dilation `y = (2 c) x`. -/
lemma exercise20_one_sub_cos_two_mul_div_sq_eq_scaled_base
    {c x : ℝ} (hc : c ≠ 0) (hx : x ≠ 0) :
    (1 - Real.cos (2 * c * x)) / x ^ 2 =
      (4 * c ^ 2) * ((1 - Real.cos ((2 * c) * x)) / (((2 * c) * x) ^ 2)) := by
  -- Clearing the two nonzero denominators isolates the constant factor `4 c²`.
  have htwo_c : 2 * c ≠ 0 := mul_ne_zero two_ne_zero hc
  have hmul : (2 * c) * x ≠ 0 := mul_ne_zero htwo_c hx
  field_simp [hx, hmul]
  ring

/-- Helper for Exercise 20: for `c ≥ 0`, scaling reduces the shared kernel to the base kernel. -/
lemma exercise20_integral_one_sub_cos_two_mul_div_sq_nonneg
    {c : ℝ} (hc : 0 ≤ c) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos (2 * c * x)) / x ^ 2 ∂volume = Real.pi * c := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · -- At frequency `0`, the integrand vanishes identically.
    simp
  have htwo_pos : 0 < 2 * c := by positivity
  have hpoint :
      ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos (2 * c * x)) / x ^ 2 ∂volume
        =
          ∫ x in Set.Ioi (0 : ℝ),
            (4 * c ^ 2) * ((1 - Real.cos ((2 * c) * x)) / (((2 * c) * x) ^ 2)) ∂volume := by
    -- Rewrite the kernel pointwise on `(0, ∞)` using the explicit scaling identity.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact exercise20_one_sub_cos_two_mul_div_sq_eq_scaled_base hcpos.ne' (ne_of_gt hx)
  have hscale :
      ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos ((2 * c) * x)) / (((2 * c) * x) ^ 2) ∂volume
        =
          (2 * c)⁻¹ *
            ∫ u in Set.Ioi (0 : ℝ), (1 - Real.cos u) / u ^ 2 ∂volume := by
    -- The substitution `u = (2 c) x` reduces the scaled base kernel to the original one.
    simpa using
      (integral_comp_mul_left_Ioi
        (g := fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2)
        (a := (0 : ℝ)) htwo_pos)
  calc
    ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos (2 * c * x)) / x ^ 2 ∂volume
        =
          ∫ x in Set.Ioi (0 : ℝ),
            (4 * c ^ 2) * ((1 - Real.cos ((2 * c) * x)) / (((2 * c) * x) ^ 2)) ∂volume := hpoint
    _ =
          (4 * c ^ 2) *
            ∫ x in Set.Ioi (0 : ℝ),
              (1 - Real.cos ((2 * c) * x)) / (((2 * c) * x) ^ 2) ∂volume := by
            rw [integral_const_mul]
    _ =
          (4 * c ^ 2) *
            ((2 * c)⁻¹ * ∫ u in Set.Ioi (0 : ℝ), (1 - Real.cos u) / u ^ 2 ∂volume) := by
            rw [hscale]
    _ = (4 * c ^ 2) * ((2 * c)⁻¹ * (Real.pi / 2)) := by
          rw [exercise20_integral_one_sub_cos_div_sq]
    _ = Real.pi * c := by
          field_simp [hcpos.ne', Real.pi_ne_zero]
          ring

/-- Helper for Exercise 20: the kernel is even in the frequency parameter, so the nonnegative
evaluation upgrades to the textbook absolute value. -/
lemma exercise20_integral_one_sub_cos_two_mul_div_sq
    (c : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos (2 * c * x)) / x ^ 2 ∂volume = Real.pi * |c| := by
  by_cases hc : 0 ≤ c
  · simpa [abs_of_nonneg hc] using
      exercise20_integral_one_sub_cos_two_mul_div_sq_nonneg hc
  · have hnegc : 0 ≤ -c := by linarith
    have hrewrite :
        ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos (2 * c * x)) / x ^ 2 ∂volume
          =
            ∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos (2 * (-c) * x)) / x ^ 2 ∂volume := by
      -- The kernel is even in `c` because `cos` is even.
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      calc
        (1 - Real.cos (2 * c * x)) / x ^ 2
            = (1 - Real.cos (-(2 * c * x))) / x ^ 2 := by rw [Real.cos_neg]
        _ = (1 - Real.cos (2 * (-c) * x)) / x ^ 2 := by
              rw [show 2 * (-c) * x = -(2 * c * x) by ring]
    rw [hrewrite, exercise20_integral_one_sub_cos_two_mul_div_sq_nonneg hnegc]
    rw [abs_of_neg (lt_of_not_ge hc)]

/-- Helper for Exercise 20: the scaled `(1 - cos)` kernels are integrable on `(0, ∞)`. -/
lemma exercise20_integrable_one_sub_cos_two_mul_div_sq
    (c : ℝ) :
    IntegrableOn (fun x : ℝ ↦ (1 - Real.cos (2 * c * x)) / x ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hnonneg :
      ∀ {d : ℝ}, 0 ≤ d →
        IntegrableOn (fun x : ℝ ↦ (1 - Real.cos (2 * d * x)) / x ^ 2) (Set.Ioi (0 : ℝ)) := by
    intro d hd
    rcases eq_or_lt_of_le hd with rfl | hdpos
    · simpa using (integrableOn_zero : IntegrableOn (fun x : ℝ ↦ (0 : ℝ)) (Set.Ioi (0 : ℝ)))
    have hscaled :
        IntegrableOn
          (fun x : ℝ ↦ (1 - Real.cos ((2 * d) * x)) / (((2 * d) * x) ^ 2))
          (Set.Ioi (0 : ℝ)) := by
      -- Positive dilation preserves integrability on `(0, ∞)`.
      have hbase :
          IntegrableOn (fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2) (Set.Ioi ((2 * d) * 0)) := by
        simpa [mul_zero] using exercise20_integrable_one_sub_cos_div_sq
      exact
        (integrableOn_Ioi_comp_mul_left_iff
          (fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2)
          (0 : ℝ) (show 0 < 2 * d by positivity)).2 hbase
    have hconst :
        IntegrableOn
          (fun x : ℝ ↦
            (4 * d ^ 2) * ((1 - Real.cos ((2 * d) * x)) / (((2 * d) * x) ^ 2)))
          (Set.Ioi (0 : ℝ)) :=
      hscaled.const_mul _
    have hEq :
        Set.EqOn
          (fun x : ℝ ↦ (1 - Real.cos (2 * d * x)) / x ^ 2)
          (fun x : ℝ ↦
            (4 * d ^ 2) * ((1 - Real.cos ((2 * d) * x)) / (((2 * d) * x) ^ 2)))
          (Set.Ioi (0 : ℝ)) := by
      intro x hx
      exact exercise20_one_sub_cos_two_mul_div_sq_eq_scaled_base hdpos.ne' (ne_of_gt hx)
    exact (integrableOn_congr_fun hEq measurableSet_Ioi).2 hconst
  by_cases hc : 0 ≤ c
  · exact hnonneg hc
  · have hnegc : 0 ≤ -c := by linarith
    have hneg :
        IntegrableOn (fun x : ℝ ↦ (1 - Real.cos (2 * (-c) * x)) / x ^ 2) (Set.Ioi (0 : ℝ)) :=
      hnonneg hnegc
    have hEq :
        Set.EqOn
          (fun x : ℝ ↦ (1 - Real.cos (2 * c * x)) / x ^ 2)
          (fun x : ℝ ↦ (1 - Real.cos (2 * (-c) * x)) / x ^ 2)
          (Set.Ioi (0 : ℝ)) := by
      intro x hx
      calc
        (1 - Real.cos (2 * c * x)) / x ^ 2
            = (1 - Real.cos (-(2 * c * x))) / x ^ 2 := by rw [Real.cos_neg]
        _ = (1 - Real.cos (2 * (-c) * x)) / x ^ 2 := by
              rw [show 2 * (-c) * x = -(2 * c * x) by ring]
    exact (integrableOn_congr_fun hEq measurableSet_Ioi).2 hneg
