import Mathlib
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import cartan.III.section12.«0008_Example_III_6_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool `lean_leansearch` was unavailable in this environment.
-- The notation in this file was verified locally by `lake lean`.

open MeasureTheory
open InnerProductSpace
open Filter
open scoped Real Topology

noncomputable section

/-- Helper for Exercise 20: reflecting an interval integral across `π` rewrites the integral over
`[0, 2π]` as the paired integral over `[0, π]`. -/
lemma exercise20_intervalIntegral_pair_reflect_two_pi
    (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (0 : ℝ) (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..2 * Real.pi, f t =
      ∫ t in (0 : ℝ)..Real.pi, (f t + f (2 * Real.pi - t)) := by
  have hpi_le : Real.pi ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hpi_mem : Real.pi ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    simp [Real.pi_pos.le, hpi_le]
  have hsplit := (IntervalIntegrable.trans_iff (f := f) (μ := volume) (a := (0 : ℝ))
    (b := Real.pi) (c := 2 * Real.pi) hpi_mem).mp hf
  have hf_left : IntervalIntegrable f volume (0 : ℝ) Real.pi := hsplit.1
  have hf_right : IntervalIntegrable f volume Real.pi (2 * Real.pi) := hsplit.2
  have hf_reflect :
      IntervalIntegrable (fun t : ℝ ↦ f (2 * Real.pi - t)) volume (0 : ℝ) Real.pi := by
    simpa [sub_eq_add_neg, two_mul] using
      hf_right.symm.comp_sub_left (2 * Real.pi) (h := by finiteness)
  -- Split at `π`, then rewrite the upper half by the substitution `t ↦ 2π - t`.
  calc
    ∫ t in (0 : ℝ)..2 * Real.pi, f t
      = (∫ t in (0 : ℝ)..Real.pi, f t) + ∫ t in Real.pi..2 * Real.pi, f t := by
          symm
          exact intervalIntegral.integral_add_adjacent_intervals hf_left hf_right
    _ = (∫ t in (0 : ℝ)..Real.pi, f t) + ∫ t in (0 : ℝ)..Real.pi, f (2 * Real.pi - t) := by
          simpa [sub_eq_add_neg, two_mul] using congrArg
            (fun u : ℝ ↦ (∫ t in (0 : ℝ)..Real.pi, f t) + u)
            (intervalIntegral.integral_comp_sub_left (f := f) (a := (0 : ℝ))
              (b := Real.pi) (d := 2 * Real.pi)).symm
    _ = ∫ t in (0 : ℝ)..Real.pi, (f t + f (2 * Real.pi - t)) := by
          simpa using (intervalIntegral.integral_add hf_left hf_reflect).symm

/-- Helper for Exercise 20: on the unit circle, the quadratic denominator is the squared distance
from the boundary point `e^{it}` to the real point `a`. -/
lemma exercise20_circle_denominator_eq_norm_sq
    (a t : ℝ) :
    1 - 2 * a * Real.cos t + a ^ 2 = ‖circleMap 0 1 t - (a : ℂ)‖ ^ 2 := by
  -- Expand the complex norm square in real and imaginary parts.
  calc
    1 - 2 * a * Real.cos t + a ^ 2
      = (Real.cos t - a) ^ 2 + Real.sin t ^ 2 := by
          rw [sq, sq]
          nlinarith [Real.sin_sq_add_cos_sq t]
    _ = ‖circleMap 0 1 t - (a : ℂ)‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq]
          simp [Complex.normSq_apply, circleMap_zero_re, circleMap_zero_im, pow_two]

/-- Helper for Exercise 20: when `|a| ≠ 1`, the Poisson-kernel denominator on the unit circle never
vanishes. -/
lemma exercise20_circle_denominator_ne_zero_of_abs_ne_one
    (a : ℝ) (ha : |a| ≠ 1) (t : ℝ) :
    1 - 2 * a * Real.cos t + a ^ 2 ≠ 0 := by
  rw [exercise20_circle_denominator_eq_norm_sq]
  intro hzero
  have hnorm_zero : ‖circleMap 0 1 t - (a : ℂ)‖ = 0 := by
    exact sq_eq_zero_iff.mp hzero
  have hpoint : circleMap 0 1 t = (a : ℂ) := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  have habs : |a| = 1 := by
    calc
      |a| = ‖(a : ℂ)‖ := by simp [Complex.norm_real]
      _ = ‖circleMap 0 1 t‖ := by simp [hpoint]
      _ = 1 := by simpa using (norm_circleMap_zero 1 t)
  exact ha habs

/-- Helper for Exercise 20: the Poisson kernel on the unit circle collapses to the standard real
Poisson denominator. -/
lemma exercise20_poissonKernel_circleMap_zero_one
    (a t : ℝ) :
    poissonKernel 0 (a : ℂ) (circleMap 0 1 t) =
      (1 - a ^ 2) / (1 - 2 * a * Real.cos t + a ^ 2) := by
  -- The numerator is `1 - a²`, and the denominator is the boundary distance squared.
  calc
    poissonKernel 0 (a : ℂ) (circleMap 0 1 t)
      = (‖circleMap 0 1 t‖ ^ 2 - ‖(a : ℂ)‖ ^ 2) / ‖circleMap 0 1 t - (a : ℂ)‖ ^ 2 := by
          simp [poissonKernel_def]
    _ = (1 - a ^ 2) / ‖circleMap 0 1 t - (a : ℂ)‖ ^ 2 := by
          simp [norm_circleMap_zero, Complex.norm_real, pow_two]
    _ = (1 - a ^ 2) / (1 - 2 * a * Real.cos t + a ^ 2) := by
          rw [exercise20_circle_denominator_eq_norm_sq]

/-- Helper for Exercise 20: the real part of the `n`-th power of the unit-circle parametrization is
the Fourier mode `cos (n t)`. -/
lemma exercise20_circleMap_zero_pow_re
    (n : ℕ) (t : ℝ) :
    ((circleMap 0 1 t) ^ n).re = Real.cos (n * t) := by
  -- Raise the unit-circle phase to the `n`-th power, then read off its real part.
  rw [circleMap_zero_pow, circleMap_zero_re]
  simp

/-- Helper for Exercise 20: the Poisson-weighted Fourier integrand is invariant under the
reflection `t ↦ 2π - t`. -/
lemma exercise20_poisson_integrand_reflect
    (a : ℝ) (n : ℕ) (t : ℝ) :
    ((1 - a ^ 2) / (1 - 2 * a * Real.cos (2 * Real.pi - t) + a ^ 2)) *
        Real.cos (n * (2 * Real.pi - t)) =
      ((1 - a ^ 2) / (1 - 2 * a * Real.cos t + a ^ 2)) * Real.cos (n * t) := by
  -- Both the Poisson denominator and the Fourier mode are even under `2π - t`.
  rw [Real.cos_two_pi_sub, mul_sub, Real.cos_nat_mul_two_pi_sub]

/-- Helper for Exercise 20: the Poisson-weighted Fourier mode is interval integrable on
`[0, 2π]` whenever the unit-circle denominator stays nonzero. -/
lemma exercise20_poisson_integrand_intervalIntegrable
    (a : ℝ) (n : ℕ) (ha : |a| ≠ 1) :
    IntervalIntegrable
      (fun t : ℝ ↦
        ((1 - a ^ 2) / (1 - 2 * a * Real.cos t + a ^ 2)) * Real.cos (n * t))
      volume (0 : ℝ) (2 * Real.pi) := by
  have hden :
      ∀ t : ℝ, 1 - 2 * a * Real.cos t + a ^ 2 ≠ 0 :=
    exercise20_circle_denominator_ne_zero_of_abs_ne_one a ha
  have hcont :
      Continuous fun t : ℝ ↦
        ((1 - a ^ 2) / (1 - 2 * a * Real.cos t + a ^ 2)) * Real.cos (n * t) := by
    -- The denominator is a nowhere-zero continuous function, so the quotient is continuous.
    refine (Continuous.div ?_ ?_ hden).mul ?_
    · exact continuous_const
    · continuity
    · continuity
  exact hcont.intervalIntegrable _ _

/-- Helper for Exercise 20: applying the Poisson mean-value formula to `Re(z^n)` evaluates the
Poisson average at the interior real point `a`. -/
lemma exercise20_poisson_average_fourier_mode
    {a : ℝ} {n : ℕ} (ha : |a| < 1) :
    Real.circleAverage (poissonKernel 0 (a : ℂ) • fun z : ℂ ↦ (z ^ n).re) 0 1 = a ^ n := by
  have hharm :
      HarmonicOnNhd (fun z : ℂ ↦ (z ^ n).re) (Metric.closedBall 0 1) := by
    -- Route correction: the remaining Poisson step is purely harmonic; no second contour package
    -- is needed once `Re(z^n)` is recognized as harmonic on the closed unit disc.
    intro z hz
    simpa using (analyticAt_id.pow n).harmonicAt_re
  have hball : (a : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, Complex.norm_real] using ha
  have hmean :=
    HarmonicOnNhd.circleAverage_poissonKernel_smul hharm hball
  have hpow : ((a : ℂ) ^ n).re = a ^ n := by
    have hcast : (a : ℂ) ^ n = ((a ^ n : ℝ) : ℂ) := by
      norm_num
    rw [hcast]
    rfl
  exact hmean.trans hpow

/-- Helper for Exercise 20: the Poisson circle average for `Re(z^n)` rewrites as the target
`0..π` cosine integral. -/
lemma exercise20_poisson_circleAverage_eq_intervalIntegral
    {a : ℝ} {n : ℕ} (ha : |a| ≠ 1) :
    Real.circleAverage (poissonKernel 0 (a : ℂ) • fun z : ℂ ↦ (z ^ n).re) 0 1 =
      ((1 - a ^ 2) / Real.pi) *
        ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2) := by
  let f : ℝ → ℝ := fun t ↦
    ((1 - a ^ 2) / (1 - 2 * a * Real.cos t + a ^ 2)) * Real.cos (n * t)
  have hf : IntervalIntegrable f volume (0 : ℝ) (2 * Real.pi) :=
    exercise20_poisson_integrand_intervalIntegrable a n ha
  have hpair :
      ∫ t in (0 : ℝ)..2 * Real.pi, f t = 2 * ∫ t in (0 : ℝ)..Real.pi, f t := by
    calc
      ∫ t in (0 : ℝ)..2 * Real.pi, f t
          = ∫ t in (0 : ℝ)..Real.pi, (f t + f (2 * Real.pi - t)) := by
              simpa [f] using exercise20_intervalIntegral_pair_reflect_two_pi f hf
      _ = ∫ t in (0 : ℝ)..Real.pi, (2 * f t) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with t ht
            have hreflect := exercise20_poisson_integrand_reflect a n t
            have hreflect' : f (2 * Real.pi - t) = f t := by
              simpa [f] using hreflect
            rw [hreflect']
            ring
      _ = 2 * ∫ t in (0 : ℝ)..Real.pi, f t := by
            rw [intervalIntegral.integral_const_mul]
  have hpoint :
      ∀ t : ℝ,
        f t = (1 - a ^ 2) *
          (Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)) := by
    intro t
    have hden : 1 - 2 * a * Real.cos t + a ^ 2 ≠ 0 :=
      exercise20_circle_denominator_ne_zero_of_abs_ne_one a ha t
    field_simp [f, hden]
    ring
  have hpull :
      ∫ t in (0 : ℝ)..Real.pi, f t =
        (1 - a ^ 2) *
          ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2) := by
    -- Pull the constant `1 - a²` outside after rewriting the pointwise quotient.
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    exact hpoint t
  -- Replace the circle average by its `0..2π` definition, then collapse by reflection.
  rw [Real.circleAverage_def, smul_eq_mul]
  calc
    (2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (poissonKernel 0 (a : ℂ) • fun z : ℂ ↦ (z ^ n).re) (circleMap 0 1 θ)
      = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
          congr 1
          apply intervalIntegral.integral_congr_ae
          filter_upwards with t ht
          simp [f, exercise20_poissonKernel_circleMap_zero_one, exercise20_circleMap_zero_pow_re]
    _ = (2 * Real.pi)⁻¹ * (2 * ∫ t in (0 : ℝ)..Real.pi, f t) := by rw [hpair]
    _ = (1 / Real.pi) * ∫ t in (0 : ℝ)..Real.pi, f t := by
          field_simp [Real.pi_ne_zero]
    _ = ((1 - a ^ 2) / Real.pi) *
        ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2) := by
          rw [hpull]
          ring

/-- Helper for Exercise 20: the substitution `x = sqrt (a / b) * y` reduces the quadratic kernel
to the normalized kernel `1 + y²`. -/
lemma exercise20_integral_inv_quadratic_pow_scaling
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
      = (Real.sqrt (a / b) / a ^ n) *
          ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := by
  let c : ℝ := Real.sqrt (a / b)
  have hc : 0 < c := by
    -- The scaling factor is positive because `a / b > 0`.
    dsimp [c]
    exact Real.sqrt_pos.mpr (div_pos ha hb)
  have hscale :
      ∫ y in Set.Ioi (0 : ℝ), (a + b * (c * y) ^ 2)⁻¹ ^ n ∂volume =
        c⁻¹ * ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume := by
    simpa [c, smul_eq_mul] using
      (integral_comp_mul_left_Ioi (g := fun t : ℝ ↦ (a + b * t ^ 2)⁻¹ ^ n) (a := (0 : ℝ)) hc)
  have hc_sq : c ^ 2 = a / b := by
    -- Squaring the chosen scale recovers the ratio `a / b`.
    dsimp [c]
    simpa [pow_two] using Real.sq_sqrt (show 0 ≤ a / b by exact (div_nonneg ha.le hb.le))
  have hpoint :
      ∀ y : ℝ,
        (a + b * (c * y) ^ 2)⁻¹ ^ n =
          (a⁻¹ ^ n) * (1 + y ^ 2)⁻¹ ^ n := by
    intro y
    have hrewrite : a + b * (c * y) ^ 2 = a * (1 + y ^ 2) := by
      -- After the scaling, the quadratic denominator factors as `a (1 + y²)`.
      calc
        a + b * (c * y) ^ 2 = a + b * (c ^ 2 * y ^ 2) := by ring
        _ = a + a * y ^ 2 := by
              rw [hc_sq]
              field_simp [hb.ne']
        _ = a * (1 + y ^ 2) := by ring
    -- Separate the constant factor `a` from the normalized kernel.
    rw [hrewrite, mul_inv_rev, mul_pow]
    ring
  -- Route correction: the outer scaling is now isolated, so the remaining blocker is only the
  -- normalized integral `∫_0^∞ (1 + y²)^(-n) dy`.
  calc
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
        = c * ∫ y in Set.Ioi (0 : ℝ), (a + b * (c * y) ^ 2)⁻¹ ^ n ∂volume := by
            calc
              ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
                  = c * (c⁻¹ * ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume) := by
                      field_simp [hc.ne']
                _ = c * ∫ y in Set.Ioi (0 : ℝ), (a + b * (c * y) ^ 2)⁻¹ ^ n ∂volume := by
                      rw [hscale]
    _ = c * ∫ y in Set.Ioi (0 : ℝ), (a⁻¹ ^ n) * (1 + y ^ 2)⁻¹ ^ n ∂volume := by
          congr 1
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y hy
          exact hpoint y
    _ = (c * a⁻¹ ^ n) * ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := by
          rw [integral_const_mul]
          ring
    _ = (Real.sqrt (a / b) / a ^ n) * ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := by
          simp [c, div_eq_mul_inv, inv_pow]

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

/-- Helper for Exercise 20: the rational prefactor in part (3) splits into the Dirichlet term minus
the quadratic correction term. -/
lemma exercise20_quadratic_ratio_mul_sin_div_split
    (a x : ℝ) (hden : x ^ 2 + a ^ 2 ≠ 0) :
    ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x) =
      Real.sin x / x - (2 * a ^ 2) * ((Real.sin x / x) / (x ^ 2 + a ^ 2)) := by
  -- Clearing the nonvanishing quadratic denominator exposes the correction term.
  field_simp [hden]
  ring

/-- Helper for Exercise 20: for `x ≠ 0`, the textbook identity `sin x / x = ∫_0^1 cos (s x) ds`
matches mathlib's interval-integral substitution API. -/
lemma exercise20_sin_div_eq_integral_cos_unit_interval
    {x : ℝ} (hx : x ≠ 0) :
    Real.sin x / x = ∫ s in (0 : ℝ)..1, Real.cos (s * x) := by
  -- Substitute `u = s x` into the elementary antiderivative of `cos`.
  have hmul :
      x * ∫ s in (0 : ℝ)..1, Real.cos (s * x) = ∫ u in (0 : ℝ)..x, Real.cos u := by
    simpa using (mul_integral_comp_mul_right (f := Real.cos) (a := (0 : ℝ)) (b := 1) x)
  have hcos : ∫ u in (0 : ℝ)..x, Real.cos u = Real.sin x := by
    simpa using (Real.integral_cos (a := (0 : ℝ)) (b := x))
  have hscaled : x * ∫ s in (0 : ℝ)..1, Real.cos (s * x) = Real.sin x := by
    rw [hmul, hcos]
  -- Divide the rescaled identity by `x`.
  apply (div_eq_iff hx).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled.symm

/-- Helper for Exercise 20: the tangent substitution on `(0, π / 2)` rewrites the normalized
quadratic kernel as an even cosine-power integral. -/
lemma exercise20_integral_inv_one_add_sq_pow_eq_cos_even_power
    (n : ℕ) (hn : 0 < n) :
    ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * (n - 1)) := by
  let s : Set ℝ := Set.Ioo (0 : ℝ) (Real.pi / 2)
  have hs_image : Real.tan '' s = Set.Ioi (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
    · intro hy
      refine ⟨Real.arctan y, ⟨Real.arctan_pos.mpr hy, Real.arctan_lt_pi_div_two y⟩, ?_⟩
      rw [Real.tan_arctan]
  have hderiv :
      ∀ θ ∈ s, HasDerivWithinAt Real.tan (1 / Real.cos θ ^ 2) s θ := by
    intro θ hθ
    -- Differentiate `tan` on the open interval where `cos θ > 0`.
    exact
      (Real.hasDerivAt_tan_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).hasDerivWithinAt
  have hinj : Set.InjOn Real.tan s := by
    intro x hx y hy hxy
    exact
      Real.injOn_tan
        ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
        ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩
        hxy
  have hchange :
      ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
        =
          ∫ θ in s,
            |(fun t : ℝ ↦ 1 / Real.cos t ^ 2) θ| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n) ∂volume := by
    rw [← hs_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  have hpoint :
      ∀ θ ∈ s, |1 / Real.cos θ ^ 2| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n)
          = Real.cos θ ^ (2 * (n - 1)) := by
    intro θ hθ
    have hcos_pos : 0 < Real.cos θ := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have hcos_ne : Real.cos θ ≠ 0 := hcos_pos.ne'
    have habs :
        |1 / Real.cos θ ^ 2| = 1 / Real.cos θ ^ 2 := by
      rw [abs_of_pos]
      positivity
    have hkernel : (1 + Real.tan θ ^ 2)⁻¹ = Real.cos θ ^ 2 := by
      simpa using Real.inv_one_add_tan_sq hcos_ne
    have hstep :
        (1 / Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ n = (Real.cos θ ^ 2) ^ (n - 1) := by
      have hn' : n = Nat.succ (n - 1) := by
        omega
      have hmul :
          (Real.cos θ ^ 2) ^ n = Real.cos θ ^ 2 * (Real.cos θ ^ 2) ^ (n - 1) := by
        rw [hn', pow_succ']
        simp
      rw [hmul]
      field_simp [pow_ne_zero 2 hcos_ne]
    -- After the Jacobian factor, only the even cosine power remains.
    calc
      |1 / Real.cos θ ^ 2| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n)
          = (1 / Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ n := by
              rw [habs, hkernel, smul_eq_mul]
      _ = (Real.cos θ ^ 2) ^ (n - 1) := hstep
      _ = Real.cos θ ^ (2 * (n - 1)) := by
            rw [pow_mul]
  -- Rewrite the image integral pointwise, then convert the open set integral to the interval form.
  calc
    ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
        =
          ∫ θ in s,
            |(fun t : ℝ ↦ 1 / Real.cos t ^ 2) θ| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n) ∂volume := hchange
    _ = ∫ θ in s, Real.cos θ ^ (2 * (n - 1)) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          exact hpoint θ hθ
    _ = ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), Real.cos θ ^ (2 * (n - 1)) ∂volume := by
          rw [integral_Ioc_eq_integral_Ioo]
    _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * (n - 1)) := by
          rw [intervalIntegral.integral_of_le]
          positivity

/-- Helper for Exercise 20: the even cosine-power integral on `[0, π / 2]` has the standard
central-binomial closed form. -/
lemma exercise20_integral_cos_even_power_centralBinom
    (m : ℕ) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * m)
      = Real.pi * (Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m + 1) := by
  have hprod :
      ∏ i ∈ Finset.range m, (2 * (i : ℝ) + 1) / (2 * i + 2)
        = (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m := by
    induction m with
    | zero =>
        simp
    | succ m hm =>
        rw [Finset.prod_range_succ, hm]
        have hcentral :
            ((m + 1 : ℝ) * (Nat.centralBinom (m + 1) : ℝ))
              = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
          exact_mod_cast Nat.succ_mul_centralBinom_succ m
        rw [pow_succ]
        field_simp
        nlinarith [hcentral]
  have hpow : (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m) := by
    calc
      (4 : ℝ) ^ m = ((2 : ℝ) ^ 2) ^ m := by norm_num
      _ = (2 : ℝ) ^ (2 * m) := by rw [pow_mul]
  -- Use the standard sine-power evaluation, then rewrite the Wallis product as a central binomial.
  calc
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * m)
        = (1 / 2 : ℝ) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (2 * m) := by
            rw [EulerSine.integral_cos_pow_eq]
    _ = (1 / 2 : ℝ) *
          (Real.pi * ∏ i ∈ Finset.range m, (2 * (i : ℝ) + 1) / (2 * i + 2)) := by
            rw [integral_sin_pow_even]
    _ = (1 / 2 : ℝ) * (Real.pi * ((Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m)) := by
          rw [hprod]
    _ = (1 / 2 : ℝ) * (Real.pi * ((Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m))) := by
          rw [hpow]
    _ = Real.pi * (Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m + 1) := by
          field_simp
          ring

/-- Exercise 20 (1): for `a, b > 0` and `n ≥ 1`,
evaluate `∫_0^∞ (a + b x^2)^{-n} dx` by residues. -/
theorem integral_inv_quadratic_pow
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
      = Real.pi * (Nat.centralBinom (n - 1) : ℝ) /
          ((2 : ℝ) ^ (2 * n - 1) * a ^ (n - 1) * Real.sqrt (a * b)) := by
  have hscale := exercise20_integral_inv_quadratic_pow_scaling a b n ha hb
  let m : ℕ := n - 1
  have hm : n = m + 1 := by
    -- Since `n > 0`, writing `n = (n - 1) + 1` keeps the final coefficient stable.
    omega
  have hsqrt_div : Real.sqrt (a / b) = Real.sqrt a / Real.sqrt b := by
    rw [Real.sqrt_div ha.le b]
  have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul ha.le b]
  have hsqrta_sq : Real.sqrt a * Real.sqrt a = a := by
    nlinarith [Real.sq_sqrt ha.le]
  have hsqrta_ne : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.2 ha
  have hsqrtb_ne : Real.sqrt b ≠ 0 := Real.sqrt_ne_zero'.2 hb
  have hcoeff :
      Real.sqrt (a / b) / a ^ n = 1 / (a ^ (n - 1) * Real.sqrt (a * b)) := by
    -- The outer scaling coefficient matches the target denominator after one square-root rewrite.
    rw [hsqrt_div, hsqrt_mul, hm, pow_succ]
    field_simp [hsqrta_ne, hsqrtb_ne, hsqrta_sq]
    simpa [pow_two, hsqrta_sq, mul_comm]
  -- Route correction: the remaining blocker is now exactly the normalized integral
  -- `∫_0^∞ (1 + y²)^(-n) dy`; the scaling and prefactor simplification are complete.
  have hnorm :
      ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
        = Real.pi * (Nat.centralBinom (n - 1) : ℝ) / (2 : ℝ) ^ (2 * n - 1) := by
    -- Close the normalized kernel by the tangent substitution and the even-power cosine integral.
    rw [exercise20_integral_inv_one_add_sq_pow_eq_cos_even_power n hn]
    have hexp : 2 * (n - 1) + 1 = 2 * n - 1 := by
      omega
    rw [← hexp]
    exact exercise20_integral_cos_even_power_centralBinom (n - 1)
  calc
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
        = (Real.sqrt (a / b) / a ^ n) *
            ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := hscale
    _ = (Real.sqrt (a / b) / a ^ n) *
          (Real.pi * (Nat.centralBinom (n - 1) : ℝ) / (2 : ℝ) ^ (2 * n - 1)) := by
            rw [hnorm]
    _ = (1 / (a ^ (n - 1) * Real.sqrt (a * b))) *
          (Real.pi * (Nat.centralBinom (n - 1) : ℝ) / (2 : ℝ) ^ (2 * n - 1)) := by
            rw [hcoeff]
    _ = Real.pi * (Nat.centralBinom (n - 1) : ℝ) /
          ((2 : ℝ) ^ (2 * n - 1) * a ^ (n - 1) * Real.sqrt (a * b)) := by
            rw [hsqrt_mul]
            field_simp [ha.ne', hsqrta_ne, hsqrtb_ne]

/-- Exercise 20 (2): for real `a` and `b`,
evaluate `∫_0^∞ (cos (2 a x) - cos (2 b x)) / x^2 dx` by residues. -/
theorem integral_cos_sub_cos_div_sq
    (a b : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), (Real.cos (2 * a * x) - Real.cos (2 * b * x)) / x ^ 2 ∂volume
      = Real.pi * (|b| - |a|) := by
  have hrewrite :
      ∫ x in Set.Ioi (0 : ℝ), (Real.cos (2 * a * x) - Real.cos (2 * b * x)) / x ^ 2 ∂volume
        =
          ∫ x in Set.Ioi (0 : ℝ),
            ((1 - Real.cos (2 * b * x)) - (1 - Real.cos (2 * a * x))) / x ^ 2 ∂volume := by
    -- This isolates the common kernel `J c = ∫ (1 - cos (2 c x)) / x²`.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simpa using exercise20_cos_sub_cos_div_sq_eq_kernel_difference a b x
  rw [hrewrite]
  have hsplit :
      ∫ x in Set.Ioi (0 : ℝ),
          ((1 - Real.cos (2 * b * x)) - (1 - Real.cos (2 * a * x))) / x ^ 2 ∂volume
        =
          ∫ x in Set.Ioi (0 : ℝ),
            (1 - Real.cos (2 * b * x)) / x ^ 2 - (1 - Real.cos (2 * a * x)) / x ^ 2 ∂volume := by
    -- Split the common denominator before using the two kernel evaluations.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp [hx0]
  rw [hsplit]
  -- Evaluate the rewritten difference as `J b - J a` using the shared kernel theorem.
  rw [integral_sub (exercise20_integrable_one_sub_cos_two_mul_div_sq b)
    (exercise20_integrable_one_sub_cos_two_mul_div_sq a)]
  rw [exercise20_integral_one_sub_cos_two_mul_div_sq,
    exercise20_integral_one_sub_cos_two_mul_div_sq]
  ring

/-- Helper for Exercise 20: after rewriting `sin x / x` as `sinc x` on the half-open interval,
the quadratic prefactor splits into the Dirichlet term minus the quadratic correction. -/
lemma exercise20_quadratic_ratio_mul_sinc_split
    (a x : ℝ) (hden : x ^ 2 + a ^ 2 ≠ 0) :
    ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * Real.sinc x =
      Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)) := by
  -- This is the same algebraic split as the textbook route, but written in the `sinc` model that
  -- is continuous at `0` and therefore stable under interval-integral decomposition.
  field_simp [hden]
  ring

/-- Helper for Exercise 20: the correction kernel is dominated by the integrable quadratic tail on
`(0, ∞)`. -/
lemma exercise20_integrable_inv_quadratic
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ 2 + a ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) := by
  have hmajorant_base :
      IntegrableOn (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
    integrable_inv_one_add_sq.integrableOn
  have hmajorant_scaled :
      IntegrableOn (fun x : ℝ ↦ (1 + (x * a⁻¹) ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) := by
    -- Positive scaling preserves the normalized Cauchy tail on `(0, ∞)`.
    have hmajorant_base' :
        IntegrableOn (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) (Set.Ioi ((0 : ℝ) * a⁻¹)) := by
      simpa [zero_mul] using hmajorant_base
    simpa [zero_mul] using
      (integrableOn_Ioi_comp_mul_right_iff
        (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) (0 : ℝ) (a := a⁻¹) (inv_pos.mpr ha)).2 hmajorant_base'
  have hscaled_const :
      IntegrableOn (fun x : ℝ ↦ (a⁻¹ ^ 2) * (1 + (x * a⁻¹) ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
    hmajorant_scaled.const_mul _
  have hEq :
      Set.EqOn
        (fun x : ℝ ↦ (x ^ 2 + a ^ 2)⁻¹)
        (fun x : ℝ ↦ (a⁻¹ ^ 2) * (1 + (x * a⁻¹) ^ 2)⁻¹)
        (Set.Ioi (0 : ℝ)) := by
    intro x hx
    have hden :
        x ^ 2 + a ^ 2 = a ^ 2 * (1 + (x * a⁻¹) ^ 2) := by
      field_simp [ha.ne']
      ring
    -- Rewrite the denominator into the normalized `1 + (x / a)^2` shape.
    calc
      (x ^ 2 + a ^ 2)⁻¹ = (a ^ 2 * (1 + (x * a⁻¹) ^ 2))⁻¹ := by rw [hden]
      _ = (1 + (x * a⁻¹) ^ 2)⁻¹ * (a ^ 2)⁻¹ := by rw [mul_inv_rev]
      _ = (a ^ 2)⁻¹ * (1 + (x * a⁻¹) ^ 2)⁻¹ := by rw [mul_comm]
      _ = (a⁻¹ ^ 2) * (1 + (x * a⁻¹) ^ 2)⁻¹ := by
            simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]
  exact (integrableOn_congr_fun hEq measurableSet_Ioi).2 hscaled_const

/-- Helper for Exercise 20: the correction kernel is dominated by the integrable quadratic tail on
`(0, ∞)`. -/
lemma exercise20_integrable_sinc_over_quadratic
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ Real.sinc x / (x ^ 2 + a ^ 2)) (Set.Ioi (0 : ℝ)) := by
  have hmajorant :
      IntegrableOn (fun x : ℝ ↦ (x ^ 2 + a ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
    exercise20_integrable_inv_quadratic a ha
  have hcont :
      Continuous fun x : ℝ ↦ Real.sinc x / (x ^ 2 + a ^ 2) := by
    -- The denominator never vanishes because `a > 0`.
    refine Real.continuous_sinc.div ?_ ?_
    · continuity
    · intro x
      have hpos : 0 < x ^ 2 + a ^ 2 := by positivity
      exact hpos.ne'
  -- Dominate `|sinc x| / (x² + a²)` by the quadratic tail.
  rw [IntegrableOn] at hmajorant ⊢
  refine Integrable.mono' hmajorant hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hden_pos : 0 < x ^ 2 + a ^ 2 := by positivity
  have hden_nonneg : 0 ≤ (x ^ 2 + a ^ 2)⁻¹ := inv_nonneg.mpr hden_pos.le
  calc
    ‖Real.sinc x / (x ^ 2 + a ^ 2)‖
        = |Real.sinc x| * (x ^ 2 + a ^ 2)⁻¹ := by
            rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos, div_eq_mul_inv]
    _ ≤ 1 * (x ^ 2 + a ^ 2)⁻¹ := by
          exact mul_le_mul_of_nonneg_right (Real.abs_sinc_le_one x) hden_nonneg
    _ = (x ^ 2 + a ^ 2)⁻¹ := by ring

/-- Helper for Exercise 20: once the cosine-over-quadratic kernel is known on `[0, 1]`, the
source `sinc x = ∫_0^1 cos (s x) ds` identity and Fubini finish the correction term. -/
lemma exercise20_integral_sinc_over_quadratic_of_cos_kernel
    (a : ℝ) (ha : 0 < a)
    (hcos :
      ∀ s ∈ Set.uIcc (0 : ℝ) 1,
        ∫ x in Set.Ioi (0 : ℝ), Real.cos (s * x) / (x ^ 2 + a ^ 2) ∂volume =
          Real.pi * Real.exp (-a * s) / (2 * a)) :
    ∫ x in Set.Ioi (0 : ℝ), Real.sinc x / (x ^ 2 + a ^ 2) ∂volume
      = Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2) := by
  let f : ℝ → ℝ → ℝ := fun s x ↦ Real.cos (s * x) / (x ^ 2 + a ^ 2)
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    simp
  have hmajorant :
      Integrable (fun z : ℝ × ℝ ↦ ((z.2 ^ 2 + a ^ 2)⁻¹ : ℝ))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hquad :
        Integrable (fun x : ℝ ↦ (x ^ 2 + a ^ 2)⁻¹) (volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa [IntegrableOn] using exercise20_integrable_inv_quadratic a ha
    simpa using hquad.comp_snd (volume.restrict (Set.uIoc (0 : ℝ) 1))
  have hcont :
      Continuous fun z : ℝ × ℝ ↦ f z.1 z.2 := by
    -- The Fubini integrand is continuous because the quadratic denominator stays positive.
    refine Continuous.div ?_ ?_ ?_
    · simpa [f] using (Real.continuous_cos.comp (continuous_fst.mul continuous_snd))
    · simpa using (continuous_snd.pow 2).add continuous_const
    · intro z
      have hpos : 0 < z.2 ^ 2 + a ^ 2 := by positivity
      simpa [f] using hpos.ne'
  have hkernel_int :
      Integrable (fun z : ℝ × ℝ ↦ f z.1 z.2)
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    refine Integrable.mono' hmajorant hcont.aestronglyMeasurable ?_
    filter_upwards with z
    have hden_pos : 0 < z.2 ^ 2 + a ^ 2 := by positivity
    have hden_nonneg : 0 ≤ (z.2 ^ 2 + a ^ 2)⁻¹ := inv_nonneg.mpr hden_pos.le
    calc
      ‖f z.1 z.2‖ = |Real.cos (z.1 * z.2)| * (z.2 ^ 2 + a ^ 2)⁻¹ := by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos, div_eq_mul_inv]
      _ ≤ 1 * (z.2 ^ 2 + a ^ 2)⁻¹ := by
            exact mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (z.1 * z.2)) hden_nonneg
      _ = (z.2 ^ 2 + a ^ 2)⁻¹ := by ring
  have hsinc_eq :
      ∫ x in Set.Ioi (0 : ℝ), Real.sinc x / (x ^ 2 + a ^ 2) ∂volume
        = ∫ x in Set.Ioi (0 : ℝ), ∫ s in (0 : ℝ)..1, f s x ∂volume := by
    -- Replace `sinc` by the textbook unit-interval cosine average before swapping integrals.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    symm
    calc
      ∫ s in (0 : ℝ)..1, f s x
          = (∫ s in (0 : ℝ)..1, Real.cos (s * x)) / (x ^ 2 + a ^ 2) := by
              simpa [f] using
                (intervalIntegral.integral_div (r := x ^ 2 + a ^ 2)
                  (f := fun s : ℝ ↦ Real.cos (s * x)))
      _ = (Real.sin x / x) / (x ^ 2 + a ^ 2) := by
            rw [exercise20_sin_div_eq_integral_cos_unit_interval hx0]
      _ = Real.sinc x / (x ^ 2 + a ^ 2) := by
            rw [Real.sinc_of_ne_zero hx0]
  have hswap :
      ∫ x in Set.Ioi (0 : ℝ), ∫ s in (0 : ℝ)..1, f s x ∂volume
        = ∫ s in (0 : ℝ)..1, ∫ x in Set.Ioi (0 : ℝ), f s x ∂volume := by
    -- The source route now reduces to a single Fubini swap on `[0, 1] × (0, ∞)`.
    simpa [f] using
      (MeasureTheory.intervalIntegral_integral_swap
        (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := f) hkernel_int).symm
  have hexp :
      ∫ s in (0 : ℝ)..1, Real.exp (-a * s) = (1 - Real.exp (-a)) / a := by
    have hscale :
        ∫ s in (0 : ℝ)..1, Real.exp (-a * s)
          = (-a)⁻¹ * ∫ u in (-a) * (0 : ℝ)..(-a) * 1, Real.exp u := by
      simpa [smul_eq_mul] using
        (intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := (0 : ℝ))
          (b := 1) (c := -a) (neg_ne_zero.mpr ha.ne'))
    -- A linear substitution evaluates the remaining exponential integral explicitly.
    calc
      ∫ s in (0 : ℝ)..1, Real.exp (-a * s)
          = (-a)⁻¹ * ∫ u in (-a) * (0 : ℝ)..(-a) * 1, Real.exp u := hscale
      _ = (-a)⁻¹ * (Real.exp (-a) - 1) := by
            rw [mul_zero, mul_one, integral_exp, Real.exp_zero]
      _ = (1 - Real.exp (-a)) / a := by
            field_simp [ha.ne']
            ring
  calc
    ∫ x in Set.Ioi (0 : ℝ), Real.sinc x / (x ^ 2 + a ^ 2) ∂volume
        = ∫ x in Set.Ioi (0 : ℝ), ∫ s in (0 : ℝ)..1, f s x ∂volume := hsinc_eq
    _ = ∫ s in (0 : ℝ)..1, ∫ x in Set.Ioi (0 : ℝ), f s x ∂volume := hswap
    _ = ∫ s in (0 : ℝ)..1, Real.pi * Real.exp (-a * s) / (2 * a) := by
          apply intervalIntegral.integral_congr
          intro s hs
          exact hcos s hs
    _ = (Real.pi / (2 * a)) * ∫ s in (0 : ℝ)..1, Real.exp (-a * s) := by
          have hconst :
              ∀ s : ℝ,
                Real.pi * Real.exp (-a * s) / (2 * a) =
                  (Real.pi / (2 * a)) * Real.exp (-a * s) := by
            intro s
            field_simp [ha.ne']
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro s hs
          exact hconst s
    _ = (Real.pi / (2 * a)) * ((1 - Real.exp (-a)) / a) := by rw [hexp]
    _ = Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2) := by
          calc
            (Real.pi / (2 * a)) * ((1 - Real.exp (-a)) / a)
                = Real.pi * (1 - Real.exp (-a)) / ((2 * a) * a) := by
                    field_simp [ha.ne']
            _ = Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2) := by ring

/-- Helper for Exercise 20: the quadratic Cauchy kernel is integrable on the whole real line. -/
lemma exercise20_integrable_inv_quadratic_univ
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ (x ^ 2 + a ^ 2)⁻¹) := by
  have hbase : Integrable (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hscaled : Integrable (fun x : ℝ ↦ (1 + (x * a⁻¹) ^ 2)⁻¹) := by
    -- The normalized whole-line kernel stays integrable after the positive scaling `x ↦ x / a`.
    simpa using
      (integrable_comp_mul_right_iff (g := fun x : ℝ ↦ (1 + x ^ 2)⁻¹)
        (R := a⁻¹) (inv_ne_zero ha.ne')).2 hbase
  have hconst :
      Integrable (fun x : ℝ ↦ (a⁻¹ ^ 2) * (1 + (x * a⁻¹) ^ 2)⁻¹) :=
    hscaled.const_mul _
  refine Integrable.congr hconst ?_
  filter_upwards with x
  have hden :
      x ^ 2 + a ^ 2 = a ^ 2 * (1 + (x * a⁻¹) ^ 2) := by
    field_simp [ha.ne']
    ring
  -- Rewrite the denominator into the normalized `1 + (x / a)^2` form used by the base kernel.
  symm
  calc
    (x ^ 2 + a ^ 2)⁻¹ = (a ^ 2 * (1 + (x * a⁻¹) ^ 2))⁻¹ := by rw [hden]
    _ = (1 + (x * a⁻¹) ^ 2)⁻¹ * (a ^ 2)⁻¹ := by rw [mul_inv_rev]
    _ = (a ^ 2)⁻¹ * (1 + (x * a⁻¹) ^ 2)⁻¹ := by rw [mul_comm]
    _ = (a⁻¹ ^ 2) * (1 + (x * a⁻¹) ^ 2)⁻¹ := by
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 20: the remaining source-faithful contour step is the whole-line unit
frequency kernel from Proposition 3.1. -/
lemma exercise20_integral_univ_exp_mul_inv_quadratic_unit_freq
    (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * x) =
      (Real.pi * Real.exp (-a) / a : ℂ) := by
  -- TODO: apply Proposition 3.1 to `f z = (z^2 + a^2)⁻¹`, isolate the unique upper-half-plane pole
  -- at `z = a * I`, compute its residue as `exp (-a) / (2 a I)`, and then simplify the residue sum.
  -- Route correction: the scaling/real-part/evenness adapters are now separated below, so this
  -- theorem is the only remaining contour-residue blocker.
  sorry

/-- Helper for Exercise 20: once the unit-frequency contour kernel is known, a positive dilation
transfers it to all `s > 0` on the whole line. -/
lemma exercise20_integral_univ_exp_mul_inv_quadratic_pos_freq
    (a s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x)) =
      (Real.pi * Real.exp (-a * s) / a : ℂ) := by
  -- TODO: scale the unit-frequency whole-line kernel by `y = s x`, rewrite
  -- `((x * s)^2 + (a * s)^2)` as `s^2 (x^2 + a^2)`, and simplify the resulting scalar factor by
  -- a single use of `exercise20_integral_univ_exp_mul_inv_quadratic_unit_freq (a * s)`.
  sorry

/-- Helper for Exercise 20: the oscillatory quadratic kernel is integrable on the whole line, so
`Complex.re` may be commuted through its integral. -/
lemma exercise20_integrable_exp_mul_inv_quadratic_univ
    (a s : ℝ) (ha : 0 < a) :
    Integrable
      (fun x : ℝ ↦
        ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x))) := by
  have hbase :
      Integrable (fun x : ℝ ↦ ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹)) := by
    -- The real quadratic majorant is already integrable, and complexification preserves that.
    refine Integrable.congr (exercise20_integrable_inv_quadratic_univ a ha).ofReal ?_
    filter_upwards with x
    simp
  have hcont : Continuous fun x : ℝ ↦ Complex.exp (Complex.I * (s * x)) := by
    -- The oscillatory factor is continuous on the whole real line.
    fun_prop
  -- The exponential factor has constant norm `1`, so the quadratic kernel still dominates.
  refine hbase.mul_bdd (c := 1) hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hnorm : ‖Complex.exp (Complex.I * (s * x))‖ = 1 := by
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (s * x)
  exact le_of_eq hnorm

/-- Helper for Exercise 20: after the whole-line residue computation, taking real parts and using
evenness halves the cosine kernel to the positive half-line. -/
lemma exercise20_integral_cos_mul_inv_quadratic_positive_freq
    (a s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (s * x) / (x ^ 2 + a ^ 2) ∂volume
      = Real.pi * Real.exp (-a * s) / (2 * a) := by
  -- TODO: commute `Complex.re` through the whole-line identity from
  -- `exercise20_integral_univ_exp_mul_inv_quadratic_pos_freq`, rewrite the resulting real kernel
  -- as `x ↦ cos (s x) / (x^2 + a^2)`, and then use evenness plus
  -- `integral_Iic_add_Ioi` / `integral_comp_neg_Iic` to halve the full-line integral.
  sorry

/-- Helper for Exercise 20: the zero-frequency cosine kernel already follows from part (1), so the
remaining contour work is only the positive-frequency residue computation. -/
lemma exercise20_integral_cos_mul_inv_quadratic_nonneg_freq
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (s * x) / (x ^ 2 + a ^ 2) ∂volume
      = Real.pi * Real.exp (-a * s) / (2 * a) := by
  by_cases hs0 : s = 0
  · -- At frequency `0`, the cosine kernel is exactly the `n = 1` quadratic integral from part (1).
    subst hs0
    calc
      ∫ x in Set.Ioi (0 : ℝ), Real.cos ((0 : ℝ) * x) / (x ^ 2 + a ^ 2) ∂volume
          = ∫ x in Set.Ioi (0 : ℝ), (a ^ 2 + 1 * x ^ 2)⁻¹ ^ 1 ∂volume := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              simp [pow_one, add_comm, add_left_comm, add_assoc]
      _ = Real.pi * (Nat.centralBinom (1 - 1) : ℝ) /
            ((2 : ℝ) ^ (2 * 1 - 1) * (a ^ 2) ^ (1 - 1) * Real.sqrt (a ^ 2 * 1)) := by
            simpa using
              (integral_inv_quadratic_pow (a := a ^ 2) (b := 1) (n := 1)
                (by positivity) (by positivity) (by norm_num : 0 < (1 : ℕ)))
      _ = Real.pi * Real.exp (-a * (0 : ℝ)) / (2 * a) := by
            simp [Real.sqrt_sq_eq_abs, abs_of_pos ha, ha.ne']
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (by simpa [eq_comm] using hs0)
    -- Route correction: the remaining contour work has been isolated in the unit-frequency kernel,
    -- and the `s > 0` branch is now only the already-packaged scaling plus evenness adapter.
    exact exercise20_integral_cos_mul_inv_quadratic_positive_freq a s ha hs_pos

/-- Helper for Exercise 20: the source correction term is the set integral behind the improper
limit. -/
lemma exercise20_integral_sinc_over_quadratic
    (a : ℝ) (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), Real.sinc x / (x ^ 2 + a ^ 2) ∂volume
      = Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2) := by
  -- Route correction: the source-faithful Fubini reduction is now complete, so the target depends
  -- only on the narrower cosine-kernel residue theorem above.
  refine exercise20_integral_sinc_over_quadratic_of_cos_kernel a ha ?_
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using hs
  exact exercise20_integral_cos_mul_inv_quadratic_nonneg_freq a s ha hs'.1

/-- Helper for Exercise 20: once the set-integral correction term is evaluated, the improper
interval limit follows from the standard `Ioi`-integral convergence theorem. -/
lemma exercise20_tendsto_intervalIntegral_sinc_over_quadratic
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun R : ℝ ↦
        ∫ x in (0 : ℝ)..R, Real.sinc x / (x ^ 2 + a ^ 2))
      atTop
      (𝓝 (Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2))) := by
  have hfi := exercise20_integrable_sinc_over_quadratic a ha
  have hlimit :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume) (f := fun x : ℝ ↦ Real.sinc x / (x ^ 2 + a ^ 2))
      (a := (0 : ℝ)) (b := fun R : ℝ ↦ R) hfi tendsto_id
  -- Route correction: the improper-limit adapter is no longer the blocker; only the exact set
  -- integral `exercise20_integral_sinc_over_quadratic` remains.
  simpa [exercise20_integral_sinc_over_quadratic a ha] using hlimit

/-- Exercise 20 (3): for `a > 0`, evaluate the conditionally convergent improper integral
`∫_0^∞ ((x^2 - a^2) / (x^2 + a^2)) (sin x / x) dx` by residues. The source integral is stated as
an interval-integral limit rather than a Lebesgue integral over `Set.Ioi`, since the integrand is
not absolutely integrable. -/
theorem integral_quadratic_ratio_mul_sin_div
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun R : ℝ ↦
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x))
      atTop
      (𝓝 (Real.pi * Real.exp (-a) - Real.pi / 2)) := by
  have ha2_ne : a ^ 2 ≠ 0 := by exact pow_ne_zero 2 ha.ne'
  have hsinc_limit :
      Tendsto (fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, Real.sinc x) atTop (𝓝 (Real.pi / 2)) := by
    have hEq :
        (fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, Real.sin x / x) =ᶠ[atTop]
          fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, Real.sinc x := by
      -- On the eventual positive tail, the imported `sin x / x = sinc x` interval identity
      -- rewrites the Dirichlet term to the continuous model.
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact intervalIntegral_sin_div_eq_intervalIntegral_sinc hR
    exact Tendsto.congr' hEq tendsto_intervalIntegral_sin_div_eq_pi_half
  have hsplit_limit :
      Tendsto
        (fun R : ℝ ↦
          ∫ x in (0 : ℝ)..R,
            Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)))
        atTop
        (𝓝 (Real.pi * Real.exp (-a) - Real.pi / 2)) := by
    have hcorr :=
      exercise20_tendsto_intervalIntegral_sinc_over_quadratic a ha
    have hsub :
        Tendsto
          (fun R : ℝ ↦
            (∫ x in (0 : ℝ)..R, Real.sinc x) -
              (2 * a ^ 2) * (∫ x in (0 : ℝ)..R, Real.sinc x / (x ^ 2 + a ^ 2)))
          atTop
          (𝓝 ((Real.pi / 2) -
            (2 * a ^ 2) * (Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2)))) :=
      hsinc_limit.sub ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (2 * a ^ 2)) atTop
        (𝓝 (2 * a ^ 2))).mul hcorr)
    have hcont_corr :
        Continuous fun x : ℝ ↦ Real.sinc x / (x ^ 2 + a ^ 2) := by
      -- The `sinc` model is continuous, and the quadratic denominator stays positive for `a > 0`.
      refine Real.continuous_sinc.div ?_ ?_
      · continuity
      · intro x
        have hpos : 0 < x ^ 2 + a ^ 2 := by positivity
        exact hpos.ne'
    have hinterval_eq :
        (fun R : ℝ ↦
          ∫ x in (0 : ℝ)..R,
            Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2))) =
          fun R : ℝ ↦
            (∫ x in (0 : ℝ)..R, Real.sinc x) -
              (2 * a ^ 2) * (∫ x in (0 : ℝ)..R, Real.sinc x / (x ^ 2 + a ^ 2)) := by
      -- Split the interval integral once the two summands are known to be interval integrable.
      funext R
      have hsinc_int : IntervalIntegrable Real.sinc volume (0 : ℝ) R :=
        Real.continuous_sinc.intervalIntegrable _ _
      have hscaled_int :
          IntervalIntegrable
            (fun x : ℝ ↦ (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)))
            volume (0 : ℝ) R :=
        (continuous_const.mul hcont_corr).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hsinc_int hscaled_int, intervalIntegral.integral_const_mul]
    have hconst :
        (Real.pi / 2) - (2 * a ^ 2) * (Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2)) =
          Real.pi * Real.exp (-a) - Real.pi / 2 := by
      field_simp [ha2_ne]
      ring
    -- Combine the Dirichlet limit with the correction-kernel limit, then normalize the constant.
    simpa [hinterval_eq, hconst] using hsub
  have hraw_eq :
      (fun R : ℝ ↦
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x)) =ᶠ[atTop]
        fun R : ℝ ↦
          ∫ x in (0 : ℝ)..R,
            Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hto_sinc :
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x)
          =
            ∫ x in (0 : ℝ)..R,
              ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * Real.sinc x := by
      -- For `R > 0`, the unordered interval is `Ioc 0 R`, so it excludes `0`; there the raw
      -- quotient and `sinc` agree pointwise.
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall <| fun x hx ↦ by
        rw [Set.uIoc_of_le hR.le, Set.mem_Ioc] at hx
        have hx0 : x ≠ 0 := by linarith
        rw [Real.sinc_of_ne_zero hx0]
    have hsinc_split :
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * Real.sinc x
          =
            ∫ x in (0 : ℝ)..R,
              Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)) := by
      -- With `sinc`, the algebraic split holds pointwise on the whole interval, including `0`.
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall <| fun x hx ↦ by
        have hden : x ^ 2 + a ^ 2 ≠ 0 := by
          have hpos : 0 < x ^ 2 + a ^ 2 := by positivity
          exact hpos.ne'
        exact exercise20_quadratic_ratio_mul_sinc_split a x hden
    exact hto_sinc.trans hsinc_split
  -- Route correction: the main theorem is now reduced to the single source-faithful blocker
  -- `exercise20_tendsto_intervalIntegral_sinc_over_quadratic`.
  exact Tendsto.congr' hraw_eq.symm hsplit_limit

/-- Exercise 20 (4): if `|a| < 1`, then
`∫_0^π cos (n t) / (1 - 2 a cos t + a^2) dt = π a^n / (1 - a^2)`. -/
theorem integral_cos_nat_mul_div_poisson_kernel_lt_one
    (a : ℝ) (n : ℕ) (ha : |a| < 1) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
      = Real.pi * a ^ n / (1 - a ^ 2) := by
  have hne : |a| ≠ 1 := ne_of_lt ha
  have hden : 1 - a ^ 2 ≠ 0 := by
    intro hzero
    have hsquare : a ^ 2 = 1 := by linarith
    have habs_sq : |a| ^ 2 = 1 := by simpa [sq_abs] using hsquare
    have habs : |a| = 1 := by
      have habs_nonneg : 0 ≤ |a| := abs_nonneg a
      nlinarith
    exact hne habs
  have havg := exercise20_poisson_average_fourier_mode (a := a) (n := n) ha
  -- The Poisson average is already the desired scalar multiple of the cosine integral.
  rw [exercise20_poisson_circleAverage_eq_intervalIntegral (a := a) (n := n) hne] at havg
  apply (eq_div_iff hden).2
  have hmul := congrArg (fun x : ℝ ↦ Real.pi * x) havg
  field_simp [hden, Real.pi_ne_zero] at hmul ⊢
  linarith

/-- Exercise 20 (5): if `1 < |a|`, then
`∫_0^π cos (n t) / (1 - 2 a cos t + a^2) dt = π / (a^n (a^2 - 1))`. -/
theorem integral_cos_nat_mul_div_poisson_kernel_gt_one
    (a : ℝ) (n : ℕ) (ha : 1 < |a|) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
      = Real.pi / (a ^ n * (a ^ 2 - 1)) := by
  have ha0 : a ≠ 0 := by
    intro hzero
    have : (1 : ℝ) < 0 := by simpa [hzero] using ha
    linarith
  have hainv : |a⁻¹| < 1 := by
    simpa [abs_inv] using (inv_lt_one_of_one_lt₀ ha)
  have hrewrite :
      ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
        = (a ^ 2)⁻¹ *
            ∫ t in (0 : ℝ)..Real.pi,
              Real.cos (n * t) / (1 - 2 * a⁻¹ * Real.cos t + (a ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
    field_simp [ha0, ha2]
    ring
  -- Reduce to the `|a| < 1` case by factoring out `a²` from the denominator.
  rw [hrewrite]
  have hsq : (a ^ 2)⁻¹ = a⁻¹ ^ 2 := by
    field_simp [ha0]
  rw [hsq, integral_cos_nat_mul_div_poisson_kernel_lt_one (a := a⁻¹) (n := n) hainv]
  field_simp [ha0]
  have hpowcancel : (1 / a) ^ n * a ^ n = 1 := by
    simp [ha0]
  rw [hpowcancel, one_div]
