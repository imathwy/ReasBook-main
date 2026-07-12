import Mathlib
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import DifferentialForms_Cartan_1970.III.section12.«0008_Example_III_6_extra_3»

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
