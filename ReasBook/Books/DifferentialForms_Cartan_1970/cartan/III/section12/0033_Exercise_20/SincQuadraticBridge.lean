import Mathlib
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import DifferentialForms_Cartan_1970.cartan.III.section12.«0008_Example_III_6_extra_3»

open MeasureTheory
open InnerProductSpace
open Filter
open scoped Real Topology

noncomputable section

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
