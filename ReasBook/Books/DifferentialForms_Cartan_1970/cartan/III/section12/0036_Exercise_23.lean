import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Real

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the improper-integral notation and real-power API were checked directly against local mathlib
-- Gamma/Beta integral files and nearby section precedent.

/-- Helper for Exercise 23: substituting `y = x ^ n` reduces the `1 + x ^ n` kernel to the
standard `1 + y` kernel. -/
lemma integral_rpow_div_one_add_pow_eq_scaled_integral_pow_sub_one_div_one_add
    (n : ℕ) (α : ℝ) (hn0 : 0 < (n : ℝ)) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ α / (1 + x ^ n) ∂volume =
      (1 / (n : ℝ)) *
        ∫ y in Set.Ioi (0 : ℝ), y ^ (((1 + α) / (n : ℝ)) - 1) / (1 + y) ∂volume := by
  let s : ℝ := (1 + α) / (n : ℝ)
  -- We match the integrand to the standard `x ↦ x ^ n` change-of-variables formula.
  calc
    ∫ x in Set.Ioi (0 : ℝ), x ^ α / (1 + x ^ n) ∂volume
        = ∫ y in Set.Ioi (0 : ℝ), ((n : ℝ)⁻¹) * (y ^ (s - 1) / (1 + y)) ∂volume := by
            rw [← integral_comp_rpow_Ioi_of_pos
              (g := fun y : ℝ ↦ ((n : ℝ)⁻¹) * (y ^ (s - 1) / (1 + y))) hn0]
            refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
            have hx0 : 0 < x := hx
            -- The derivative factor `n * x^(n-1)` combines with `(x^n)^(s-1)` to recover `x^α`.
            simp only [smul_eq_mul]
            have hxpow : 0 < 1 + x ^ (n : ℝ) := by positivity
            have hcancel :
                (n : ℝ) * x ^ ((n : ℝ) - 1) *
                    ((n : ℝ)⁻¹ * ((x ^ (n : ℝ)) ^ (s - 1) / (1 + x ^ (n : ℝ)))) =
                  x ^ ((n : ℝ) - 1) * ((x ^ (n : ℝ)) ^ (s - 1) / (1 + x ^ (n : ℝ))) := by
              field_simp [hxpow.ne', show (n : ℝ) ≠ 0 by positivity]
            rw [hcancel, ← Real.rpow_mul (le_of_lt hx0)]
            simp only [div_eq_mul_inv]
            rw [← mul_assoc, ← Real.rpow_add hx0]
            congr 1
            · have hnne : (n : ℝ) ≠ 0 := by positivity
              have hexp :
                  α = -1 + (n : ℝ) * α * (n : ℝ)⁻¹ + (n : ℝ) * (n : ℝ)⁻¹ := by
                field_simp [hnne]
                ring
              rw [hexp]
              congr 1
              simp [s]
              field_simp [hnne]
              ring
            · simp
    _ = (1 / (n : ℝ)) *
          ∫ y in Set.Ioi (0 : ℝ), y ^ (((1 + α) / (n : ℝ)) - 1) / (1 + y) ∂volume := by
          rw [integral_const_mul]
          simp [s, one_div]

/-- Helper for Exercise 23: the reduced `1 + x` kernel is the real Beta integral
`Β(s, 1 - s)` when `0 < s < 1`. -/
lemma integral_pow_sub_one_div_one_add_eq_beta
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) / (1 + x) ∂volume =
      ProbabilityTheory.beta s (1 - s) := by
  let f : ℝ → ℝ := fun x ↦ x / (1 + x)
  have hf_deriv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (1 / (1 + x) ^ 2) (Set.Ioi 0) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hx1 : 0 < 1 + x := by linarith
    have hsum : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) + y) 1 x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    simpa [f, pow_two] using ((hasDerivAt_id x).div hsum hx1.ne').hasDerivWithinAt
  have hf_inj : Set.InjOn f (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    have hx1 : 1 + x ≠ 0 := by nlinarith
    have hy1 : 1 + y ≠ 0 := by nlinarith
    dsimp [f] at hxy
    field_simp [f, hx1, hy1] at hxy
    linarith
  have hf_image : f '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : 0 < x := hx
      have hx1 : 0 < 1 + x := by nlinarith
      constructor
      · exact div_pos hx0 hx1
      · rw [div_lt_one hx1]
        linarith
    · intro hy
      refine ⟨y / (1 - y), ?_, ?_⟩
      · have hy1pos : 0 < 1 - y := sub_pos.mpr hy.2
        exact div_pos hy.1 hy1pos
      · have hy1pos : 0 < 1 - y := sub_pos.mpr hy.2
        have hy1 : 1 - y ≠ 0 := hy1pos.ne'
        dsimp [f]
        field_simp [hy1]
        ring_nf
  calc
    ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) / (1 + x) ∂volume
        = ∫ y in Set.Ioo (0 : ℝ) 1, y ^ (s - 1) * (1 - y) ^ ((1 - s) - 1) ∂volume := by
            rw [← hf_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf_deriv
              hf_inj]
            refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
            have hx0 : 0 < x := hx
            have hx1 : 0 < 1 + x := by nlinarith
            have hsub : 1 - x / (1 + x) = (1 + x)⁻¹ := by
              field_simp [hx1.ne']
              ring
            have hs : ((1 - s) - 1 : ℝ) = -s := by ring
            have hpow : (1 + x) ^ s / (1 + x) ^ (s - 1) = 1 + x := by
              rw [← Real.rpow_sub hx1, sub_sub_cancel, Real.rpow_one]
            symm
            rw [smul_eq_mul, abs_of_pos (by positivity), Real.div_rpow hx0.le hx1.le, hsub, hs,
              Real.rpow_neg_eq_inv_rpow, inv_inv]
            calc
              (1 / (1 + x) ^ 2) * (x ^ (s - 1) / (1 + x) ^ (s - 1) * (1 + x) ^ s)
                  = (1 / (1 + x) ^ 2) * (x ^ (s - 1) * ((1 + x) ^ s / (1 + x) ^ (s - 1))) := by
                      ring
              _ = (1 / (1 + x) ^ 2) * (x ^ (s - 1) * (1 + x)) := by rw [hpow]
              _ = x ^ (s - 1) / (1 + x) := by
                    field_simp [hx1.ne']
    _ = (Complex.betaIntegral s (1 - s)).re := by
          rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
            ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
          · refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
            norm_cast
            rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
              Complex.re_mul_ofReal, Complex.ofReal_re]
            all_goals nlinarith [hx.1, hx.2]
          · convert! Complex.betaIntegral_convergent (u := s) (v := 1 - s) (by simpa)
              (by simpa using sub_pos.mpr hs1) using 1
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
    _ = ProbabilityTheory.beta s (1 - s) := by
          simpa using (ProbabilityTheory.beta_eq_betaIntegralReal s (1 - s) hs0
            (sub_pos.mpr hs1)).symm

/-- Helper for Exercise 23: Euler's reflection formula evaluates the reduced `1 + x` kernel. -/
lemma integral_pow_sub_one_div_one_add
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) / (1 + x) ∂volume =
      Real.pi / Real.sin (Real.pi * s) := by
  -- Once the kernel is identified with the Beta function, the reflection formula closes it.
  rw [integral_pow_sub_one_div_one_add_eq_beta s hs0 hs1, ProbabilityTheory.beta,
    show s + (1 - s) = 1 by ring, Real.Gamma_one, div_one, Real.Gamma_mul_Gamma_one_sub]

/-- Exercise 23 (2): for a natural number `n` and a real number `α` with `0 < 1 + α < n`,
`∫_0^∞ x^α / (1 + x^n) dx = (π / n) / sin (π (1 + α) / n)`. -/
theorem integral_rpow_div_one_add_pow
    (n : ℕ) (α : ℝ)
    (hα_left : 0 < 1 + α) (hα_right : 1 + α < (n : ℝ)) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ α / (1 + x ^ n) ∂volume =
      (Real.pi / (n : ℝ)) / Real.sin (Real.pi * (1 + α) / (n : ℝ)) := by
  let s : ℝ := (1 + α) / (n : ℝ)
  have hn0 : 0 < (n : ℝ) := by linarith
  have hs0 : 0 < s := by
    exact div_pos hα_left hn0
  have hs1 : s < 1 := by
    simpa [s] using (div_lt_one hn0).2 (by simpa using hα_right)
  -- The source proof first reduces to the `1 + x` kernel, then evaluates it by Beta/Gamma.
  rw [integral_rpow_div_one_add_pow_eq_scaled_integral_pow_sub_one_div_one_add n α hn0,
    integral_pow_sub_one_div_one_add s hs0 hs1]
  simp [s, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Exercise 23 (1): for a natural number `n ≥ 2`,
`∫_0^∞ dx / (1 + x^n) = (π / n) / sin (π / n)`. This is the case `α = 0` of
`integral_rpow_div_one_add_pow`. -/
theorem integral_inv_one_add_pow
    (n : ℕ) (hn : 2 ≤ n) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x ^ n) ∂volume =
      (Real.pi / (n : ℝ)) / Real.sin (Real.pi / (n : ℝ)) := by
  have hn' : (1 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (show (1 : ℕ) < 2 by decide) hn
  simpa using integral_rpow_div_one_add_pow n 0 (by norm_num) (by simpa using hn')
