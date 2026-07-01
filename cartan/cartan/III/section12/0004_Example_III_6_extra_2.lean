import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool `lean_leansearch` was unavailable in this environment.
-- Notation was verified locally.

open MeasureTheory
open scoped Real

/-- Helper for Example III.6-extra-2: on `(0, ∞)`, raising `x ^ (1 / 6)` to the sixth
power recovers `x`. -/
private theorem rpow_one_six_nat_six_on_Ioi {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ((x ^ (1 / 6 : ℝ)) ^ (6 : ℕ)) = x := by
  have hx0 : 0 < x := hx
  -- The positive-base `rpow` laws reduce the composition to the exponent product `1`.
  calc
    ((x ^ (1 / 6 : ℝ)) ^ (6 : ℕ)) = (x ^ (1 / 6 : ℝ)) ^ (6 : ℝ) := by
      simpa using (Real.rpow_natCast (x ^ (1 / 6 : ℝ)) 6).symm
    _ = x ^ ((1 / 6 : ℝ) * 6) := by
      rw [← Real.rpow_mul (le_of_lt hx0)]
    _ = x := by
      norm_num

/-- Helper for Example III.6-extra-2: the substitution `y = x^(1/6)` rewrites the original
integral into the Beta-type integral over `Ioi 0`. -/
private theorem integral_inv_one_add_pow_six_eq_one_six_mul_integral_inv_rpow_five_six_mul_one_add :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x ^ 6) ∂volume =
      (1 / 6 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ (5 / 6 : ℝ) * (1 + x)) ∂volume := by
  -- The textbook route starts with the change of variables `y = x ^ (1 / 6)` on `(0, ∞)`.
  calc
    ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x ^ 6) ∂volume
        = ∫ x in Set.Ioi (0 : ℝ),
            (1 / 6 : ℝ) * (1 / (x ^ (5 / 6 : ℝ) * (1 + x))) ∂volume := by
            rw [← integral_comp_rpow_Ioi_of_pos
              (g := fun x : ℝ ↦ 1 / (1 + x ^ 6))
              (by norm_num : 0 < (1 / 6 : ℝ))]
            refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
            have hx0 : 0 < x := hx
            have hx56 : x ^ (5 / 6 : ℝ) ≠ 0 := by
              positivity
            have hx1 : 1 + x ≠ 0 := by
              linarith
            -- Route correction: normalize the Jacobian factor and the composed kernel separately.
            rw [smul_eq_mul, rpow_one_six_nat_six_on_Ioi hx]
            have hneg : ((1 / 6 : ℝ) - 1) = -(5 / 6 : ℝ) := by
              norm_num
            rw [hneg, Real.rpow_neg_eq_inv_rpow, Real.inv_rpow (le_of_lt hx0)]
            field_simp [div_eq_mul_inv, hx56, hx1]
    _ = (1 / 6 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ (5 / 6 : ℝ) * (1 + x)) ∂volume := by
          rw [integral_const_mul]

/-- Helper for Example III.6-extra-2: the Beta function is the integral of the standard
Beta-density kernel on `(0, 1)`. -/
private theorem integral_Ioo_rpow_sub_one_mul_one_sub_rpow_sub_one_eq_beta
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (u - 1) * (1 - x) ^ (v - 1) ∂volume =
      ProbabilityTheory.beta u v := by
  -- We identify the real set integral with the standard complex Beta integral on `[0, 1]`.
  calc
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (u - 1) * (1 - x) ^ (v - 1) ∂volume
        = (Complex.betaIntegral u v).re := by
            rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
              ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
            · refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
              -- On `Ioc 0 1`, the complex powers are just the real powers viewed in `ℂ`.
              norm_cast
              rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
                Complex.re_mul_ofReal, Complex.ofReal_re]
              all_goals
                nlinarith [hx.1, hx.2]
            · convert! Complex.betaIntegral_convergent (u := u) (v := v) hu hv using 1
              rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
    _ = ProbabilityTheory.beta u v := by
          simpa using (ProbabilityTheory.beta_eq_betaIntegralReal u v hu hv).symm

/-- Helper for Example III.6-extra-2: the Möbius substitution `t ↦ t / (1 - t)` turns the
auxiliary integral on `(0, ∞)` into a Beta integral. -/
private theorem integral_inv_rpow_mul_one_add_eq_beta
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ α * (1 + x)) ∂volume =
      ProbabilityTheory.beta (1 - α) α := by
  let s : ℝ := 1 - α
  have hs0 : 0 < s := by
    simpa [s] using sub_pos.mpr hα1
  have hs1 : s < 1 := by
    linarith
  have hbeta :
      ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) / (1 + x) ∂volume =
        ProbabilityTheory.beta s (1 - s) := by
    let f : ℝ → ℝ := fun x ↦ x / (1 + x)
    have hf_deriv :
        ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (1 / (1 + x) ^ 2) (Set.Ioi 0) x := by
      intro x hx
      have hx0 : 0 < x := hx
      have hx1 : 0 < 1 + x := by
        linarith
      have hsum : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) + y) 1 x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
      -- The Möbius map has derivative `1 / (1 + x)^2` on `(0, ∞)`.
      simpa [f, pow_two] using ((hasDerivAt_id x).div hsum hx1.ne').hasDerivWithinAt
    have hf_inj : Set.InjOn f (Set.Ioi (0 : ℝ)) := by
      intro x hx y hy hxy
      have hx0 : 0 < x := hx
      have hy0 : 0 < y := hy
      have hx1 : 1 + x ≠ 0 := by
        nlinarith
      have hy1 : 1 + y ≠ 0 := by
        nlinarith
      dsimp [f] at hxy
      field_simp [f, hx1, hy1] at hxy
      linarith
    have hf_image : f '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx0 : 0 < x := hx
        have hx1 : 0 < 1 + x := by
          nlinarith
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
    -- The same Möbius substitution from the nearby Beta proof reduces the kernel to `(0, 1)`.
    calc
      ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) / (1 + x) ∂volume
          = ∫ y in Set.Ioo (0 : ℝ) 1, y ^ (s - 1) * (1 - y) ^ ((1 - s) - 1) ∂volume := by
              rw [← hf_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
                hf_deriv hf_inj]
              refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
              have hx0 : 0 < x := hx
              have hx1 : 0 < 1 + x := by
                nlinarith
              have hsub : 1 - x / (1 + x) = (1 + x)⁻¹ := by
                field_simp [hx1.ne']
                ring
              have hs : ((1 - s) - 1 : ℝ) = -s := by
                ring
              have hpow : (1 + x) ^ s / (1 + x) ^ (s - 1) = 1 + x := by
                rw [← Real.rpow_sub hx1, sub_sub_cancel, Real.rpow_one]
              symm
              rw [smul_eq_mul, abs_of_pos (by positivity), Real.div_rpow hx0.le hx1.le, hsub,
                hs, Real.rpow_neg_eq_inv_rpow, inv_inv]
              calc
                (1 / (1 + x) ^ 2) * (x ^ (s - 1) / (1 + x) ^ (s - 1) * (1 + x) ^ s)
                    = (1 / (1 + x) ^ 2) *
                        (x ^ (s - 1) * ((1 + x) ^ s / (1 + x) ^ (s - 1))) := by
                            ring
                _ = (1 / (1 + x) ^ 2) * (x ^ (s - 1) * (1 + x)) := by
                      rw [hpow]
                _ = x ^ (s - 1) / (1 + x) := by
                      field_simp [hx1.ne']
      _ = ProbabilityTheory.beta s (1 - s) := by
            exact integral_Ioo_rpow_sub_one_mul_one_sub_rpow_sub_one_eq_beta hs0
              (sub_pos.mpr hs1)
  -- The target kernel is the same Beta kernel with exponent `s - 1 = -α`.
  calc
    ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ α * (1 + x)) ∂volume
        = ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) / (1 + x) ∂volume := by
            refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
            have hx0 : 0 < x := hx
            have hxα : x ^ α ≠ 0 := by
              positivity
            have hx1 : 1 + x ≠ 0 := by
              linarith
            have hs : (s - 1 : ℝ) = -α := by
              simp [s]
            rw [hs, Real.rpow_neg_eq_inv_rpow, Real.inv_rpow (le_of_lt hx0)]
            field_simp [div_eq_mul_inv, hxα, hx1]
    _ = ProbabilityTheory.beta s (1 - s) := hbeta
    _ = ProbabilityTheory.beta (1 - α) α := by
          simpa [s]

/-- Helper for Example III.6-extra-2: the Beta value at `(1/6, 5/6)` simplifies to `2π`. -/
private theorem beta_one_six_five_six_eq_two_pi :
    ProbabilityTheory.beta (1 / 6 : ℝ) (5 / 6 : ℝ) = 2 * Real.pi := by
  -- Evaluate Beta via Euler's reflection formula for Gamma.
  rw [ProbabilityTheory.beta,
    show (1 / 6 : ℝ) + (5 / 6 : ℝ) = 1 by norm_num,
    Real.Gamma_one, div_one]
  have hgamma :
      Real.Gamma (5 / 6 : ℝ) * Real.Gamma (1 / 6 : ℝ) =
        Real.pi / Real.sin (Real.pi * (5 / 6 : ℝ)) := by
    convert Real.Gamma_mul_Gamma_one_sub (5 / 6 : ℝ) using 1
    norm_num
  rw [mul_comm, hgamma]
  have hsin : Real.sin (Real.pi * (5 / 6 : ℝ)) = 1 / 2 := by
    rw [show Real.pi * (5 / 6 : ℝ) = Real.pi - Real.pi / 6 by ring, Real.sin_pi_sub]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using Real.sin_pi_div_six
  rw [hsin]
  ring

/-- Example III.6-extra-2: the residue computation for `1 / (1 + z^6)` yields
`∫_0^∞ dx / (1 + x^6) = π / 3`. -/
theorem integral_inv_one_add_pow_six :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x ^ 6) ∂volume = Real.pi / 3 := by
  -- Reduce to the standard Beta integral and then evaluate the special Beta value.
  calc
    ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x ^ 6) ∂volume =
        (1 / 6 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ (5 / 6 : ℝ) * (1 + x)) ∂volume :=
      integral_inv_one_add_pow_six_eq_one_six_mul_integral_inv_rpow_five_six_mul_one_add
    _ = (1 / 6 : ℝ) * ProbabilityTheory.beta (1 / 6 : ℝ) (5 / 6 : ℝ) := by
      rw [integral_inv_rpow_mul_one_add_eq_beta (5 / 6 : ℝ) (by norm_num) (by norm_num)]
      congr 1
      norm_num
    _ = (1 / 6 : ℝ) * (2 * Real.pi) := by
      rw [beta_one_six_five_six_eq_two_pi]
    _ = Real.pi / 3 := by ring
