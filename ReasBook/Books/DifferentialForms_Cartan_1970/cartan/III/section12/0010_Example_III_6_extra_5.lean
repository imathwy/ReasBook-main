import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Real

-- The source-facing integral is canonically the Beta value `β(1 - α, α)`, and the closed form is
-- the standard reflection identity `Real.Gamma_mul_Gamma_one_sub`.

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
      -- The Möbius substitution has derivative `(1 + x)⁻²` on `(0, ∞)`.
      have hsum : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) + y) 1 x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
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
    -- First rewrite the improper integral on `(0, ∞)` as the standard Beta kernel on `(0, 1)`.
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
      _ = (Complex.betaIntegral s (1 - s)).re := by
            rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
              ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
            · refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
              -- On `(0, 1)`, the complex powers reduce to the corresponding real powers.
              norm_cast
              rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
                Complex.re_mul_ofReal, Complex.ofReal_re]
              all_goals
                nlinarith [hx.1, hx.2]
            · convert! Complex.betaIntegral_convergent (u := s) (v := 1 - s) (by simpa)
                (by simpa using sub_pos.mpr hs1) using 1
              rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
      _ = ProbabilityTheory.beta s (1 - s) := by
            simpa using (ProbabilityTheory.beta_eq_betaIntegralReal s (1 - s) hs0
              (sub_pos.mpr hs1)).symm
  -- Finally specialize `s = 1 - α`, so the target kernel is exactly the Beta kernel.
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
          simp [s]

/-- Cartan section12 0010_Example_III_6_extra_5: for `0 < α < 1`,
`∫_0^∞ dx / (x^α (1 + x)) = π / sin (π α)`. -/
theorem integral_inv_rpow_mul_one_add
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (x ^ α * (1 + x)) ∂volume =
      Real.pi / Real.sin (Real.pi * α) := by
  rw [integral_inv_rpow_mul_one_add_eq_beta α hα0 hα1, ProbabilityTheory.beta,
    show 1 - α + α = 1 by ring, Real.Gamma_one, div_one, mul_comm,
    Real.Gamma_mul_Gamma_one_sub]
